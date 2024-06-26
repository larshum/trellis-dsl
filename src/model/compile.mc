include "math.mc"
include "seq.mc"
include "futhark/ast.mc"
include "futhark/pprint.mc"
include "mexpr/info.mc"

include "ast.mc"
include "encode.mc"
include "../trellis-arg.mc"
include "../trellis-common.mc"

let initialProbabilityId = nameSym "initial_probability"
let outputProbabilityId = nameSym "output_probability"
let transitionProbabilityId = nameSym "transition_probability"
let constructModelEntryId = nameSym "init_model"
let tablesId = nameSym "tables"
let modelId = nameSym "model"

let stateTyId = nameSym "state_t"
let probTyId = nameSym "prob_t"
let obsTyId = nameSym "obs_t"
let modelTyId = nameSym "model_t"
let tablesTyId = nameSym "tables_t"
let stateModuleId = nameSym "state"
let probModuleId = nameSym "prob"
let obsModuleId = nameSym "obs"
let nstatesId = nameSym "nstates"
let nobsId = nameSym "nobs"
let npredsId = nameSym "npreds"

lang TrellisCompileBase = TrellisModelAst + FutharkAst + TrellisTypeBitwidth
  -- The environment used throughout compilation of the Trellis model AST.
  type TrellisCompileEnv = {
    -- The command-line options provided by the user
    options : TrellisOptions,

    -- The tables defined in the model
    tables : Map Name FutType,

    -- The declared types of the state and the output
    stateType : TType,
    outputType : TType,

    -- Determines whether we pre-compute the tables when constructing the
    -- model, or if we directly use the functions to compute the initial,
    -- output, and transition probabilities. This is a trade-off between
    -- execution time and memory usage -- for models with few states, it is
    -- very likely to be worth precomputing the tables due to the performance
    -- gains.
    precomputeTables : Bool,

    -- The maximum number of predecessors of any state
    maxpreds : Int
  }

  sem initCompileEnv : TrellisOptions -> TModel -> TrellisCompileEnv
  sem initCompileEnv options =
  | model ->
    let maxpreds =
      if and options.skipPredecessors (eqi options.maxpreds (negi 1)) then
        error "When skipping predecessors, the --maxpreds argument must be used"
      else options.maxpreds
    in
    { options = options, tables = mapEmpty nameCmp
    , stateType = model.stateType, outputType = model.outType
    , precomputeTables = options.forcePrecomputeTables
    , maxpreds = maxpreds }

  sem probModuleProjection : Info -> String -> FutExpr
  sem probModuleProjection info =
  | id ->
    let probModule =
      FEVar {ident = probModuleId, ty = FTyUnknown {info = info}, info = info}
    in
    FEProj { target = probModule, label = stringToSid id
           , ty = FTyUnknown {info = info}, info = info }

  sem logAppExpr : FutExpr -> FutExpr
  sem logAppExpr =
  | rhs ->
    let info = infoFutTm rhs in
    let logExpr = probModuleProjection info "log" in
    FEApp {lhs = logExpr, rhs = rhs, ty = tyFutTm rhs, info = info}

  sem expAppExpr : FutExpr -> FutExpr
  sem expAppExpr =
  | rhs ->
    let info = infoFutTm rhs in
    let expExpr = probModuleProjection info "exp" in
    FEApp {lhs = expExpr, rhs = rhs, ty = tyFutTm rhs, info = info}

  sem negInfExpr : Info -> FutExpr
  sem negInfExpr =
  | info ->
    FEApp {
      lhs = probModuleProjection info "neg",
      rhs = probModuleProjection info "inf",
      ty = FTyUnknown {info = info}, info = info}

  sem chooseIntegerSize : Int -> FutIntSize
  sem chooseIntegerSize =
  | bits ->
    if leqi bits 8 then U8 ()
    else if leqi bits 16 then U16 ()
    else if leqi bits 32 then U32 ()
    else if leqi bits 64 then U64 ()
    else
      let msg = join [
        "Trellis does not support states or observations requiring ",
        "more than 64 bits to encode"
      ] in
      error msg

  sem chooseIntegerType : Int -> FutType
  sem chooseIntegerType =
  | bits -> FTyInt {sz = chooseIntegerSize bits, info = NoInfo ()}

  sem stateIntegerSize : TType -> FutIntSize
  sem stateIntegerSize =
  | ty -> chooseIntegerSize (bitwidthType ty)

  sem stateFutharkType : TrellisCompileEnv -> FutType
  sem stateFutharkType =
  | env -> FTyInt {sz = stateIntegerSize env.stateType, info = NoInfo ()}

  sem outputIntegerSize : TType -> FutIntSize
  sem outputIntegerSize =
  | ty ->
    -- NOTE(larshum, 2024-02-14): We reserve one bit for representing an
    -- "empty" observation. We use this when padding the sequence in the
    -- Viterbi algorithm.
    chooseIntegerSize (addi (bitwidthType ty) 1)

  sem outputFutharkType : TrellisCompileEnv -> FutType
  sem outputFutharkType =
  | env -> FTyInt {sz = outputIntegerSize env.outputType, info = NoInfo ()}
end

lang TrellisCompileType =
  TrellisCompileBase + TrellisTypeCardinality + TrellisTypeBitwidth

  sem compileTrellisType : TrellisCompileEnv -> TType -> FutType
  sem compileTrellisType env =
  | TBool {info = info} -> FTyBool {info = info}
  | ty & (TInt {bounds = Some _, info = info}) ->
    let bitwidth = bitwidthType ty in
    withInfoFutTy info (chooseIntegerType bitwidth)
  | TInt {bounds = None (), info = info} -> FTyInt {sz = I64 (), info = info}
  | TProb {info = info} -> FTyIdent {ident = probTyId, info = info}
  | TTuple {tys = tys, info = info} ->
    errorSingle [info] "Standalone tuple types are not supported"
  | TTable {args = args, ret = ret, info = info} ->
    let buildSizedArrayType = lam dim. lam ty.
      FTyArray {elem = ty, dim = Some (AbsDim dim), info = info}
    in
    let dims = map cardinalityType args in
    let elemTy = compileTrellisType env ret in
    foldr buildSizedArrayType elemTy dims
end

lang TrellisCompileExpr =
  TrellisCompileBase + TrellisCompileType + TrellisEncode + FutharkPrettyPrint

  sem compileTrellisExpr : TrellisCompileEnv -> TExpr -> FutExpr
  sem compileTrellisExpr env =
  | EBool {b = b, ty = ty, info = info} ->
    let ty = compileTrellisType env ty in
    FEConst {val = FCBool {val = b}, ty = ty, info = info}
  | EVar {id = id, ty = ty, info = info} ->
    FEVar {ident = id, ty = compileTrellisType env ty, info = info}
  | EInt {i = i, ty = ty, info = info} ->
    let ty = compileTrellisType env ty in
    FEConst {val = FCInt {val = i, sz = None ()}, ty = ty, info = info}
  | EProb {p = p, ty = ty, info = info} ->
    match ty with TProb _ then
      -- NOTE(larshum, 2024-01-24): Here, we convert probability literals to
      -- logscale.
      let ty = compileTrellisType env ty in
      let floatSz =
        Some (if env.options.useDoublePrecisionFloats then F64 () else F32 ())
      in
      FEConst {val = FCFloat {val = log p, sz = floatSz}, ty = ty, info = info}
    else errorSingle [info] "Probability literal was assigned an invalid type"
  | ESlice {target = target, lo = lo, hi = hi, ty = ty, info = info} ->
    errorSingle [info] "Internal error: Found slice when compiling intermediate AST"
  | ETableAccess {table = table, args = args, ty = ty, info = info} ->
    let compileTableArg = lam acc. lam targ.
      let index = compileTrellisExpr env targ in
      FEArrayAccess {
        array = acc, index = index,
        ty = FTyUnknown {info = info}, info = info}
    in
    let tableExpr = FEProj {
      target = FEVar {
        ident = tablesId, ty = FTyUnknown {info = info}, info = info
      },
      label = stringToSid (nameGetStr table), ty = FTyUnknown {info = info},
      info = info
    } in
    let resultTy = compileTrellisType env ty in
    withTypeFutTm resultTy (foldl compileTableArg tableExpr args)
  | EIf {cond = cond, thn = thn, els = els, ty = ty, info = info} ->
    let cond = compileTrellisExpr env cond in
    let thn = compileTrellisExpr env thn in
    let els = compileTrellisExpr env els in
    let ty = compileTrellisType env ty in
    FEIf {cond = cond, thn = thn, els = els, ty = ty, info = info}
  | EBinOp (t & {op = OAdd _ | OSub _ | OMul _ | ODiv _}) ->
    compileArithmeticOperation env t
  | EBinOp t ->
    let lhs = compileTrellisExpr env t.lhs in
    let rhs = compileTrellisExpr env t.rhs in
    let op = compileTrellisBinOp t.info t.op in
    let opExpr = FEConst {val = op, ty = FTyUnknown {info = t.info}, info = t.info} in
    constructBinOp t.info opExpr lhs rhs

  type BinOpStruct = {op : BOp, lhs : TExpr, rhs : TExpr, ty : TType, info : Info}

  sem constructBinOp : Info -> FutExpr -> FutExpr -> FutExpr -> FutExpr
  sem constructBinOp info op lhs =
  | rhs ->
    let resultTy = tyFutTm lhs in
    let tyuk = FTyUnknown {info = info} in
    FEApp { lhs = FEApp {lhs = op, rhs = lhs, ty = tyuk, info = info}
          , rhs = rhs, ty = resultTy, info = info }

  sem compileTrellisBinOp : Info -> BOp -> FutConst
  sem compileTrellisBinOp info =
  | OAdd _ | OSub _ | OMul _ | ODiv _ ->
    errorSingle [info]
      "Internal error: Arithmetic operations compile differently based on type"
  | OEq _ -> FCEq ()
  | ONeq _ -> FCNeq ()
  | OLt _ -> FCLt ()
  | OGt _ -> FCGt ()
  | OLeq _ -> FCLeq ()
  | OGeq _ -> FCGeq ()
  | OAnd _ -> FCAnd ()
  | OOr _ -> FCOr ()
  | OMod _ -> FCRem ()

  sem compileArithmeticOperation : TrellisCompileEnv -> BinOpStruct -> FutExpr
  sem compileArithmeticOperation env =
  | t ->
    let lhs = compileTrellisExpr env t.lhs in
    let rhs = compileTrellisExpr env t.rhs in
    let ty = compileTrellisType env t.ty in
    match t.ty with TInt _ then
      let c =
        switch t.op
        case OAdd _ then FCAdd ()
        case OSub _ then FCSub ()
        case OMul _ then FCMul ()
        case ODiv _ then FCDiv ()
        end
      in
      let op = FEConst {val = c, ty = ty, info = t.info} in
      constructBinOp t.info op lhs rhs
    else
      -- NOTE(larshum, 2024-01-24): All probability values are represented in
      -- logarithmic scale, so we need to use operations accordingly.
      switch t.op
      case OAdd _ | OSub _ then
        let c = match t.op with OAdd _ then FCAdd () else FCSub () in
        let op = FEConst {val = c, ty = FTyUnknown {info = t.info}, info = t.info} in
        logAppExpr (constructBinOp t.info op (expAppExpr lhs) (expAppExpr rhs))
      case OMul _ | ODiv _ then
        let c = match t.op with OMul _ then FCAdd () else FCSub () in
        let op = FEConst {val = c, ty = ty, info = t.info} in
        constructBinOp t.info op lhs rhs
      end
end

-- Compiles set expressions to a boolean expression determining whether a given
-- state (or pairs of states) are in the set.
lang TrellisCompileSet = TrellisCompileExpr + TrellisCompileType
  sem binaryOp : FutConst -> FutExpr -> FutExpr -> FutExpr
  sem binaryOp c lhs =
  | rhs ->
    let info = mergeInfo (infoFutTm lhs) (infoFutTm rhs) in
    FEApp {
      lhs = FEApp {
        lhs = FEConst {val = c, ty = FTyUnknown {info = info}, info = info},
        rhs = lhs, ty = FTyUnknown {info = info}, info = info},
      rhs = rhs, ty = FTyUnknown {info = info}, info = info}

  sem boolAnd : FutExpr -> FutExpr -> FutExpr
  sem boolAnd lhs =
  | rhs -> binaryOp (FCAnd ()) lhs rhs

  sem compileTrellisSet : TrellisCompileEnv -> TSet -> FutExpr
  sem compileTrellisSet env =
  | SAll {info = info} ->
    FEConst {val = FCBool {val = true}, ty = FTyBool {info = info}, info = info}
  | SValueBuilder {conds = conds, info = info}
  | STransitionBuilder {conds = conds, info = info} ->
    foldl1 boolAnd (map (compileTrellisExpr env) conds)
end

lang TrellisCompileProbabilityFunction =
  TrellisCompileExpr + TrellisCompileSet

  type ProbFunRepr = {
    args : [(Name, FutType)],
    decl : FutDecl
  }
  type ProbFuns = (ProbFunRepr, ProbFunRepr, ProbFunRepr)

  sem generateProbabilityFunctions : TrellisCompileEnv -> TModel -> ProbFuns
  sem generateProbabilityFunctions env =
  | model ->
    let stateTy = nFutIdentTy_ stateTyId in
    let outTy = nFutIdentTy_ obsTyId in
    let init = model.initial in
    let initBaseArgs = [(init.x, stateTy)] in
    match generateProbabilityFunction env init.info initialProbabilityId initBaseArgs init.cases
    with (t1, initFun) in
    let out = model.output in
    let outBaseArgs = [(out.x, stateTy), (out.o, outTy)] in
    match generateProbabilityFunction env out.info outputProbabilityId outBaseArgs out.cases
    with (t2, outFun) in
    let trans = model.transition in
    let transBaseArgs = [(trans.x, stateTy), (trans.y, stateTy)] in
    match generateProbabilityFunction env trans.info transitionProbabilityId transBaseArgs trans.cases
    with (t3, transFun) in

    -- If any of the declared tables are unused, we report an error
    -- TODO(larshum, 2024-01-25): Improve this error by using info fields of
    -- the tables, and make it possible to ignore/get a warning.
    let unusedTables = mapDifference env.tables (mapUnion t1 (mapUnion t2 t3)) in
    if mapIsEmpty unusedTables then (initFun, outFun, transFun)
    else
      let unusedTableIds = map nameGetStr (mapKeys unusedTables) in
      error (join ["Model contains unused tables: ", strJoin " " unusedTableIds])

  sem generateProbabilityFunction : TrellisCompileEnv -> Info -> Name -> [(Name, FutType)]
                                 -> [Case] -> (Map Name FutType, ProbFunRepr)
  sem generateProbabilityFunction env info id args =
  | cases ->
    let compileCase = lam c. lam acc.
      let tables = collectUsedTables env.tables acc.0 c.body in
      let cond = compileTrellisSet env c.cond in
      let thn = compileTrellisExpr env c.body in
      ( tables
      , FEIf {
          cond = cond, thn = thn, els = acc.1,
          ty = FTyUnknown {info = info}, info = info} )
    in
    let defaultBody = negInfExpr info in
    match foldr compileCase (mapEmpty nameCmp, defaultBody) cases
    with (tables, body) in
    let argIds = map (lam a. a.0) args in
    let resymbolizedArgs = map (lam a. (nameSetNewSym a.0, a.1)) args in
    let body = convertArgsToI64 resymbolizedArgs argIds body in
    let args = cons (tablesId, nFutIdentTy_ tablesTyId) resymbolizedArgs in
    let funDecl = FDeclFun {
        ident = id, entry = false, typeParams = [],
        params = args, ret = FTyIdent {ident = probTyId, info = info},
        body = body, info = info
    } in
    ( tables, {args = args, decl = funDecl} )

  sem convertArgsToI64 : [(Name, FutType)] -> [Name] -> FutExpr -> FutExpr
  sem convertArgsToI64 args newIds =
  | body ->
    let i = infoFutTm body in
    let int64 = FTyInt {sz = I64 (), info = i} in
    let f = lam accExpr. lam arg.
      match arg with ((argId, ty), bindId) in
      let argModuleId =
        -- NOTE(larshum, 2024-04-10): Currently, we only support states and
        -- observations as arguments to the three probability functions. We
        -- cast them to an i64 at the start to avoid issues with typing.
        match ty with FTyIdent {ident = id} then
          let str = nameGetStr id in
          match str with "state_t" then
            stateModuleId
          else match str with "obs_t" then
            obsModuleId
          else
            errorSingle [i] "Unsupported type of probability function argument"
        else
          errorSingle [i] "Unsupported type of probability function argument"
      in
      let castExpr = FEApp {
        lhs = FEProj {
          target = FEVar {
            ident = argModuleId, ty = FTyUnknown {info = i}, info = i},
          label = stringToSid "to_i64", ty = FTyUnknown {info = i}, info = i},
        rhs = FEVar {ident = argId, ty = ty, info = i},
        ty = int64, info = i
      } in
      FELet {
        ident = bindId, tyBody = int64, body = castExpr,
        inexpr = accExpr, ty = tyFutTm body, info = i}
    in
    foldl f body (zip args newIds)

  sem collectUsedTables : Map Name FutType -> Map Name FutType -> TExpr
                       -> Map Name FutType
  sem collectUsedTables tables acc =
  | ETableAccess {table = table} ->
    match mapLookup table tables with Some ty then mapInsert table ty acc
    else acc
  | e -> sfoldTExprTExpr (collectUsedTables tables) acc e
end

lang TrellisCompileInitializer =
  TrellisCompileBase + TrellisTypeBitwidth + TrellisTypeCardinality +
  TrellisCompileProbabilityFunction + FutharkPrettyPrint

  sem constructTablesType : TrellisCompileEnv -> FutDecl
  sem constructTablesType =
  | env ->
    let tables = map (lam t. (nameGetStr t.0, t.1)) (mapBindings env.tables) in
    FDeclType {
      ident = tablesTyId, typeParams = [],
      ty = futRecordTy_ tables, info = NoInfo ()
    }

  sem constructModelType : TrellisCompileEnv -> FutDecl
  sem constructModelType =
  | env ->
    let modelTy =
      if env.precomputeTables then
        let probTy = nFutIdentTy_ probTyId in
        futRecordTy_ ([
          ("init", futSizedArrayTy_ probTy nstatesId),
          ("out", futSizedArrayTy_ (futSizedArrayTy_ probTy nobsId) nstatesId),
          ("trans", futSizedArrayTy_ (futSizedArrayTy_ probTy nstatesId) nstatesId)
        ])
      else
        FTyIdent {ident = tablesTyId, info = NoInfo ()}
    in
    FDeclType {ident = modelTyId, typeParams = [], ty = modelTy, info = NoInfo ()}

  sem constructModelEntry : TrellisCompileEnv -> FutDecl
  sem constructModelEntry =
  | env ->
    let localTablesId = nameSym "tables" in
    let addTabulate = lam d. lam acc.
      futTabulate_ (nFutVar_ d.0) (futLam_ d.2 acc)
    in
    let probBody = lam funId. lam dims.
      let probArgs =
        map
          (lam d. futApp_ (futProj_ (nFutVar_ d.1) "i64") (futVar_ d.2))
          dims
      in
      let probApp =
        futAppSeq_ (nFutVar_ funId) (cons (nFutVar_ localTablesId) probArgs)
      in
      foldr addTabulate probApp dims
    in
    let params = mapBindings env.tables in
    let tableBody =
      futRecord_ (map (lam p. (nameGetStr p.0, nFutVar_ p.0)) params)
    in
    let modelBody =
      if env.precomputeTables then
        futBind_
          (nuFutLet_ localTablesId tableBody)
          (futRecord_ [
            ("init",
              probBody initialProbabilityId [(nstatesId, stateModuleId, "x")]),
            ("out",
              probBody outputProbabilityId [
                (nstatesId, stateModuleId, "x"), (nobsId, obsModuleId, "o")]),
            ("trans",
              probBody transitionProbabilityId [
                (nstatesId, stateModuleId, "x"), (nstatesId, stateModuleId, "y")])
          ])
      else
        tableBody
    in
    FDeclFun {
      ident = constructModelEntryId, entry = true, typeParams = [],
      params = params, ret = nFutIdentTy_ modelTyId, body = modelBody,
      info = NoInfo ()
    }

  sem generateInitializer : TrellisCompileEnv -> TModel -> FutProg
  sem generateInitializer env =
  | model ->
    let pprintType = lam ty.
      match pprintType 0 pprintEnvEmpty ty with (_, str) in
      str
    in
    match generateProbabilityFunctions env model with (initp, outp, transp) in
    let stateTyStr = pprintType (stateFutharkType env) in
    let outTyStr = pprintType (outputFutharkType env) in
    let probTyStr =
      if env.options.useDoublePrecisionFloats then "f64" else "f32"
    in
    FProg {decls = [
      FDeclModuleAlias {ident = stateModuleId, moduleId = stateTyStr, info = NoInfo ()},
      FDeclModuleAlias {ident = obsModuleId, moduleId = outTyStr, info = NoInfo ()},
      FDeclModuleAlias {ident = probModuleId, moduleId = probTyStr, info = NoInfo ()},
      FDeclType {
        ident = stateTyId, typeParams = [],
        ty = futProjTy_ (nFutIdentTy_ stateModuleId) "t", info = NoInfo ()},
      FDeclType {
        ident = obsTyId, typeParams = [],
        ty = futProjTy_ (nFutIdentTy_ obsModuleId) "t", info = NoInfo ()},
      FDeclType {
        ident = probTyId, typeParams = [],
        ty = futProjTy_ (nFutIdentTy_ probModuleId) "t", info = NoInfo ()},
      FDeclConst {
        ident = nstatesId, ty = FTyInt {info = NoInfo (), sz = I64 ()},
        val = futInt_ (cardinalityType env.stateType), info = NoInfo ()},
      FDeclConst {
        ident = nobsId, ty = FTyInt {info = NoInfo (), sz = I64 ()},
        val = futInt_ (cardinalityType env.outputType), info = NoInfo ()},
      FDeclConst {
        ident = npredsId, ty = FTyInt {info = NoInfo (), sz = I64 ()},
        val = futInt_ env.maxpreds, info = NoInfo ()},
      constructTablesType env,
      initp.decl,
      outp.decl,
      transp.decl,
      constructModelType env,
      constructModelEntry env
    ]}
end

lang TrellisCompileModel =
  TrellisCompileInitializer + TrellisCompileProbabilityFunction

  -- The complete output from the compilation of the Trellis model. This
  -- consists of multiple separate pieces that we combine to produce one
  -- Futhark program.
  type TrellisCompileOutput = {
    -- The environment used during compilation
    env : TrellisCompileEnv,

    -- The generated initializer code, which we put at the top of the final
    -- Futhark program.
    initializer : FutProg
  }

  sem compileTrellisModel : TrellisCompileEnv -> TModel -> TrellisCompileOutput
  sem compileTrellisModel env =
  | model ->
    let env =
      {env with tables = mapMapWithKey (lam. compileTrellisType env) model.tables}
    in
    { env = env, initializer = generateInitializer env model }
end

lang TestLang = TrellisCompileModel + FutharkPrettyPrint
end

mexpr

use TestLang in

let pprintType = lam ty.
  match pprintType 0 pprintEnvEmpty ty with (_, s) in s
in
let pprintExpr = lam e.
  match pprintExpr 0 pprintEnvEmpty e with (_, s) in s
in
let compEnv = lam opts. lam tables. lam sty. lam oty.
  { options = opts, tables = tables, stateType = sty, outputType = oty
  , precomputeTables = false, maxpreds = cardinalityType sty }
in
let eqStringIgnoreWhitespace = lam l. lam r.
  eqString
    (filter (lam c. not (isWhitespace c)) l)
    (filter (lam c. not (isWhitespace c)) r)
in
let i = trellisInfo "trellis-compile" in

utest pprintType (chooseIntegerType 1) with "u8" using eqString else ppStrings in
utest pprintType (chooseIntegerType 8) with "u8" using eqString else ppStrings in
utest pprintType (chooseIntegerType 9) with "u16" using eqString else ppStrings in
utest pprintType (chooseIntegerType 31) with "u32" using eqString else ppStrings in
utest pprintType (chooseIntegerType 37) with "u64" using eqString else ppStrings in

-- Types
let boolTy = TBool {info = i} in
let emptyEnv = compEnv trellisDefaultOptions (mapEmpty nameCmp) boolTy boolTy in
utest pprintType (compileTrellisType emptyEnv boolTy) with "bool"
using eqString else ppStrings in

let intTy1 = TInt {bounds = Some (2, 7), info = i} in
let intTy2 = TInt {bounds = Some (5, 278), info = i} in
utest pprintType (compileTrellisType emptyEnv intTy1) with "u8"
using eqString else ppStrings in
utest pprintType (compileTrellisType emptyEnv intTy2) with "u16"
using eqString else ppStrings in

let probTy = TProb {info = i} in
utest pprintType (compileTrellisType emptyEnv probTy) with "prob_t"
using eqString else ppStrings in

let tableTy = TTable {args = [intTy1, intTy2, boolTy], ret = probTy, info = i} in
utest pprintType (compileTrellisType emptyEnv tableTy) with "[6][274][2]prob_t"
using eqString else ppStrings in

-- Expressions
let x = lam ty. EVar {id = nameNoSym "x", ty = ty, info = i} in
utest pprintExpr (compileTrellisExpr emptyEnv (x boolTy))
with "x" using eqString else ppStrings in

let p = EProb {p = 1.0, ty = TProb {info = i}, info = i} in
utest pprintExpr (compileTrellisExpr emptyEnv p)
with "0.0f32" using eqString else ppStrings in

let probAdd = EBinOp {
  op = OMul (), lhs = x probTy, rhs = p, ty = probTy, info = i
} in
utest pprintExpr (compileTrellisExpr emptyEnv probAdd)
with "(+) x 0.0f32"
using eqStringIgnoreWhitespace else ppStrings in

let intLit = EInt {i = 3, ty = TInt {bounds = None (), info = i}, info = i} in
utest pprintExpr (compileTrellisExpr emptyEnv intLit) with "3"
using eqString else ppStrings in

let intAdd = EBinOp {
  op = OAdd (), lhs = x intTy1, rhs = intLit, ty = intTy1, info = i
} in
utest pprintExpr (compileTrellisExpr emptyEnv intAdd) with "(+) x 3"
using eqStringIgnoreWhitespace else ppStrings in

let intEq = EBinOp {
  op = OEq (), lhs = x intTy1, rhs = intLit, ty = boolTy, info = i
} in
utest pprintExpr (compileTrellisExpr emptyEnv intEq) with "(==) x 3"
using eqStringIgnoreWhitespace else ppStrings in

-- Sets
let allSet = SAll {info = i} in
utest pprintExpr (compileTrellisSet emptyEnv allSet) with "true"
using eqString else ppStrings in

let xId = nameNoSym "x" in
let valueSet1 = SValueBuilder {x = xId, conds = [intEq], info = i} in
let valueSet2 = SValueBuilder {x = xId, conds = [intEq, intEq], info = i} in
utest pprintExpr (compileTrellisSet emptyEnv valueSet1) with "(==) x 3"
using eqStringIgnoreWhitespace else ppStrings in
utest pprintExpr (compileTrellisSet emptyEnv valueSet2) with "(&&) ((==) x 3) ((==) x 3)"
using eqStringIgnoreWhitespace else ppStrings in

()
