include "futhark/generate.mc"
include "futhark/pprint.mc"
include "futhark/record-inline.mc"
include "mexpr/boot-parser.mc"
include "mexpr/cse.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"
include "mexpr/utesttrans.mc"
include "mexpr/rewrite/deadcode.mc"
include "mexpr/rewrite/parallel-keywords.mc"
include "mexpr/rewrite/parallel-rewrite.mc"
include "mexpr/rewrite/rules.mc"
include "mexpr/rewrite/tailrecursion.mc"

lang PMExprCompile =
  BootParser +
  MExprSym + MExprTypeAnnot + MExprUtestTrans + MExprParallelKeywordMaker +
  MExprANF + MExprRewrite + MExprTailRecursion + MExprParallelPattern +
  MExprCSE + MExprParallelDeadcodeElimination +
  FutharkGenerate + FutharkRecordInline
end

lang PMExprPrettyPrint = MExprPrettyPrint + MExprParallelKeywordMaker
  sem isAtomic =
  | TmParallelMap _ -> false
  | TmParallelMap2 _ -> false
  | TmParallelFlatMap _ -> false
  | TmParallelReduce _ -> false
  | TmParallelScan _ -> false
  | TmParallelFilter _ -> false
  | TmParallelPartition _ -> false
  | TmParallelAll _ -> false
  | TmParallelAny _ -> false

  sem pprintCode (indent : Int) (env : PprintEnv) =
  | TmParallelMap t ->
    match printParen indent env t.f with (env, f) then
      match pprintCode indent env t.as with (env, as) then
        (env, join ["parallelMap (", f, ") (", as, ")"])
      else never
    else never
  | TmParallelMap2 t ->
    match printParen indent env t.f with (env, f) then
      match pprintCode indent env t.as with (env, as) then
        match pprintCode indent env t.bs with (env, bs) then
          (env, join ["parallelMap2 (", f, ") (", as, ") (", bs, ")"])
        else never
      else never
    else never
  | TmParallelFlatMap t ->
    match printParen indent env t.f with (env, f) then
      match pprintCode indent env t.as with (env, as) then
        (env, join ["parallelFlatMap (", f, ") (", as, ")"])
      else never
    else never
  | TmParallelReduce t ->
    match printParen indent env t.f with (env, f) then
      match pprintCode indent env t.ne with (env, ne) then
        match pprintCode indent env t.as with (env, as) then
          (env, join ["parallelReduce (", f, ") (", ne, ") (", as, ")"])
        else never
      else never
    else never
  | TmParallelScan t -> never
  | TmParallelFilter t -> never
  | TmParallelPartition t -> never
  | TmParallelAll t -> never
  | TmParallelAny t -> never
end

let parallelKeywords = [
  "parallelMap",
  "parallelMap2",
  "parallelReduce",
  "parallelScan",
  "parallelFilter",
  "parallelPartition",
  "parallelAll",
  "parallelAny"
]

let keywordsSymEnv =
  {symEnvEmpty with varEnv =
    mapFromSeq
      cmpString
      (map (lam s. (s, nameSym s)) parallelKeywords)}

let parallelPatterns = [
  getMapPattern (),
  getMap2Pattern (),
  getReducePattern ()
]

let printPMExprAst : Expr -> Unit = lam ast.
  use PMExprPrettyPrint in
  printLn (expr2str ast)

let printFutharkAst : FutProg -> Unit = lam ast.
  use FutharkPrettyPrint in
  printLn (expr2str ast)

let patternTransformation : Expr -> Expr = lam ast.
  use PMExprCompile in
  let ast = rewriteTerm ast in
  let ast = tailRecursive ast in
  let ast = cseGlobal ast in
  let ast = normalizeTerm ast in
  parallelPatternRewrite parallelPatterns ast

let futharkTranslation : Expr -> FutProg = lam ast.
  use PMExprCompile in
  let ast = deadcodeEliminationToplevel ast in
  let futharkAst : FutProg = generateProgram ast in
  inlineRecords futharkAst

let compile : String -> Unit = lam file.
  use PMExprCompile in
  let ast = parseMCoreFile parallelKeywords file in
  let ast = symbolizeExpr keywordsSymEnv ast in
  let ast = typeAnnot ast in
  let ast = makeKeywords [] ast in
  let ast = utestStrip ast in
  let ast = patternTransformation ast in
  let futharkAst = futharkTranslation ast in
  printFutharkAst futharkAst

mexpr

if geqi (length argv) 2 then
  let file = get argv 1 in
  compile file
else
  printLn (join ["Usage: '", get argv 0, " <file>'"]);
  exit 1
