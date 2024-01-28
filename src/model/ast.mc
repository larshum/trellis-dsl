include "name.mc"
include "map.mc"
include "mexpr/info.mc"

lang TrellisModelTypeAst
  type IntBound = Option (Int, Int)

  syn TType =
  | TBool {info : Info}
  | TInt {bounds : IntBound, info : Info}
  | TProb {info : Info}
  | TTuple {tys : [TType], info : Info}
  | TTable {args : [TType], ret : TType, info : Info}

  sem infoTTy : TType -> Info
  sem infoTTy =
  | TBool t -> t.info
  | TInt t -> t.info
  | TProb t -> t.info
  | TTuple t -> t.info
  | TTable t -> t.info

  sem smapTTypeTType : (TType -> TType) -> TType -> TType
  sem smapTTypeTType f =
  | TBool t -> TBool t
  | TInt t -> TInt t
  | TProb t -> TProb t
  | TTuple t -> TTuple {t with tys = map f t.tys}
  | TTable t -> TTable {t with args = map f t.args, ret = f t.ret}

  sem eqTType : TType -> TType -> Option TType
  sem eqTType l =
  | r -> optionIsSome (checkTType l r)

  sem checkTType : TType -> TType -> Option TType
  sem checkTType l =
  | r -> checkTTypeH (l, r)

  -- NOTE(larshum, 2024-01-25): Check that a pair of types are equivalent.
  -- Bounded integer types are all subtypes of the unbounded integer type, so
  -- we allow using bounded integers whenever an integer type is expected.
  -- However, two integer ranges with different bounds are not equal.
  sem checkTTypeH : (TType, TType) -> Option TType
  sem checkTTypeH =
  | (TBool l, TBool r) -> Some (TBool {info = mergeInfo l.info r.info})
  | (TInt l, TInt r) ->
    match
      switch (l.bounds, r.bounds)
      case (Some l, Some r) then
        if and (eqi l.0 r.0) (eqi l.1 r.1) then Some (Some l)
        else None ()
      case (Some x, None _) | (None _, Some x) then Some (Some x)
      case (None _, None _) then Some (None ())
      end
    with Some validBounds then
      let i = mergeInfo l.info r.info in
      Some (TInt {bounds = validBounds, info = i})
    else None ()
  | (TProb l, TProb r) -> Some (TProb {info = mergeInfo l.info r.info})
  | (TTuple l, TTuple r) ->
    match optionMapM checkTTypeH (zip l.tys r.tys) with Some tys then
      let infos = map infoTTy tys in
      Some (TTuple {tys = tys, info = foldl1 mergeInfo infos})
    else None ()
  | (TTable l, TTable r) ->
    match optionMapM checkTTypeH (zip l.args r.args) with Some args then
      let i1 = foldl1 mergeInfo (map infoTTy args) in
      match checkTType l.ret r.ret with Some ret then
        Some (TTable {args = args, ret = ret, info = mergeInfo i1 (infoTTy ret)})
      else None ()
    else None ()
end

lang TrellisModelExprAst = TrellisModelTypeAst
  syn TExpr =
  | EBool {b : Bool, ty : TType, info : Info}
  | EVar {id : Name, ty : TType, info : Info}
  | EInt {i : Int, ty : TType, info : Info}
  | EProb {p : Float, ty : TType, info : Info}
  | ESlice {target : TExpr, lo : Int, hi : Int, ty : TType, info : Info}
  | ETableAccess {table : Name, args : [TExpr], ty : TType, info : Info}
  | EIf {cond : TExpr, thn : TExpr, els : TExpr, ty : TType, info : Info}
  | EBinOp {op : BOp, lhs : TExpr, rhs : TExpr, ty : TType, info : Info}

  syn BOp =
  | OAdd ()
  | OSub ()
  | OMul ()
  | ODiv ()
  | OEq ()
  | ONeq ()
  | OLt ()
  | OGt ()
  | OLeq ()
  | OGeq ()
  | OAnd ()
  | OOr ()

  sem infoTExpr : TExpr -> Info
  sem infoTExpr =
  | EBool t -> t.info
  | EVar t -> t.info
  | EInt t -> t.info
  | EProb t -> t.info
  | ESlice t -> t.info
  | ETableAccess t -> t.info
  | EIf t -> t.info
  | EBinOp t -> t.info

  sem tyTExpr : TExpr -> TType
  sem tyTExpr =
  | EBool t -> t.ty
  | EVar t -> t.ty
  | EInt t -> t.ty
  | EProb t -> t.ty
  | ESlice t -> t.ty
  | ETableAccess t -> t.ty
  | EIf t -> t.ty
  | EBinOp t -> t.ty

  sem withTyTExpr : TType -> TExpr -> TExpr
  sem withTyTExpr ty =
  | EBool t -> EBool {t with ty = ty}
  | EVar t -> EVar {t with ty = ty}
  | EInt t -> EInt {t with ty = ty}
  | EProb t -> EProb {t with ty = ty}
  | ESlice t -> ESlice {t with ty = ty}
  | ETableAccess t -> ETableAccess {t with ty = ty}
  | EIf t -> EIf {t with ty = ty}
  | EBinOp t -> EBinOp {t with ty = ty}

  sem smapAccumLTExprTExpr : all a. (a -> TExpr -> (a, TExpr)) -> a -> TExpr -> (a, TExpr)
  sem smapAccumLTExprTExpr f acc =
  | EBool t -> (acc, EBool t)
  | EVar t -> (acc, EVar t)
  | EInt t -> (acc, EInt t)
  | EProb t -> (acc, EProb t)
  | ESlice t ->
    match f acc t.target with (acc, target) in
    (acc, ESlice {t with target = target})
  | ETableAccess t ->
    match mapAccumL f acc t.args with (acc, args) in
    (acc, ETableAccess {t with args = args})
  | EIf t ->
    match f acc t.cond with (acc, cond) in
    match f acc t.thn with (acc, thn) in
    match f acc t.els with (acc, els) in
    (acc, EIf {t with cond = cond, thn = thn, els = els})
  | EBinOp t ->
    match f acc t.lhs with (acc, lhs) in
    match f acc t.rhs with (acc, rhs) in
    (acc, EBinOp {t with lhs = lhs, rhs = rhs})

  sem smapTExprTExpr : (TExpr -> TExpr) -> TExpr -> TExpr
  sem smapTExprTExpr f =
  | e ->
    match smapAccumLTExprTExpr (lam. lam e. ((), f e)) () e with (_, e) in
    e

  sem sfoldTExprTExpr : all a. (a -> TExpr -> a) -> a -> TExpr -> a
  sem sfoldTExprTExpr f acc =
  | e ->
    match smapAccumLTExprTExpr (lam acc. lam e. (f acc e, e)) acc e
    with (acc, _) in
    acc
end

lang TrellisModelSetAst = TrellisModelTypeAst + TrellisModelExprAst
  syn TSet =
  | SAll {info : Info}
  | SValueBuilder {x : Name, conds : [TExpr], info : Info}
  | SValueLiteral {exprs : [TExpr], info : Info}
  | STransitionBuilder {x : Name, y : Name, conds : [TExpr], info : Info}
  | STransitionLiteral {exprs : [(TExpr, TExpr)], info : Info}

  sem infoTSet : TSet -> Info
  sem infoTSet =
  | SAll t -> t.info
  | SValueBuilder t -> t.info
  | SValueLiteral t -> t.info
  | STransitionBuilder t -> t.info
  | STransitionLiteral t -> t.info

  sem smapTSetTExpr : (TExpr -> TExpr) -> TSet -> TSet
  sem smapTSetTExpr f =
  | SAll t -> SAll t
  | SValueBuilder t -> SValueBuilder {t with conds = map f t.conds}
  | SValueLiteral t -> SValueLiteral {t with exprs = map f t.exprs}
  | STransitionBuilder t -> STransitionBuilder {t with conds = map f t.conds}
  | STransitionLiteral t ->
    STransitionLiteral {t with exprs = map (lam e. (f e.0, f e.1)) t.exprs}
end

lang TrellisModelAst =
  TrellisModelTypeAst + TrellisModelExprAst + TrellisModelSetAst

  type Case = {
    cond : TSet,
    body : TExpr
  }

  type InitialProbDef = {x : Name, cases : [Case], info : Info}
  type OutputProbDef = {x : Name, o : Name, cases : [Case], info : Info}
  type TransitionProbDef = {x : Name, y : Name, cases : [Case], info : Info}

  type TModel = {
    stateType : TType,
    outType : TType,
    tables : Map Name TType,
    initial : InitialProbDef,
    output : OutputProbDef,
    transition : TransitionProbDef
  }
end