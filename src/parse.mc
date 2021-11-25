include "string.mc"
include "stringid.mc"
include "mexpr/boot-parser.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"

type ViterbiParams =
{ signalLevels : Int
, observationProbabilities : [[Float]]
, transitionProbabilities : [[Float]]
, duration : [Float]
, k : Int
, dMax : Int
, tailFactor : Float
, tailFactorComp : Float
}

type Signal = {id : String, values : [Int]}

type Reference = {id : String, genome : [Int]}

let _readKey2Key = lam readKey.
  let prefix = "read_" in
  if isPrefix eqChar prefix readKey then
    subsequence readKey (length prefix) (length readKey)
  else error (concat "Unexpected key: " readKey)

utest _readKey2Key "read_catitude200" with "catitude200"

let _expr2int : Expr -> Int = use MExprAst in lam expr.
  match expr with TmConst {val = CInt {val = i}} then i
  else dprintLn expr; error "Expected integer"

utest _expr2int (int_ 42) with 42

let _expr2char : Expr -> Char = use MExprAst in lam expr.
  match expr with TmConst {val = CChar {val = c}} then c
  else error "Expected character"

utest _expr2char (char_ 'a') with 'a'

let _expr2float : Expr -> Flaot = use MExprAst in lam expr.
  match expr with TmConst {val = CFloat {val = v}} then v
  -- negative numbers
  else match expr with
    TmApp {lhs = TmConst {val = CNegf _}, rhs = TmConst {val = CFloat {val = v}}}
  then negf v
  -- minus infinity
  else match expr with
    TmApp {
      lhs = TmConst {val = CNegf _},
      rhs = TmApp {lhs = TmApp {lhs = TmConst {val = CDivf _},
                          rhs = TmConst {val = CFloat {val = v1}}},
             rhs = TmConst {val = CFloat {val = v2}}}}
  then negf (divf v1 v2)
  else dprintLn expr; error "Expected float"

utest _expr2float (float_ 0.20001) with 0.20001 using eqfApprox 1e-6

let _expr2seq : (Expr -> a) -> Expr -> [a] = use MExprAst in lam f. lam expr.
  match expr with TmSeq {tms = tms} then
    map f tms
  else error "Expected sequence"

let _expr2floatSeq : Expr -> [Float] = _expr2seq _expr2float

utest _expr2floatSeq (seq_ [float_ 0.1, float_ 0.43, float_ 78.97123])
with [0.1, 0.43, 78.97123]
using eqSeq (eqfApprox 1e-6)

let _expr2floatSeqOfSeq : Expr -> [[Float]] = _expr2seq (_expr2seq _expr2float)

utest _expr2floatSeqOfSeq (seq_ [seq_ [float_ 0.0, float_ 1.01],
                            seq_ [float_ 0.6, float_ 10.1]])
with [[0.0, 1.01], [0.6, 10.1]]
using
  (lam s1. lam s2. eqSeq (lam e1. lam e2. eqSeq (eqfApprox 1e-6) e1 e2) s1 s2)

let _expr2strSeq : Expr -> [String] = _expr2seq (_expr2seq _expr2char)
utest _expr2strSeq (seq_ [str_ "Hello", str_ "World"]) with ["Hello", "World"]

let _expr2intSeqOfSeq : Expr -> [[Int]] = _expr2seq (_expr2seq _expr2int)
utest _expr2intSeqOfSeq (seq_ [seq_ [int_ 1, int_ 2], seq_ [int_ 3]]) with [[1,2],[3]]

let _mapSidToString : Map SID a -> Map String a = lam m.
  mapFromSeq cmpString (
    map (lam t : (SID, a). (sidToString t.0, t.1)) (mapBindings m))

let parseModel : String -> ViterbiParams = lam filename.
  use BootParser in
  let str = readFile filename in
  let parsed = parseMExprString [] str in

  match parsed with TmRecord {bindings = bindings} then
    let bindings = _mapSidToString bindings in

    let signalLevels = _expr2int (mapFindExn "signalLevels" bindings) in
    let observationProbs = _expr2floatSeqOfSeq (mapFindExn "observationProbabilities" bindings) in
    let transitionProbs = _expr2floatSeqOfSeq (mapFindExn "transitionProbabilities" bindings) in
    let duration = _expr2floatSeq (mapFindExn "duration" bindings) in
    let k = _expr2int (mapFindExn "k" bindings) in
    let dMax = _expr2int (mapFindExn "dMax" bindings) in
    let tailFactor = _expr2float (mapFindExn "tailFactor" bindings) in
    let tailFactorComp = _expr2float (mapFindExn "tailFactorComp" bindings) in

    { signalLevels = signalLevels
    , observationProbabilities = observationProbs
    , transitionProbabilities = transitionProbs
    , duration = duration
    , k = k
    , dMax = dMax
    , tailFactor = tailFactor
    , tailFactorComp = tailFactorComp
    }

  else error "Expected record"

let parseSignals : String -> [Signal] = lam filename.
  use BootParser in
  let str = readFile filename in
  let parsed = parseMExprString [] str in

  match parsed with TmRecord {bindings = bindings} then
    let bindings = _mapSidToString bindings in

    let readKeys = _expr2strSeq (mapFindExn "keys" bindings) in
    let keys = map _readKey2Key readKeys in
    let signals = _expr2intSeqOfSeq (mapFindExn "signals" bindings) in

    zipWith (lam k. lam s. {id = k, values = s}) keys signals

  else error "Expected record"

let parseReferences : String -> [Reference] = lam filename.
  use BootParser in
  let str = readFile filename in
  let parsed = parseMExprString [] str in

  match parsed with TmRecord {bindings = bindings} then
    let bindings = _mapSidToString bindings in

    let keys = _expr2strSeq (mapFindExn "keys" bindings) in
    let genomes = _expr2intSeqOfSeq (mapFindExn "genomes" bindings) in

    zipWith (lam k. lam g. {id = k, genome = g}) keys genomes
  else error "Expected record"

mexpr
dprintLn (
parseModel (get argv 1)
);

dprintLn (
parseSignals (get argv 2)
);

dprintLn (
parseReferences (get argv 3)
)
