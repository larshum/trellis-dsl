include "../main.mc"
include "../parse.mc"

let bases = "ACGT"

let baseToIndex = lam base : Char.
  match base with 'A' then 0
  else match base with 'C' then 1
  else match base with 'G' then 2
  else match base with 'T' then 3
  else never

let printFloatSeq = lam s : [Float].
  strJoin "\n" [
    int2string (length s),
    join (map (lam f : Float. concat (float2string f) " ") s)
  ]

let printIntSeq = lam s : [Int].
  strJoin "\n" [
    int2string (length s),
    join (map (lam i : Int. concat (int2string i) " ") s)
  ]

let transitionProb = lam model : ViterbiParams. lam s1 : State. lam s2 : State.
  let stateIdx = stateToIndex (length bases) baseToIndex s1 in
  let baseIdx = baseToIndex (last s2.kmer) in
  let baseProb = get (get model.transitionProbabilities baseIdx) stateIdx in
  let durProb =
    if eqi s1.layer 1 then
      get model.duration (subi s2.layer 1)
    else if eqi s1.layer model.dMax then
      if eqi s2.layer model.dMax then
        model.tailFactor
      else if eqi s2.layer (subi model.dMax 1) then
        model.tailFactorComp
      else divf (negf 1.0) 0.0
    else log1
  in
  probMul baseProb durProb

let cmpState : State -> State -> Int = lam s1 : State. lam s2 : State.
  let i1 = stateToIndex (length bases) baseToIndex s1 in
  let i2 = stateToIndex (length bases) baseToIndex s2 in
  subi i1 i2

let printModel = lam model : ViterbiParams.
  let states = states bases model.k model.dMax in
  let predecessors =
    map (lam s2.
      let pre = setOfSeq cmpState (pred bases model.dMax s2) in
      map (lam s1.
        if setMem s1 pre then
          stateToIndex (length bases) baseToIndex s1
        else negi 1) states) states
  in
  let transitions =
    map (lam s1. map (lam s2. transitionProb model s1 s2) states) states
  in
  strJoin "\n" [
    int2string model.signalLevels,
    strJoin "\n" (map (lam s : [Float]. printFloatSeq s) model.observationProbabilities),
    printFloatSeq model.duration,
    int2string model.k,
    int2string model.dMax,
    float2string model.tailFactor,
    float2string model.tailFactorComp,
    strJoin "\n" (map (lam s : [Int]. join (map (lam i. concat (int2string i) " ") s)) predecessors),
    strJoin "\n" (map (lam s : [Float]. join (map (lam f. concat (float2string f) " ") s)) transitions)
 ]

let printSignal = lam signal : Signal.
  strJoin "\n" [
    int2string (length signal.id),
    signal.id,
    printIntSeq signal.values
  ]

let printSignals = lam signals : [Signal].
  join [
    int2string (length signals),
    "\n",
    strJoin "\n" (map printSignal signals)
  ]

mexpr

let model = parseModel (get argv 1) in
let signals = parseSignals (get argv 2) in
writeFile "model.txt" (printModel model);
writeFile "signals.txt" (printSignals signals)
