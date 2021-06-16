include "../main.mc"
include "../parse.mc"

let bases = "ACGT"

let baseToIndex = lam base : Char.
  match base with 'A' then 0
  else match base with 'C' then 1
  else match base with 'G' then 2
  else match base with 'T' then 3
  else never

let indexToBase = lam idx : Int.
  match idx with 0 then 'A'
  else match idx with 1 then 'C'
  else match idx with 2 then 'G'
  else match idx with 3 then 'T'
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

let statesPerLayer = lam model : ViterbiParams.
  floorfi (powf (int2float (length bases)) model.k)

let stateToIndex = lam model : ViterbiParams. lam s : State.
  addi (muli (subi s.layer 1) (statesPerLayer model))
       (stateToIndex (length bases) baseToIndex s)

let indexToState = lam model : ViterbiParams. lam i : Int.
  let layer = addi 1 (divi i (statesPerLayer model)) in
  let kmerIndex = modi i (statesPerLayer model) in
  let base1 = indexToBase (modi kmerIndex (length bases)) in
  let base2 = indexToBase (modi (divi kmerIndex (length bases)) (length bases)) in
  let base3 = indexToBase (modi (divi kmerIndex (muli (length bases) (length bases))) (length bases)) in
  {kmer = [base1, base2, base3], layer = layer}

let cmpState : ViterbiParams -> State -> State -> Int =
  lam model : ViterbiParams. lam s1 : State. lam s2 : State.
  subi (stateToIndex model s1) (stateToIndex model s2)

let printModel = lam model : ViterbiParams.
  let states = sort (cmpState model) (states bases model.k model.dMax) in
  let predecessors =
    map (lam s2. map (stateToIndex model) (pred bases model.dMax s2)) states
  in
  strJoin "\n" [
    printFloatSeq model.duration,
    int2string model.k,
    int2string model.dMax,
    float2string model.tailFactor,
    float2string model.tailFactorComp,
    int2string model.signalLevels,
    strJoin "\n" (map (lam s : [Float]. strJoin " " (map float2string s)) model.observationProbabilities),
    int2string (length (get predecessors 0)),
    strJoin "\n" (map (lam s : [Int]. join (map (lam i. concat (int2string i) " ") s)) predecessors),
    strJoin "\n" (map (lam s : [Float]. join (map (lam f. concat (float2string f) " ") s))
                      model.transitionProbabilities)
 ]

let printSignal = lam signal : Signal.
  strJoin "\n" [
    int2string (length signal.id),
    signal.id,
    printIntSeq signal.values
  ]

let compareSignalLength : Signal -> Signal -> Int = lam s1. lam s2.
  subi (length s1.values) (length s2.values)

let printSignals = lam signals : [Signal].
  match max compareSignalLength signals with Some longestSignal then
    let signal : Signal = longestSignal in
    strJoin "\n" [
      int2string (length signals),
      int2string (length signal.values),
      strJoin "\n" (map printSignal signals)
    ]
  else error "Empty signal input"

let printReferences = lam references : [Reference].
  let printGenome = lam genome : [Int]. map indexToBase genome in
  strJoin "\n"
    (map
      (lam ref : Reference. join [ref.id, "\n", printGenome ref.genome])
      references)

mexpr

let model = parseModel (get argv 1) in
let signals = parseSignals (get argv 2) in
let references = parseReferences (get argv 3) in
writeFile "model.txt" (printModel model);
writeFile "signals.txt" (printSignals signals);
writeFile "reference.txt" (printReferences references)
