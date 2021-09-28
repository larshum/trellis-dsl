include "state.mc"

type ViterbiForwardResult = {chi : [Float], zeta : [[Int]]}

let mapi : (Int -> Int -> Float) -> [Int] -> [Float] =
  lam f. lam s.
  recursive let work = lam acc. lam sa. lam sb.
    if null sa then acc
    else if null sb then acc
    else work (snoc acc (f (head sa) (head sb))) (tail sa) (tail sb)
  in work [] (create (length s) (lam i. i)) s

let probMul = addf

let maxByStateExn : (Int -> Float) -> [Int] -> Int =
  lam f. lam s.
  let h = head s in
  let n = length s in
  recursive let work = lam acc. lam idx.
    if null idx then acc
    else
      let i = head idx in
      let x = get s i in
      let m = if gtf (f acc) (f x) then acc else x in
      work m (tail idx)
  in
  work h (create n (lam i. i))

let maxIndexByStateExn : [Float] -> Int =
  lam s.
  let is : [(Int, Float)] =
    create
      (length s)
      (lam i.
        let t : (Int, Float) = (i, get s i) in t) in
  let f : (Int, Float) -> (Int, Float) -> (Int, Float) = lam a. lam b.
    if gtf a.1 b.1 then a else b
  in
  recursive let work = lam acc. lam s.
    if null s then acc
    else work (f acc (head s)) (tail s)
  in
  let r : (Int, Float) = work (head is) (tail is) in
  r.0

let parallelViterbi_forward : [[Int]] -> (Int -> Int -> Float) -> (Int -> Int -> Float)
                           -> [Int] -> [Float] -> {chi : [Float], zeta : [[Int]]} =
  lam predecessors.
  lam transitionProb.
  lam outputProb.
  lam inputs.
  lam chi1.
  let numStates = length predecessors in
  let n = length inputs in
  let zeta : [[Int]] = create n (lam.
    let t : [Int] = create numStates (lam. 0) in t) in
  recursive let work : ViterbiForwardResult -> Int -> ViterbiForwardResult =
    lam acc. lam idx.
    if null idx then acc
    else
      let i = head idx in
      let x = get inputs i in
      let logProbFrom =
        lam state : Int. lam pre : Int.
          probMul (get acc.chi pre)
                  (transitionProb pre state) in
      let newZeta = create numStates
        (lam state : Int. maxByStateExn (logProbFrom state) (get predecessors state)) in
      let newChi = mapi
        (lam state : Int. lam pre : Int.
          probMul (logProbFrom state pre) (outputProb state x))
        newZeta in
      let zeta = set acc.zeta i newZeta in
      work {chi = newChi, zeta = zeta} (tail idx)
  in
  work {chi = chi1, zeta = zeta} (create n (lam i. i))

let parallelViterbi_backwardStep : Int -> [[Int]] -> [Int] =
  lam lastState.
  lam zeta.
  let n = length zeta in
  let acc = concat [lastState] (create n (lam. 0)) in
  recursive let work = lam acc. lam idx.
    if null idx then acc
    else
      let i = head idx in
      let ii = addi i 1 in
      let here = get zeta i in
      let acc = set acc ii (get here (get acc i)) in
      work acc (tail idx)
  in
  work acc (create n (lam i. i))

-- Assumptions on data:
-- * States have been mapped to integers in range 0..n-1 (can use sequences instead of map)
-- * Inputs have been mapped to integers in range 0..m-1 (instead of being an arbitrary type)
let viterbi : [[Int]] -> (Int -> Int -> Float) -> [Float]
           -> (Int -> Int -> Float) -> [Int] -> [Int] =
  lam predecessors.
  lam transitionProb.
  lam initProbs.
  lam outputProb.
  lam inputs.
  let x = head inputs in
  let inputs = tail inputs in
  let numStates = length predecessors in
  let chi1 =
    create
      numStates
      (lam state.
        probMul (get initProbs state) (outputProb state x)) in
  let r = parallelViterbi_forward predecessors transitionProb outputProb
                                  inputs chi1 in
  match r with {chi = chi, zeta = zeta} then
    let lastState = maxIndexByStateExn chi in
    reverse (parallelViterbi_backwardStep lastState (reverse zeta))
  else never

let stateLayer : Int -> Int -> Int =
  lam statesPerLayer. lam state.
  divi state statesPerLayer

let pow : Int -> Int -> Int = lam b. lam e.
  recursive let work = lam acc. lam s.
    if null s then acc
    else work (muli (head s) acc) (tail s)
  in
  let i = 1 in
  work i (create e (lam. b))

let getTransitionProb : [[Float]] -> [Float] -> Int -> Int -> Int -> Float
                     -> Float -> Int -> Int -> Float =
  lam transProbs. lam duration. lam k. lam dMax. lam statesPerLayer.
  lam tailFactor. lam tailFactorComp. lam fromState. lam toState.
  let stateIdx = modi fromState statesPerLayer in
  let baseIdx = modi (divi toState (pow 4 (subi k 1))) 4 in
  let baseProb = get (get transProbs baseIdx) stateIdx in
  let durProb =
    if eqi (stateLayer statesPerLayer fromState) 0 then
      get duration (stateLayer statesPerLayer toState)
    else if eqi (stateLayer statesPerLayer fromState) dMax then
      if eqi (stateLayer statesPerLayer toState) dMax then
        tailFactor
      else tailFactorComp
    else 0.0
  in
  probMul baseProb durProb

let getOutputProb : [[Float]] -> Int -> Int -> Int -> Float =
  lam outProb. lam statesPerLayer. lam state. lam input.
  get (get outProb input) (modi state statesPerLayer)

let batchedViterbi : [[Int]] -> (Int -> Int -> Float) -> [Float]
                  -> (Int -> Int -> Float) -> Int -> Int -> [Int] -> [Int] =
  lam predecessors.
  lam transitionProb.
  lam initProbs.
  lam outputProb.
  lam batchSize.
  lam batchOverlap.
  lam signal.
  let batchOutputSize = subi batchSize batchOverlap in
  let nbatches = divi (subi (length signal) batchOverlap) batchOutputSize in
  let output : [[Int]] =
    create
      nbatches
      (lam.
        let t : [Int] = create batchOutputSize (lam. 0) in t) in
  recursive
    let loop = lam acc : [[Int]]. lam idx : [Int].
      if null idx then acc
      else
        let i = head idx in
        let offset = muli i batchOutputSize in
        let batch : [Int] = subsequence signal offset batchSize in
        let out : [Int] = viterbi predecessors transitionProb initProbs outputProb batch in
        let batchOut : [Int] = subsequence out 0 batchOutputSize in
        let acc : [[Int]] = set acc i batchOut in
        loop acc (tail idx)
    let flatMapId = lam acc. lam s.
      if null s then acc
      else
        let h = head s in
        let x = h in
        flatMapId (concat acc x) (tail s)
  in
  flatMapId [] (loop output (create nbatches (lam i. i)))

let parallelViterbi : [[Int]] -> [[Float]] -> [Float] -> [[Float]]
                   -> [Float] -> Int -> Int -> Int -> Float -> Float
                   -> Int -> Int -> [[Int]] -> [[Int]] =
  lam predecessors.
  lam transProb.
  lam initProbs.
  lam outProb.
  lam duration.
  lam k.
  lam dMax.
  lam statesPerLayer.
  lam tailFactor.
  lam tailFactorComp.
  lam batchSize.
  lam batchOverlap.
  lam inputSignals.
  let transitionProb : Int -> Int -> Float =
    getTransitionProb transProb duration k dMax
                      statesPerLayer tailFactor tailFactorComp in
  let outputProb : Int -> Int -> Float = getOutputProb outProb statesPerLayer in
  let batchOutputSize = subi batchSize batchOverlap in
  let nbatches = divi (subi (length (head inputSignals)) batchOverlap)
                      batchOutputSize in
  let n = muli batchOutputSize nbatches in
  map
    (lam signal.
      let batch : [Int] =
        batchedViterbi predecessors transitionProb initProbs
                       outputProb batchSize batchOverlap signal in
      let t : [Int] = subsequence batch 0 n in
      t)
    inputSignals

mexpr

let t0 = wallTimeMs () in
let model = parseModel (get argv 1) in
let t1 = wallTimeMs () in
let signals = parseSignals (get argv 2) in
let t2 = wallTimeMs () in
printLn (join ["parseModel: ", float2string (divf (subf t1 t0) 1000.0)]);
printLn (join ["parseSignals: ", float2string (divf (subf t2 t1) 1000.0)]);

let batchSize = 1024 in
let batchOverlap = 128 in

let states : [State] = sort (cmpState model) (stateSpace model) in

let predecessors : [[Int]] =
  map (lam s. map (stateToIndex model) (pred model s)) states
in

let transProb : [[Float]] = model.transitionProbabilities in

let initProbs : [Float] =
  map
    (lam s : State.
      if eqi s.layer 0 then
        divf 1.0 (int2float (statesPerLayer model))
      else negf (divf 1.0 0.0))
    states
in

let outProb : [[Float]] = model.observationProbabilities in
let duration : [Float] = model.duration in
let k : Int = model.k in
let dMax : Int = model.dMax in
let statesPerLayer : Int = statesPerLayer model in
let tailFactor : Float = model.tailFactor in
let tailFactorComp : Float = model.tailFactorComp in

let paddedSignalValues : [[Int]] =
  let signalLength = lam signal : Signal. length signal.values in
  match max subi (map signalLength signals) with Some maxLength then
    -- Add extra padding to fit the extra batching overlap
    let batchOutputSize = subi batchSize batchOverlap in
    let lengthPlusBatch =
      addi
        (muli
          (divi (addi maxLength (addi batchOutputSize 1)) batchOutputSize)
          batchOutputSize)
        batchOverlap
    in
    map
      (lam signal : Signal.
        let values : [Int] = signal.values in
        let createPadded = lam i.
          if lti i (length values) then get values i else 0
        in
        create lengthPlusBatch createPadded)
      signals
  else []
in

let t0 = wallTimeMs () in
let result = accelerate
  (parallelViterbi
    predecessors
    transProb
    initProbs
    outProb
    duration
    k
    dMax
    statesPerLayer
    tailFactor
    tailFactorComp
    batchSize
    batchOverlap
    paddedSignalValues)
in
let t1 = wallTimeMs () in
printLn (join ["Viterbi time: ", float2string (divf (subf t1 t0) 1000.0)]);

printLn
  (strJoin "\n"
    (create (length result) (lam i.
      let inputSignal : Signal = get signals i in
      let signalLength = length inputSignal.values in
      let output = subsequence (get result i) 0 signalLength in
      join [inputSignal.id, "\n", printStateData (map (indexToState model) output)])))
