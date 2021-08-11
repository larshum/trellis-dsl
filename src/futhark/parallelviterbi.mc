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
  let is = create (length s) (lam i. (i, get s i)) in
  let f = lam a. lam b.
    if gtf a.1 b.1 then a else b
  in
  recursive let work = lam acc. lam s.
    if null s then acc
    else work (f acc (head s)) (tail s)
  in
  (work (head is) (tail is)).0

let parallelViterbi_forward : [[Int]] -> (Int -> Int -> Float) -> (Int -> Int -> Float)
                           -> [Int] -> [Float] -> {chi : [Float], zeta : [[Int]]} =
  lam predecessors.
  lam transitionProb.
  lam outputProb.
  lam inputs.
  lam chi1.
  let numStates = length predecessors in
  let n = length inputs in
  let zeta = create n (lam. create numStates (lam. 0)) in
  recursive let work = lam acc. lam idx.
    if null idx then acc
    else
      let i = head idx in
      let x = get inputs i in
      let logProbFrom =
        lam state. lam pre.
          probMul (get acc.chi pre)
                  (transitionProb pre state) in
      let newZeta = create numStates
        (lam state. maxByStateExn (logProbFrom state) (get predecessors state)) in
      let newChi = mapi
        (lam state. lam pre. probMul (logProbFrom state pre)
                                     (outputProb state x))
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
  in work 1 (create e (lam. b))

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
  let output = create nbatches (lam. create batchOutputSize (lam. 0)) in
  recursive
    let loop = lam acc. lam idx.
      if null idx then acc
      else
        let i = head idx in
        let offset = muli i batchOutputSize in
        let batch = subsequence signal offset batchSize in
        let out = viterbi predecessors transitionProb initProbs outputProb batch in
        let acc = set acc i (subsequence out 0 batchOutputSize) in
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
  let transitionProb = getTransitionProb transProb duration k dMax
                                         statesPerLayer tailFactor tailFactorComp in
  let outputProb = getOutputProb outProb statesPerLayer in
  let batchOutputSize = subi batchSize batchOverlap in
  let nbatches = divf (subf (length (head inputSignals)) batchOverlap)
                      batchOutputSize in
  let n = muli batchOutputSize nbatches in
  map
    (lam signal.
      subsequence
        (batchedViterbi predecessors transitionProb initProbs outputProb
                        batchSize batchOverlap signal)
        0 n)
    inputSignals

mexpr

-- Nonsense utest to prevent the deadcode elimination from removing the called
-- functions. The utest will be ignored by 'parallelmi'.
utest
  parallelViterbi
  [[]]
  [[]]
  []
  [[]]
  []
  0
  0
  0
  0.0
  0.0
  0
  0
  [[]]
with () in
()
