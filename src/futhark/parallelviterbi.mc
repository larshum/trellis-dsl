type State = Int
type LogProb = Float
type ViterbiResult = {prob : LogProb, states : [State]}

-- Redefinitions of standard library functions with specialized type
-- annotations as we currently do not support generic types.
let head : [State] -> State = lam s : [State].
  let h : State = get s 0 in
  h

let getLogProb : [LogProb] -> Int -> LogProb = lam s : [LogProb]. lam idx : Int.
  get s idx

let identity : LogProb -> LogProb = lam x : LogProb. x

let indexedSeq : [State] -> [(Int, State)] = lam s : [State].
  create
    (length s)
    (lam i : Int.
      let e : State = get s i in
      (i, e))

let mapi : (Int -> State -> LogProb) -> [State] -> [LogProb] =
  lam f : Int -> State -> LogProb. lam s : [State].
  let f = lam x : (Int, State). f x.0 x.1 in
  let is : [(Int, State)] = create (length s) (lam i : Int. (i, get s i)) in
  let res : [LogProb] = parallelMap f is in
  res

let probMul : LogProb -> LogProb -> LogProb = addf

let maxByStateExn : (State -> LogProb) -> [State] -> State =
  lam f : State -> LogProb. lam s : [State].
  match s with [h] ++ t then
    parallelReduce
      (lam x : State. lam y : State.
        if gtf (f x) (f y) then x else y)
      h
      t
  else never -- empty sequence

let maxIndexByStateExn : (LogProb -> LogProb) -> [LogProb] -> Int =
  lam s : [LogProb].
  let is : [(Int, LogProb)] = create (length s) (lam i : Int. (i, get s i)) in
  match is with [h] ++ t then
    (parallelReduce
      (lam x : (Int, LogProb). lam y : (Int, LogProb).
        if gtf x.1 y.1 then x else y)
      h
      t).0
  else never -- empty sequence

-- Assumptions on data:
-- * States have been mapped to integers in range 0..n-1 (can use sequences instead of map)
-- * Inputs have been mapped to integers in range 0..m-1 (instead of being an arbitrary type)
let parallelViterbi : [[State]] -> [[LogProb]] -> [LogProb] -> Int
                   -> [[LogProb]] -> [Int] -> ViterbiResult =
  lam predecessors : [[State]].
  lam transitionProb : [[LogProb]].
  lam initProbs : [LogProb].
  lam numStates : Int.
  lam outputProb : [[LogProb]].
  lam inputs : [Int].
  match inputs with [x] ++ inputs then
    let chi1 : [LogProb] =
      create
        numStates
        (lam state : State.
          probMul (getLogProb initProbs state) (getLogProb (get outputProb state) x)) in
    recursive
      let forward =
        lam chi : [LogProb].
        lam zeta : [[State]].
        lam inputs : [Int].
        match inputs with [] then {chi = chi, zeta = zeta}
        else match inputs with [x] ++ inputs then
          let logProbFrom : State -> State -> LogProb =
            lam state. lam pre. probMul (getLogProb chi pre)
                                        (getLogProb (get transitionProb pre) state) in
          let newZeta : [State] = create numStates
            (lam state : State. maxByStateExn (logProbFrom state) (get predecessors state)) in
          let newChi = mapi
            (lam state : State. lam pre : State. probMul (logProbFrom state pre)
                                                         (getLogProb (get outputProb state) x))
            newZeta in
          forward newChi (snoc zeta newZeta) inputs
        else never
      let backwardStep =
        lam acc : [State].
        lam zeta : [[State]].
        match zeta with [] then acc
        else match zeta with zeta ++ [here] then
          backwardStep (cons (get here (head acc)) acc) zeta
        else never
    in
    match forward chi1 [] inputs with {chi = chi, zeta = zeta} then
      let lastState = maxIndexByStateExn identity chi in
      let logprob = get chi lastState in
      {prob = logprob, states = backwardStep [lastState] zeta}
    else never
  else never

mexpr

-- Need to contain a call to parallel viterbi implementation, or it will be
-- removed by the dead code elimintation step.
parallelViterbi
  [[]]
  [[]]
  []
  0
  [[]]
  []

/-
let compareViterbiResult = lam delta. lam l : ViterbiResult. lam r : ViterbiResult.
  match l with {states = lstates, prob = lprob} then
    match r with {states = rstates, prob = rprob} then
      and (all (lam b. b) (zipWith eqi lstates rstates))
          (ltf (absf (subf lprob rprob)) delta)
    else never
  else never
in

let delta = 1e-2 in

let baseToIndex = lam base : Char.
  if eqc base 'A' then 0
  else if eqc base 'C' then 1
  else if eqc base 'G' then 2
  else if eqc base 'T' then 3
  else error (concat "Unknown base character: " [base])
in

-- Example adapted from
-- https://personal.utdallas.edu/~prr105020/biol6385/2019/lecture/lecture12_Viterbi_handout.pdf
let predecessors = [[0, 1], [0, 1]] in
let transitionProbs = [[negf 1.0, negf 1.0], [negf 1.322, negf 0.737]] in
let initProbs = [negf 1.0, negf 1.0] in
let states = [0, 1] in
let outputProbs = [
  [negf 2.322, negf 1.737, negf 1.737, negf 2.322],
  [negf 1.737, negf 2.322, negf 2.322, negf 1.737]
] in
let inputs = map baseToIndex ['G', 'G', 'C', 'A', 'C', 'T', 'G', 'A', 'A'] in
let mostProbableSequence =
  parallelViterbi
    predecessors
    transitionProbs
    initProbs
    (length states)
    outputProbs
    inputs
in
let expected = {prob = negf 24.49, states = [0, 0, 0, 1, 1, 1, 1, 1, 1]} in
utest mostProbableSequence with expected using compareViterbiResult delta in

-- Example adapted from https://www.pythonpool.com/viterbi-algorithm-python/
let predecessors = [[0, 1], [0, 1]] in
let transitionProbs = [[negf 0.515, negf 1.737], [negf 1.322, negf 0.737]] in
let initProbs = [negf 0.737, negf 1.322] in
let states = [0, 1] in
let outputProbs = [
  [negf 1.0, negf 1.322, negf 3.322],
  [negf 3.322, negf 1.737, negf 0.737]
] in
let inputs = [0, 1, 2] in
let mostProbableSequence =
  parallelViterbi
    predecessors
    transitionProbs
    initProbs
    (length states)
    outputProbs
    inputs
in
let expected = {prob = negf 6.047, states = [0, 0, 1]} in
utest mostProbableSequence with expected using compareViterbiResult delta in
-/
()
