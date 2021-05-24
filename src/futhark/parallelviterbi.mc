
include "translate.mc"
let parallelReduce = lam f. lam ne. lam as.
  recursive let work = lam acc. lam as.
    work (f acc (head as)) (tail as)
  in
  work ne as
let map = lam f. lam s.
  recursive let work = lam acc. lam s.
    if null s then acc
    else
      work (snoc acc (f (head s))) (tail s)
  in
  work [] s
let parallelMap = lam f. lam as. map f as

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

let maxIndexByStateExn : [LogProb] -> Int =
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

let model = parseModel (get argv 1) in
let signals = parseSignals (get argv 2) in
let inputSignal : Signal = get signals 0 in

let bases = "ACGT" in

let stateToIndex = lam s : State.
  stateToIndex (length bases) baseToIndex s
in

let cmpState = lam s1 : State. lam s2 : State.
  subi (stateToIndex s1) (stateToIndex s2)
in

let states = states bases model.k model.dMax in
let predecessors =
  map
    (lam s1 : State.
      let preds = setOfSeq cmpState (pred bases model.dMax s1) in
      map
        (lam s2 : State.
          if setMem s2 preds then
            stateToIndex s2
          else negi 1)
        states)
    states in
let transitionProb =
  map (lam s1. map (lam s2. transitionProb model s1 s2) states) states in
let initProbs = lam s : State. initProbs (length bases) s in
let outputProb =
  map
    (lam s : State.
      create
        model.signalLevels
        (lam i : Int.
          let si = stateToIndex s in
          get (get model.observationProbabilities i) si))
    states
in

-- Need to contain a call to parallel viterbi implementation, or it will be
-- removed by the dead code elimintation step.
parallelViterbi
  predecessors
  transitionProb
  initProbs
  (length states)
  outputProb
  (subsequence inputSignal.values 0 10)
