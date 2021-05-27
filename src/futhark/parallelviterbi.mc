
type LogProb = Float
type ViterbiResult = {prob : LogProb, states : [Int]}

-- Redefinitions of standard library functions with specialized type
-- annotations as we currently do not support generic types.
let head : [Int] -> Int = lam s : [Int].
  let h : Int = get s 0 in
  h

let getLogProb : [LogProb] -> Int -> LogProb = lam s : [LogProb]. lam idx : Int.
  get s idx

let identity : LogProb -> LogProb = lam x : LogProb. x

let mapi : (Int -> Int -> LogProb) -> [Int] -> [LogProb] =
  lam f : Int -> Int -> LogProb. lam s : [Int].
  let f = lam x : (Int, Int). f x.0 x.1 in
  let is : [(Int, Int)] = create (length s) (lam i : Int. (i, get s i)) in
  let res : [LogProb] = parallelMap f is in
  res

let probMul : LogProb -> LogProb -> LogProb = addf

let maxByStateExn : (Int -> LogProb) -> [Int] -> Int =
  lam f : Int -> LogProb. lam s : [Int].
  let h = head s in
  let t = tail s in
  parallelReduce
    (lam x : Int. lam y : Int.
      if gtf (f x) (f y) then x else y)
    h
    t

let maxIndexByStateExn : [LogProb] -> Int =
  lam s : [LogProb].
  let is : [(Int, LogProb)] = create (length s) (lam i : Int. (i, get s i)) in
  let h = head is in
  let t = tail is in
  (parallelReduce
    (lam x : (Int, LogProb). lam y : (Int, LogProb).
      if gtf x.1 y.1 then x else y)
    h
    t).0

-- Assumptions on data:
-- * States have been mapped to integers in range 0..n-1 (can use sequences instead of map)
-- * Inputs have been mapped to integers in range 0..m-1 (instead of being an arbitrary type)
let parallelViterbi : [[Int]] -> [[LogProb]] -> [LogProb] -> Int
                   -> [[LogProb]] -> [Int] -> ViterbiResult =
  lam predecessors : [[Int]].
  lam transitionProb : [[LogProb]].
  lam initProbs : [LogProb].
  lam numStates : Int.
  lam outputProb : [[LogProb]].
  lam inputs : [Int].
  match inputs with [x] ++ inputs then
    let chi1 : [LogProb] =
      create
        numStates
        (lam state : Int.
          probMul (getLogProb initProbs state) (getLogProb (get outputProb state) x)) in
    recursive
      let forward =
        lam chi : [LogProb].
        lam zeta : [[Int]].
        lam inputs : [Int].
        match inputs with [] then {chi = chi, zeta = zeta}
        else match inputs with [x] ++ inputs then
          let logProbFrom : Int -> Int -> LogProb =
            lam state. lam pre.
              probMul (getLogProb chi pre)
                      (getLogProb (get transitionProb pre) state) in
          let newZeta : [Int] = create numStates
            (lam state : Int. maxByStateExn (logProbFrom state) (get predecessors state)) in
          let newChi = mapi
            (lam state : Int. lam pre : Int. probMul (logProbFrom state pre)
                                                     (getLogProb (get outputProb state) x))
            newZeta in
          forward newChi (snoc zeta newZeta) inputs
        else never
      let backwardStep =
        lam acc : [Int].
        lam zeta : [[Int]].
        match zeta with [] then acc
        else match zeta with [here] ++ zeta then
          backwardStep (cons (get here (head acc)) acc) zeta
        else never
    in
    match forward chi1 [] inputs with {chi = chi, zeta = zeta} then
      let lastState = maxIndexByStateExn chi in
      let logprob = get chi lastState in
      {prob = logprob, states = reverse (backwardStep [lastState] (reverse zeta))}
    else never
  else never

mexpr

parallelViterbi
  [[]]
  [[]]
  []
  0
  [[]]
  []
