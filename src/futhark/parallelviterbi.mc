
type LogProb = Float
type ViterbiForwardResult = {chi : [LogProb], zeta : [[Int]]}
type ViterbiResult = {prob : LogProb, states : [Int]}

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
  match s with [h] ++ t then
    parallelReduce
      (lam x : Int. lam y : Int.
        if gtf (f x) (f y) then x else y)
      h
      t
  else never

let maxIndexByStateExn : [LogProb] -> Int =
  lam s : [LogProb].
  let is : [(Int, LogProb)] = create (length s) (lam i : Int. (i, get s i)) in
  match is with [h] ++ t then
    (parallelReduce
      (lam x : (Int, LogProb). lam y : (Int, LogProb).
        if gtf x.1 y.1 then x else y)
      h
      t).0
  else never

recursive
  let parallelViterbi_forward : [[Int]] -> [[LogProb]] -> [[LogProb]] -> [Int]
                             -> [LogProb] -> [[Int]] -> Int -> Int
                             -> ViterbiForwardResult =
    lam predecessors : [[Int]].
    lam transitionProb : [[LogProb]].
    lam outputProb : [[LogProb]].
    lam inputs : [Int].
    lam chi : [LogProb].
    lam zeta : [[Int]].
    lam i : Int.
    lam n : Int.
    if lti i n then
      let numStates : Int = length predecessors in
      let x : Int = get inputs i in
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
      let zeta = set zeta i newZeta in
      parallelViterbi_forward predecessors transitionProb outputProb inputs
                              newChi zeta (addi i 1) n
    else {chi = chi, zeta = zeta}
  let parallelViterbi_backwardStep : [Int] -> [[Int]] -> Int -> Int -> [Int] =
    lam acc : [Int].
    lam zeta : [[Int]].
    lam i : Int.
    lam n : Int.
    if lti i n then
      let ii = addi i 1 in
      let here : [Int] = get zeta i in
      let acc : [Int] = set acc ii (get here (get acc i)) in
      parallelViterbi_backwardStep acc zeta ii n
    else acc
end

-- Assumptions on data:
-- * States have been mapped to integers in range 0..n-1 (can use sequences instead of map)
-- * Inputs have been mapped to integers in range 0..m-1 (instead of being an arbitrary type)
let parallelViterbi : [[Int]] -> [[LogProb]] -> [LogProb] -> [[LogProb]]
                   -> [Int] -> ViterbiResult =
  lam predecessors : [[Int]].
  lam transitionProb : [[LogProb]].
  lam initProbs : [LogProb].
  lam outputProb : [[LogProb]].
  lam inputs : [Int].
  match inputs with [x] ++ inputs then
    let numStates : Int = length predecessors in
    let chi1 : [LogProb] =
      create
        numStates
        (lam state : Int.
          probMul (getLogProb initProbs state) (getLogProb (get outputProb state) x)) in
    let n = length inputs in
    let acc : [[Int]] = create n (lam. create numStates (lam. 0)) in
    let r : ViterbiForwardResult = parallelViterbi_forward chi1 acc 0 n in
    match r with {chi = chi, zeta = zeta} then
      let lastState = maxIndexByStateExn chi in
      let logprob : LogProb = get chi lastState in
      let n = length zeta in
      let acc : [Int] = create (addi n 1) (lam. 0) in
      let states : [Int] = reverse (parallelViterbi_backwardStep acc (reverse zeta) 0 n) in
      {prob = logprob, states = states}
    else never
  else never

mexpr

parallelViterbi
  [[]]
  [[]]
  []
  [[]]
  []
