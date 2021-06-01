type ViterbiResult = {prob : Float, states : [Int]}
type ViterbiForwardResult = {chi : [Float], zeta : [[Int]]}

let getFloat : [Float] -> Int -> Float = lam s : [Float]. lam idx : Int.
  get s idx

let identity : Float -> Float = lam x : Float. x

let mapi : (Int -> Int -> Float) -> [Int] -> [Float] =
  lam f : Int -> Int -> Float. lam s : [Int].
  let f = lam x : (Int, Int). f x.0 x.1 in
  let is : [(Int, Int)] = create (length s) (lam i : Int. (i, get s i)) in
  let res : [Float] = parallelMap f is in
  res

let probMul : Float -> Float -> Float = addf

let maxByStateExn : (Int -> Float) -> [Int] -> Int =
  lam f : Int -> Float. lam s : [Int].
  match s with [h] ++ t then
    parallelReduce
      (lam x : Int. lam y : Int.
        if gtf (f x) (f y) then x else y)
      h
      t
  else never

let maxIndexByStateExn : [Float] -> Int =
  lam s : [Float].
  let is : [(Int, Float)] = create (length s) (lam i : Int. (i, get s i)) in
  match is with [h] ++ t then
    (parallelReduce
      (lam x : (Int, Float). lam y : (Int, Float).
        if gtf x.1 y.1 then x else y)
      h
      t).0
  else never

let parallelViterbi_forward : [[Int]] -> [[Float]] -> [[Float]] -> [Int]
                           -> [Float] -> ViterbiForwardResult =
  lam predecessors : [[Int]].
  lam transitionProb : [[Float]].
  lam outputProb : [[Float]].
  lam inputs : [Int].
  lam chi1 : [Float].
  let numStates : Int = length predecessors in
  let n = length inputs in
  let zeta : [[Int]] = create n (lam. create numStates (lam. 0)) in
  recursive let work : [Float] -> [[Int]] -> Int -> Int
                    -> {chi : [Float], zeta : [[Int]]} =
      lam chi : [Float].
      lam zeta : [[Int]].
      lam i : Int.
      lam n : Int.
      if lti i n then
        let x : Int = get inputs i in
        let logProbFrom : Int -> Int -> Float =
          lam state. lam pre.
            probMul (getFloat chi pre)
                    (getFloat (get transitionProb pre) state) in
        let newZeta : [Int] = create numStates
          (lam state : Int. maxByStateExn (logProbFrom state) (get predecessors state)) in
        let newChi = mapi
          (lam state : Int. lam pre : Int. probMul (logProbFrom state pre)
                                                   (getFloat (get outputProb state) x))
          newZeta in
        let zeta : [[Int]] = set zeta i newZeta in
        work newChi zeta (addi i 1) n
      else {chi = chi, zeta = zeta}
  in
  work chi1 zeta 0 n

let parallelViterbi_backwardStep : Int -> [[Int]] -> [Int] =
  lam lastState : Int.
  lam zeta : [[Int]].
  let n = length zeta in
  let acc : [Int] = concat [lastState] (create n (lam. 0)) in
  recursive let work : [Int] -> Int -> Int -> [Int] =
    lam acc : [Int].
    lam i : Int.
    lam n : Int.
    if lti i n then
      let ii = addi i 1 in
      let here : [Int] = get zeta i in
      let acc : [Int] = set acc ii (get here (get acc i)) in
      work acc ii n
    else acc
  in
  work acc 0 n

let getProb : ViterbiResult -> Float =
  lam result : ViterbiResult.
  result.prob

let getStates : ViterbiResult -> [Int] =
  lam result : ViterbiResult.
  result.states

-- Assumptions on data:
-- * States have been mapped to integers in range 0..n-1 (can use sequences instead of map)
-- * Inputs have been mapped to integers in range 0..m-1 (instead of being an arbitrary type)
let parallelViterbi : [[Int]] -> [[Float]] -> [Float] -> [[Float]]
                   -> [Int] -> ViterbiResult =
  lam predecessors : [[Int]].
  lam transitionProb : [[Float]].
  lam initProbs : [Float].
  lam outputProb : [[Float]].
  lam inputs : [Int].
  match inputs with [x] ++ inputs then
    let numStates : Int = length predecessors in
    let chi1 : [Float] =
      create
        numStates
        (lam state : Int.
          probMul (getFloat initProbs state) (getFloat (get outputProb state) x)) in
    let r : ViterbiForwardResult =
      parallelViterbi_forward predecessors transitionProb outputProb
                              inputs chi1 in
    match r with {chi = chi, zeta = zeta} then
      let lastState = maxIndexByStateExn chi in
      let logprob : Float = get chi lastState in
      let states : [Int] = reverse (parallelViterbi_backwardStep lastState (reverse zeta)) in
      {prob = logprob, states = states}
    else never
  else never

mexpr

let result =
  parallelViterbi
    [[]]
    [[]]
    []
    [[]]
    [] in
let p = getProb result in
let states = getStates result in
()
