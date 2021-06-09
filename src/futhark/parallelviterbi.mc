type ViterbiResult = {prob : Float, states : [Int]}
type ViterbiForwardResult = {chi : [Float], zeta : [[Int]]}

let mapi : (Int -> Int -> Float) -> [Int] -> [Float] =
  lam f. lam s.
  -- Would like to do it the following way, but there is no function for
  -- getting indices, and the below approach does not work because the type
  -- checker fails to infer that the length of idxs and the result is the same
  -- as length of s.

  --let idxs : [Int] = create (length s) (lam i : Int. i) in
  --let res : [Float] = parallelMap2 f idxs s in
  --res

  let f = lam x. f x.0 x.1 in
  let is = create (length s) (lam i. (i, get s i)) in
  parallelMap f is

let probMul = addf

let maxByStateExn : (Int -> Float) -> [Int] -> Int =
  lam f. lam s.
  let h = head s in
  let n = length s in
  recursive let work : Int -> Int -> Int -> Int =
    lam max. lam i. lam n.
    if lti i n then
      let x = get s i in
      let m =
        if gtf (f max) (f x) then
          max
        else x
      in
      work m (addi i 1) n
    else max
  in
  work h 0 n

let maxIndexByStateExn : [Float] -> Int =
  lam s.
  let is = create (length s) (lam i. (i, get s i)) in
  let h = head is in
  let t = tail is in
  (parallelReduce
    (lam x. lam y.
      if gtf x.1 y.1 then x else y)
    h
    t).0

let parallelViterbi_forward : [[Int]] -> [[Float]] -> [[Float]] -> [Int]
                           -> [Float] -> ViterbiForwardResult =
  lam predecessors.
  lam transitionProb.
  lam outputProb.
  lam inputs.
  lam chi1.
  let numStates = length predecessors in
  let n = length inputs in
  let zeta = create n (lam. create numStates (lam. 0)) in
  recursive let work : [Float] -> [[Int]] -> Int -> Int
                    -> {chi : [Float], zeta : [[Int]]} =
      lam chi.
      lam zeta.
      lam i.
      lam n.
      if lti i n then
        let x = get inputs i in
        let logProbFrom =
          lam state. lam pre.
            probMul (get chi pre)
                    (get (get transitionProb pre) state) in
        let newZeta = create numStates
          (lam state. maxByStateExn (logProbFrom state) (get predecessors state)) in
        let newChi = mapi
          (lam state. lam pre. probMul (logProbFrom state pre)
                                                   (get (get outputProb state) x))
          newZeta in
        let zeta = set zeta i newZeta in
        work newChi zeta (addi i 1) n
      else {chi = chi, zeta = zeta}
  in
  work chi1 zeta 0 n

let parallelViterbi_backwardStep : Int -> [[Int]] -> [Int] =
  lam lastState.
  lam zeta.
  let n = length zeta in
  let acc : [Int] = concat [lastState] (create n (lam. 0)) in
  recursive let work : [Int] -> Int -> Int -> [Int] =
    lam acc.
    lam i.
    lam n.
    if lti i n then
      let ii = addi i 1 in
      let here = get zeta i in
      let acc = set acc ii (get here (get acc i)) in
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
    let numStates = length predecessors in
    let chi1 =
      create
        numStates
        (lam state.
          probMul (get initProbs state) (get (get outputProb state) x)) in
    let r = parallelViterbi_forward predecessors transitionProb outputProb
                                    inputs chi1 in
    match r with {chi = chi, zeta = zeta} then
      let lastState = maxIndexByStateExn chi in
      let logprob = get chi lastState in
      let states = reverse (parallelViterbi_backwardStep lastState (reverse zeta)) in
      {prob = logprob, states = states}
    else never
  else never

mexpr

-- Nonsense calls inserted to prevent the deadcode elimination from removing
-- the called functions.
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
