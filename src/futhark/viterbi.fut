type ViterbiResult [n] = {prob : f64, states : [n]i64}

let probMul (a : f64) (b : f64) : f64 = a + b

let mapi (f : i64 -> i64 -> f64) (s : []i64) : []f64 =
  let f = (\(x : (i64, i64)) -> f x.0 x.1) in
  let is = tabulate (length s) (\i -> (i, s[i])) in
  map f is

let maxByStateExn (f : i64 -> f64) (s : []i64) : i64 =
  reduce (\x y -> if f x > f y then x else y) (head s) (tail s)

let maxIndexByStateExn (s : []f64) : i64 =
  let is = tabulate (length s) (\i -> (i, s[i])) in
  let h = is[0] in
  let t = is[1:] in
  (reduce (\x y -> if x.1 > y.1 then x else y) h t).0

entry getProb (result : ViterbiResult []) : f64 = result.prob
entry getStates (result : ViterbiResult []) : []i64 = result.states

entry parallelViterbi (predecessors : [][]i64) (transitionProb : [][]f64)
                      (initProbs : []f64) (outputProb : [][]f64) (inputs : []i64)
                      : ViterbiResult [] =
  let x = inputs[0] in
  let inputs = inputs[1:] in
  let numStates = length predecessors in
  let chi1 = tabulate numStates (\state -> probMul initProbs[state] outputProb[state, x]) in

  let forward (chi : []f64) (inputs : []i64) : {chi : []f64, zeta : [][]i64} =
    let n = length inputs in
    let zeta = replicate n (replicate numStates 0i64) in
    loop {chi = chi, zeta = zeta} for i < n do
      let x = inputs[i] in
      let logProbFrom = (\state pre -> probMul chi[pre] transitionProb[pre, state]) in
      let newZeta = tabulate numStates (\state -> maxByStateExn (logProbFrom state) predecessors[state]) in
      let newChi = mapi (\state pre -> probMul (logProbFrom state pre) outputProb[state, x]) newZeta in
      {chi = newChi, zeta = zeta with [i] = newZeta}
  in

  let backwardStep (acc : []i64) (zeta : [][]i64) =
    let n = length zeta in
    let acc = concat acc (replicate n 0i64) in
    loop acc for i < n do
      let here = zeta[i] in
      acc with [i+1] = zeta[i, acc[i]]
  in

  let r = forward chi1 inputs in
  match r case {chi=chi, zeta=zeta} ->
    let lastState = maxIndexByStateExn chi in
    let logprob = chi[lastState] in
    {prob = logprob, states = reverse (backwardStep [lastState] (reverse zeta))}
