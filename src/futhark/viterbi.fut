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
  let h = head is in
  let t = tail is in
  (reduce (\x y -> if x.1 > y.1 then x else y) h t).0

entry parallelViterbi (predecessors : [][]i64) (transitionProb : [][]f64)
                      (initProbs : []f64) (numStates : i64) (outputProb : [][]f64)
                      (inputs : []i64) : ViterbiResult [] =
  let x = head inputs in
  let inputs = tail inputs in
  let chi1 = tabulate numStates (\state -> probMul initProbs[state] (outputProb[state, x])) in

  let forward (chi : []f64) (inputs : []i64) : {chi : []f64, zeta : [][]i64} =
    let zeta = map (\_ -> replicate numStates 0i64) inputs in
    let n = length inputs in
    let (chi, zeta, _) =
      loop (chi, zeta, inputs) = (chi, zeta, inputs) for i < n do
        let x = head inputs in
        let inputs = tail inputs in
        let logProbFrom =
          (\state pre -> probMul chi[pre] transitionProb[pre, state])
        in
        let newZeta = tabulate numStates (\state -> maxByStateExn (logProbFrom state) predecessors[state]) in
        let newChi = mapi (\state pre -> probMul (logProbFrom state pre)
                                                 outputProb[state, x])
                          newZeta in
        (newChi, zeta with [i] = newZeta, inputs)
    in
    {chi = chi, zeta = zeta}
  in
  let backwardStep (acc : []i64) (zeta : [][]i64) : []i64 =
    let lastState = acc[0] in
    let acc = map (\_ -> lastState) zeta in
    let n = length zeta in
    let (acc, _) =
      loop (acc, zeta) for i < n do
        let here = last zeta in
        let zeta = init zeta in
        (acc with [n-i-1] = here[acc[n-i-1]], zeta)
    in
    concat acc [lastState]
  in

  let r = forward chi1 inputs in
  match r case {chi=chi, zeta=zeta} ->
    let lastState = maxIndexByStateExn chi in
    let logprob = chi[lastState] in
    {prob = logprob, states = backwardStep [lastState] zeta}
