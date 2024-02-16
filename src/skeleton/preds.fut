
-- We use the below to check each component of a composite type, to ensure that
-- they all contain valid values. We have to do this when using the bitset
-- encoding, in case a component (excluding the most significant one) is not a
-- power of two, because then we end up with "gaps".
let valid_component (x : i64) (cond : (i64, i64, i64)) : bool =
  (x >> cond.0) & cond.1 < cond.2

let valid_state (x : i64) : bool =
  all (valid_component x) state_conds

let is_predecessor (x : i64) (y : i64) : bool =
  if valid_state x && valid_state y then
    transition_probability {} x y == 0.0
  else
    false

let count_preds (y : i64) : i64 =
  i64.sum (map (\x -> if is_predecessor x y then 1 else 0) (iota nstates))

let find_preds_state (maxpreds : i64) (y : i64) : [maxpreds]i64 =
  let preds = filter (\x -> is_predecessor x y) (iota nstates) in
  let preds =
    if length preds < maxpreds then
      preds ++ replicate (maxpreds - length preds) (-1)
    else preds
  in
  preds[0:maxpreds]

entry find_preds (_ : i64) : [nstates][]i64 =
  let maxpreds = i64.maximum (map count_preds (iota nstates)) in
  map (find_preds_state maxpreds) (iota nstates)
