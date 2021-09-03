include "common.mc"
include "seq.mc"

let mapSumOfProducts : [Int] -> [Int] -> [Int] = lam a. lam b.
  map (lam x. foldl addi 0 (map (muli x) b)) a

mexpr

let s1 = create 50000 (lam. randIntU 1 10) in
let s2 = create 50000 (lam. randIntU 1 10) in
let t1 = wallTimeMs () in
let lhs = accelerate (mapSumOfProducts s1 s2) in
let t2 = wallTimeMs () in
let rhs = mapSumOfProducts s1 s2 in
let t3 = wallTimeMs () in
printLn (join ["GPU: ", float2string (divf (subf t2 t1) 1000.0)]);
printLn (join ["CPU: ", float2string (divf (subf t3 t2) 1000.0)]);
if eqSeq eqi lhs rhs then
  printLn "Accelerated code produced the expected result"
else error "results not equal"
