include "common.mc"
include "string.mc"
include "../levenshtein.mc"

let readInput : String -> [(String, String)] = lam filename.
  recursive let work : [(String, String)] -> [String] -> [(String, String)] =
    lam acc. lam linesLeft.
    match linesLeft with [h1, h2] ++ t then
      work (snoc acc (h1, h2)) t
    else match linesLeft with [h] then
      error "Expected an even number of lines"
    else acc
  in
  let lines = strSplit "\n" (strTrim (readFile filename)) in
  work [] lines

let compareStrings : String -> String -> Float = lam s1. lam s2.
  let dist = levenshtein s1 s2 in
  subf 1.0 (divf (int2float dist) (int2float (length s1)))

mexpr

let reference : [(String, String)] = readInput (get argv 1) in
let output : [(String, String)] = readInput (get argv 2) in

map
  (lam p : ((String, String), (String, String)).
    let ref = p.0 in
    let out = p.1 in
    if eqString ref.0 out.0 then
      printLn (join [ref.0, ": ", float2string (compareStrings ref.1 out.1)])
    else error "Output mismatch")
  (zip reference output)
