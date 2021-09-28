include "math.mc"
include "../parse.mc"

type State = {
  kmer : [a],
  layer : Int
}

let bases = "ACGT"
let nbases = length bases

let baseToIndex : Char -> Int = lam base.
  match base with 'A' then 0
  else match base with 'C' then 1
  else match base with 'G' then 2
  else match base with 'T' then 3
  else error (join ["Invalid base character: ", [base]])

utest baseToIndex 'A' with 0
utest baseToIndex 'C' with 1
utest baseToIndex 'G' with 2
utest baseToIndex 'T' with 3

let indexToBase : Int -> Char = lam index.
  match index with 0 then 'A'
  else match index with 1 then 'C'
  else match index with 2 then 'G'
  else match index with 3 then 'T'
  else error (join ["Invalid base index: ", int2string index])

utest indexToBase 0 with 'A'
utest indexToBase 1 with 'C'
utest indexToBase 2 with 'G'
utest indexToBase 3 with 'T'

let powf = lam b : Float. lam e : Int.
  foldl mulf 1.0 (create e (lam. b))

utest powf 2.0 4 with 16.0 using eqfApprox 1e-6
utest powf 2.5 2 with 6.25 using eqfApprox 1e-6
utest powf 1.0 100 with 1.0 using eqfApprox 1e-6

let statesPerLayer : ViterbiParams -> Int = lam model.
  floorfi (powf (int2float nbases) model.k)

let stateToIndex : ViterbiParams -> State -> Int = lam model. lam s.
  let layerIndex = muli s.layer (statesPerLayer model) in
  let stateIndex =
    foldl
      addi
      0
      (mapi
        (lam i. lam k.
          let factor = floorfi (powf (int2float nbases) i) in
          muli (baseToIndex k) factor)
        s.kmer)
  in
  addi layerIndex stateIndex

let indexToState : ViterbiParams -> Int -> State = lam model. lam i.
  let layer = divi i (statesPerLayer model) in
  let kmerIndex = modi i (statesPerLayer model) in
  let nbases = length bases in
  recursive let work = lam acc. lam kmerIndex. lam k.
    if eqi k 0 then acc
    else
      let nextBase = indexToBase (modi kmerIndex nbases) in
      work (snoc acc nextBase) (divi kmerIndex nbases) (subi k 1) 
  in
  {kmer = work [] kmerIndex model.k, layer = layer}

let stateSpace : ViterbiParams -> [State] = lam model.
  -- Finds all possible states within one layer
  recursive let work = lam n.
    if eqi n 0 then [[]]
    else
      let recTails = work (subi n 1) in
      join (map (lam tail. map (lam letter. cons letter tail) bases) recTails)
  in
  let kmers = work model.k in
  -- Replicates the states produced above for each possible layer
  recursive let work2 = lam n.
    if eqi n 0 then []
    else
      let layer = subi n 1 in
      let states = map (lam kmer. {kmer = kmer, layer = layer}) kmers in
      concat states (work2 layer)
  in
  work2 model.dMax

let cmpState : ViterbiParams -> State -> State -> Int =
  lam model. lam s1. lam s2.
  subi (stateToIndex model s1) (stateToIndex model s2)

let eqState : ViterbiParams -> State -> State -> Bool =
  lam model. lam s1. lam s2.
  eqi (cmpState model s1 s2) 0

let pred : ViterbiParams -> State -> [State] = lam model. lam s.
  let layer0 = {s with layer = 0} in
  concat
    (map (lam i. {layer0 with kmer = cons i (init s.kmer)}) bases)
    (if eqi s.layer (subi model.dMax 1) then
      [{s with layer = s.layer}]
    else
      [{s with layer = addi s.layer 1}])

let printState : State -> String = lam s.
  join ["{kmer=", s.kmer, ", layer=", int2string s.layer, "}"]

let printStateData : [State] -> String = lam states.
  let layerCount : Map Int Int =
    foldl
      (lam lc. lam s : State. mapInsertWith addi s.layer 1 lc)
      (mapEmpty subi)
      states
  in
  let firstLayerStates = filter (lam s : State. eqi s.layer 0) states in
  map (lam s : State. last s.kmer) firstLayerStates

mexpr

let model = {
  signalLevels = 2,
  observationProbabilities = [[], []],
  transitionProbabilities = [],
  duration = [],
  k = 2,
  dMax = 2,
  tailFactor = 1.0,
  tailFactorComp = 0.0
} in

utest statesPerLayer model with 16 in

let s1 = {kmer = "AA", layer = 0} in
let s2 = {kmer = "AA", layer = 1} in
let s3 = {kmer = "TG", layer = 1} in
let s4 = {kmer = "CG", layer = 0} in
let s5 = {kmer = "CT", layer = 1} in

utest stateToIndex model s1 with 0 in
utest stateToIndex model s2 with 16 in
utest stateToIndex model s3 with 27 in
utest stateToIndex model {s3 with layer = 0} with 11 in
utest stateToIndex model s4 with 9 in
utest stateToIndex model {s4 with layer = 1} with 25 in
utest stateToIndex model s5 with 29 in
utest stateToIndex model {s5 with layer = 0} with 13 in

utest indexToState model 0 with s1 using eqState model in
utest indexToState model 16 with s2 using eqState model in
utest indexToState model 27 with s3 using eqState model in
utest indexToState model 9 with s4 using eqState model in
utest indexToState model 29 with s5 using eqState model in

let ss = stateSpace model in
utest length ss with 32 in

let predecessorsS1 = [
  {s1 with kmer = "AA"}, {s1 with kmer = "CA"}, {s1 with kmer = "GA"},
  {s1 with kmer = "TA"}, {s1 with layer = 1}] in
utest pred model s1 with predecessorsS1 using eqSeq (eqState model) in

()
