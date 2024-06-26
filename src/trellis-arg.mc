include "arg.mc"
include "set.mc"
include "string.mc"

let defaultStr = lam defaultOptStr. lam msg.
  join [msg, " (default: ", defaultOptStr, ")"]

type TrellisOptions = {
  batchSize : Int,
  batchOverlap : Int,
  useDoublePrecisionFloats : Bool,
  forcePrecomputeTables : Bool,
  skipPredecessors : Bool,
  maxpreds : Int,
  printParse : Bool,
  printModel : Bool,
  printTransformedModel : Bool,
  outputDir : String,
  futharkTarget : String
}

let trellisDefaultOptions = {
  batchSize = 1024,
  batchOverlap = 128,
  useDoublePrecisionFloats = false,
  forcePrecomputeTables = false,
  skipPredecessors = false,
  maxpreds = negi 1,
  printParse = false,
  printModel = false,
  printTransformedModel = false,
  outputDir = ".",
  futharkTarget = "multicore"
}

let _supportedFutharkTargets = setOfSeq cmpString [
  "c", "multicore", "cuda", "opencl"
]
let validateFutharkTarget = lam target.
  if setMem target _supportedFutharkTargets then target
  else
    let msg = join [
      "Futhark target '", target, "' is not supported\n",
      "Supported Futhark targets: ", strJoin " " (setToSeq _supportedFutharkTargets)
    ] in
    error msg

let config = [
  ([("--batch-size", " ", "<n>")],
    defaultStr (int2string trellisDefaultOptions.batchSize)
      "Manually sets the size of each batch of input values processed in Viterbi.",
    lam p.
      let o = p.options in {o with batchSize = argToIntMin p 0}),
  ([("--batch-overlap", " ", "<n>")],
    defaultStr (int2string trellisDefaultOptions.batchOverlap)
      "Manually sets the overlap to use between consecutive batches in Viterbi.",
    lam p.
      let o = p.options in {o with batchOverlap = argToIntMin p 0}),
  ([("--use-double-precision", "", "")],
    defaultStr (bool2string trellisDefaultOptions.useDoublePrecisionFloats)
      "Use double-precision floating point numbers.",
    lam p.
      let o = p.options in {o with useDoublePrecisionFloats = true}),
  ([("--precompute-tables", "", "")],
    defaultStr (bool2string trellisDefaultOptions.forcePrecomputeTables)
      "Pre-computes all probability tables when constructing the model. This improves execution time but increases memory usage.",
    lam p.
      let o = p.options in {o with forcePrecomputeTables = true}),
  ([("--skip-predecessors", "", "")],
    defaultStr (bool2string trellisDefaultOptions.skipPredecessors)
      "Makes the compiler skip the predecessor computation part, to speed up compilation. Requires using the maxpreds argument to specify the maximum number of predecessors manually.",
    lam p.
      let o = p.options in {o with skipPredecessors = true}),
  ([("--maxpreds", " ", "<n>")],
    defaultStr (int2string trellisDefaultOptions.maxpreds)
      "Specifies the maximum number of predecessors of any node. Should be used with the --skip-predecessors flag.",
    lam p.
      let o = p.options in {o with maxpreds = argToInt p}),
  ([("--print-parse", "", "")],
    "Pretty-prints the initial AST after parsing.",
    lam p.
      let o = p.options in {o with printParse = true}),
  ([("--print-model", "", "")],
    "Pretty-prints the model AST after pre-processing the parsed AST.",
    lam p.
      let o = p.options in {o with printModel = true}),
  ([("--print-transformed-model", "", "")],
    "Pretty-prints the transformed model AST before generating code..",
    lam p.
      let o = p.options in {o with printTransformedModel = true}),
  ([("--output-dir", " ", "<dir>")],
    defaultStr trellisDefaultOptions.outputDir
      "Specifies the name of a directory in which files should be placed.",
    lam p.
      let o = p.options in {o with outputDir = argToString p}),
  ([("--futhark-target", " ", "<target>")],
    defaultStr trellisDefaultOptions.futharkTarget
      "Specifies the target backend to use when compiling Futhark.",
    lam p.
      let o = p.options in {o with futharkTarget = validateFutharkTarget (argToString p)})
]

let menu = lam. join [
  "Usage: trellis [<options>] file.trellis\n\n",
  "Options:\n",
  argHelpOptions config,
  "\n"
]
