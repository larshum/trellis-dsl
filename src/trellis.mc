
include "parser/ast.mc"
include "parser/pprint.mc"
include "parser/resolve.mc"
include "model/ast.mc"
include "model/constant-fold.mc"
include "model/convert.mc"
include "model/pprint.mc"
include "model/reduce-tables.mc"
include "model/table-opt.mc"
include "model/validate.mc"
include "constraints/predecessors.mc"
include "./cuda/compile.mc"
include "./cuda/pprint.mc"
include "build.mc"
include "trellis-arg.mc"

lang Trellis =
  TrellisAst + TrellisModelAst + TrellisModelConvert + TrellisConstantFold +
  TrellisReduceTableDimensionality + TrellisModelReplaceNonTrivialBody +
  TrellisModelValidate + TrellisModelPredecessorAnalysis + TrellisCudaCompile +
  TrellisBuild
end

mexpr

use Trellis in

let result = argParse trellisDefaultOptions config in
match result with ParseOK r then
  let options : TrellisOptions = r.options in
  if or options.help (neqi (length r.strings) 1) then
    print (menu ());
    exit 0
  else
    let filename = head r.strings in

    -- Read the "parse" AST, the one generated by the syn tool.
    let p = parseTrellisExn filename (readFile filename) in
    (if options.printParse then
      printLn (use TrellisPrettyPrint in pprintTrellis p)
    else ());

    -- Construct the model AST, which is a simpler representation of the above
    -- AST.
    let modelAst = constructTrellisModelRepresentation p in

    -- Apply constant folding to the model AST to simplify the condition
    -- expressions of the set constraints.
    let modelAst = constantFoldModel modelAst in

    (if options.printModel then
      printLn (use TrellisModelPrettyPrint in pprintTrellisModel modelAst)
    else ());

    -- Simplify the model by reducing the dimension of all tables to one and
    -- transforming the model accordingly.
    let modelAst = reduceTableDimensionalityModel modelAst in

    -- Replaces non-trivial bodies in probability functions that are
    -- independent of the input variables with a new synthetic table. The
    -- result is an environment mapping the name of a synthetic table to the
    -- expression it represents, and the updated model AST containing synthetic
    -- tables.
    match replaceNonTrivialBodiesInProbabilityFunctions modelAst
    with (tableEnv, modelAst) in

    -- Validates the set constraints of the model by ensuring they all describe
    -- non-empty sets and that they are all pairwise disjoint (within each
    -- probability function).
    validateModelSetConstraints modelAst;

    -- Produces an abstract representation of the predecessor constraints
    -- imposed by each case of the transition probability function. The result
    -- is an option; should the cases include conditions of unsupported shape,
    -- the result is None. This step is always skipped and None is returned if
    -- a compiler flag is set.
    let constraints =
      if options.forcePrecomputePredecessors then None ()
      else performPredecessorAnalysis options modelAst
    in

    -- Compiles the provided model with the constraints to CUDA code, using
    -- different approaches depending on whether the predecessor constraints
    -- are supported or not.
    match compileToCuda options tableEnv modelAst constraints with (env, cuProg) in

    -- Produces a simple Python library which performs runtime compilation of
    -- the CUDA code and calls it.
    buildPythonLibrary options tableEnv modelAst cuProg env
else
  argPrintError result;
  exit 1
