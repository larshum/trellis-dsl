
include "parser/ast.mc"
include "parser/pprint.mc"
include "parser/resolve.mc"
include "model/ast.mc"
include "model/compile.mc"
include "model/convert.mc"
include "model/encode.mc"
include "model/pprint.mc"
include "model/viterbi.mc"
include "build.mc"
include "trellis-arg.mc"

lang Trellis =
  TrellisAst + TrellisModelAst + TrellisModelConvert + TrellisCompileModel +
  TrellisEncode + TrellisGenerateViterbiEntry + TrellisGenerateViterbiProgram +
  TrellisBuild
end

mexpr

use Trellis in

-- Parse command-line arguments
let result = argParse trellisDefaultOptions config in
match result with ParseOK r then
  let options : TrellisOptions = r.options in
  -- Exactly one file as argument?
  if neqi (length r.strings) 1 then
    -- No, print the menu and exit
    print (menu ());
    exit 0
  else
    -- Yes, read and parse the file
    let filename = head r.strings in

    -- Read the "parse" AST, the one generated by the syn tool.
    let p = parseTrellisExn filename (readFile filename) in
    (if options.printParse then
      printLn (use TrellisPrettyPrint in pprintTrellis p)
    else ());

    -- Construct the model AST, which is a simpler representation of the above
    -- AST.
    let modelAst = constructTrellisModelRepresentation p in
    (if options.printModel then
      printLn (use TrellisModelPrettyPrint in pprintTrellisModel modelAst)
    else ());

    -- Encodes state types as integers when in table accesses.
    let modelAst = encodeStateOperations options modelAst in

    -- Compile the Trellis model to Futhark, resulting in initializer code,
    -- definitions of the initial, output, and transition probabilities, as
    -- well and the compilation environment (to use later).
    let fut = compileTrellisModel options modelAst in

    -- Generate a complete Futhark program by gluing together parts from the
    -- compilation results with a pre-defined Viterbi implementation (found
    -- under "src/skeleton").
    let prog = generateViterbiProgram fut in

    buildPythonWrapper fut.env prog;
    printLn (concat "Wrote output code to " options.outputDir)
else
  argPrintError result;
  exit 1