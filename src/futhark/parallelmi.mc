include "futhark/generate.mc"
include "futhark/pprint.mc"
include "futhark/record-inline.mc"
include "mexpr/boot-parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"
include "mexpr/utesttrans.mc"
include "mexpr/rewrite/rules.mc"
include "mexpr/rewrite/parallel-keywords.mc"
include "mexpr/rewrite/parallel-rewrite.mc"
include "mexpr/rewrite/tailrecursion.mc"

lang PMExprCompile =
  BootParser +
  MExprSym + MExprTypeAnnot + MExprUtestTrans + MExprParallelKeywordMaker +
  MExprANF + MExprRewrite + MExprTailRecursion + MExprParallelPattern +
  FutharkRecordInline + FutharkGenerate
end

let parallelKeywords = [
  "parallelMap",
  "parallelMap2",
  "parallelReduce",
  "parallelScan",
  "parallelFilter",
  "parallelPartition",
  "parallelAll",
  "parallelAny",
  "flatten",
  "indices"
]

let keywordsSymEnv =
  {symEnvEmpty with varEnv =
    mapFromSeq
      cmpString
      (map (lam s. (s, nameSym s)) parallelKeywords)}

let parallelPatterns = [
  getMapPattern (),
  getMap2Pattern (),
  getReducePattern (),
  getForPattern ()
]

let mergeWithKeywordsSymEnv : SymEnv -> SymEnv = lam symEnv.
  {symEnv with varEnv = mapUnion symEnv.varEnv keywordsSymEnv.varEnv}

let printMExprAst : Expr -> Unit = lam ast.
  use MExprPrettyPrint in
  printLn (expr2str ast)

let printFutharkAst : FutProg -> Unit = lam ast.
  use FutharkPrettyPrint in
  printLn (expr2str ast)

let patternTransformation : Expr -> Expr = lam ast.
  use PMExprCompile in
  let ast = rewriteTerm ast in
  let ast = tailRecursive ast in
  let ast = normalizeTerm ast in
  parallelPatternRewrite parallelPatterns ast

let futharkTranslation : Expr -> FutProg = lam ast.
  use PMExprCompile in
  let ast = inlineRecords ast in
  generateProgram ast

let compile : String -> Unit = lam file.
  use PMExprCompile in
  let ast = parseMCoreFile parallelKeywords file in
  let ast = symbolizeExpr keywordsSymEnv ast in
  let ast = typeAnnot ast in
  let ast = makeKeywords [] ast in
  let ast = utestStrip ast in
  let ast = patternTransformation ast in
  let futharkAst = futharkTranslation ast in
  printFutharkAst futharkAst

mexpr

if geqi (length argv) 2 then
  let file = get argv 1 in
  compile file
else
  printLn (join ["Usage: '", get argv 0, " <file>'"]);
  exit 1
