include "futhark/generate.mc"
include "futhark/pprint.mc"
include "mexpr/boot-parser.mc"
include "mexpr/patterns.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"
include "mexpr/utesttrans.mc"
include "mexpr/rewrite/rules.mc"
include "mexpr/rewrite/parallel-patterns.mc"
include "mexpr/rewrite/tailrecursion.mc"

lang PMExprCompile =
  BootParser +
  MExprSym + MExprTypeAnnot + MExprUtestTrans + MExprParallelKeywordMaker +
  MExprRewrite + MExprTailRecursion + MExprParallelPatterns +
  FutharkGenerate
end

let parallelKeywords = [
  "parallelMap",
  "parallelMap2",
  "parallelReduce",
  "parallelScan",
  "parallelFilter",
  "parallelPartition",
  "parallelAll",
  "parallelAny"
]

let keywordsSymEnv =
  {symEnvEmpty with varEnv =
    mapFromSeq
      cmpString
      (map (lam s. (s, nameSym s)) parallelKeywords)}

let mergeWithKeywordsSymEnv = lam symEnv : SymEnv.
  {symEnv with varEnv = mapUnion symEnv.varEnv keywordsSymEnv.varEnv}

let printMExprAst = lam ast : Expr.
  use MExprPrettyPrint in
  printLn (expr2str ast)

let printFutharkAst = lam ast : FutProg.
  use FutharkPrettyPrint in
  printLn (expr2str ast)

let patternTransformation = lam ast : Expr.
  use PMExprCompile in
  let ast = rewriteTerm ast in
  let ast = tailRecursive ast in
  insertParallelPatterns ast

let compile = lam file.
  use PMExprCompile in
  let ast = parseMCoreFile parallelKeywords file in
  let ast = symbolizeExpr keywordsSymEnv ast in
  let ast = typeAnnot ast in
  let ast = makeKeywords [] ast in
  let ast = utestStrip ast in
  let ast = patternTransformation ast in
  let futharkAst = generateProgram ast in
  printFutharkAst futharkAst

mexpr

if geqi (length argv) 2 then
  let file = get argv 1 in
  compile file
else
  printLn (join ["Usage: '", get argv 0, " <file>'"]);
  exit 1
