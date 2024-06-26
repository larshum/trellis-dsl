#!/bin/sh

MODEL_PATH=../../synthetic_dna/model/Params3_true.h5
SIGNAL_PATH=../../synthetic_dna/data/signals100_1.fast5

case $1 in
  build)
    trellis kmer.trellis
    ;;
  run)
    python3 runner.py $MODEL_PATH $SIGNAL_PATH
    ;;
  clean)
    rm -rf *generated* trellis.py __init__.py __pycache__ predecessors.txt
    ;;
  *)
    >&2 echo "Expected argument 'build', 'run' or 'clean'"
    exit 1
    ;;
esac
