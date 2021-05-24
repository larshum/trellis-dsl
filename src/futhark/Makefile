export LIBRARY_PATH=/usr/local/cuda/lib64
export LD_LIBRARY_PATH=/usr/local/cuda/lib64/
export CPATH=/usr/local/cuda/include
export CFLAGS=-O3 -std=c11

viterbi: main.c viterbi.h viterbi.c
	gcc -std=c11 -O3 main.c viterbi.c -lcuda -lcudart -lnvrtc -lm -o $@

viterbi.h: viterbi.fut
	futhark cuda $^ --library
