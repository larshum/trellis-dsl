export LIBRARY_PATH=/usr/local/cuda/lib64
export LD_LIBRARY_PATH=/usr/local/cuda/lib64/
export CPATH=/usr/local/cuda/include
export CFLAGS=-O3 -std=c11

default: viterbi parallelviterbi model.txt signals.txt

parallelviterbi: parallelviterbi.mc parallelmi
	./parallelmi $<

parallelmi: parallelmi.mc
	mi compile $^

translate: translate.mc
	mi compile $^

model.txt signals.txt: translate
	./translate ../model.txt ../signal.txt

viterbi: main.c viterbi.h viterbi.c
	gcc -std=c11 -O3 main.c viterbi.c -lcuda -lcudart -lnvrtc -lm -o $@

viterbi.c viterbi.h: viterbi.fut
	futhark cuda $^ --library

clean:
	rm -f model.txt signals.txt parallelmi parallelviterbi translate viterbi \
	      viterbi.c viterbi.h
