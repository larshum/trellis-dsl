export LIBRARY_PATH=/usr/local/cuda/lib64
export LD_LIBRARY_PATH=/usr/local/cuda/lib64/
export CPATH=/usr/local/cuda/include
export CFLAGS=-O3 -std=c11

default: viterbi evaluate model.txt signals.txt reference.txt

translate: translate.mc
	mi compile $^

model.txt signals.txt reference.txt: translate
	./translate ../model.txt ../signal.txt ../reference.txt

viterbi: main.c viterbi.c
	gcc -std=c11 -g $^ -lcuda -lcudart -lnvrtc -lm -o $@

viterbi.c viterbi.h: viterbi.fut
	futhark cuda $^ --library

viterbi.fut: parallelviterbi.mc parallelmi
	./parallelmi $< > $@

evaluate: evaluate.cpp
	g++ -std=c++14 -O2 $^ -o $@

parallelmi: parallelmi.mc
	mi compile $^

clean:
	rm -f model.txt signals.txt parallelmi parallelviterbi translate \
			viterbi* evaluate
