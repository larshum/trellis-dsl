default: parallelviterbi evaluate

parallelviterbi: parallelviterbi.mc parallelmi
	./parallelmi $<

evaluate: evaluate.cpp
	g++ -std=c++14 -O2 $^ -o $@

parallelmi: parallelmi.mc
	mi compile $^

clean:
	rm -f parallelmi parallelviterbi evaluate
