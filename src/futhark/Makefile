default: parallelviterbi evaluate

parallelviterbi: parallelviterbi.mc state.mc parallelmi
	./parallelmi $<

evaluate: evaluate.mc
	mi compile $<

parallelmi: parallelmi.mc
	mi compile $<

clean:
	rm -f parallelmi parallelviterbi evaluate
