default: parallelviterbi evaluate

parallelviterbi: parallelviterbi.mc state.mc
	mi accelerate $<

evaluate: evaluate.mc
	mi compile $<

clean:
	rm -f parallelmi parallelviterbi evaluate
