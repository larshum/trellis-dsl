default: main model.txt reference.txt signal.txt

model.txt reference.txt signal.txt: parse.py
	python3 parse.py --model ../synthetic_dna/model/Params3_true.h5 \
					 --output-model model.txt \
					 --signal ../synthetic_dna/data/signals100_1.fast5 \
					 --output-signal signal.txt \
					 --reference ../synthetic_dna/data/mapped_reads100_1.hdf5 \
					 --output-reference reference.txt

main: main.mc levenshtein.mc viterbi.mc
	mi compile $<

clean:
	rm -f model.txt reference.txt signal.txt main
