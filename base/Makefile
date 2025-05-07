COQ_MAKEFILE=coq_makefile

theory: CoqMakefile
	make -f CoqMakefile
.PHONY: theory

clean: CoqMakefile
	make -f CoqMakefile clean
	rm CoqMakefile CoqMakefile.conf
.PHONY: clean

CoqMakefile:
	$(COQ_MAKEFILE) -f _CoqProject -o CoqMakefile
