COQMF = coq_makefile -f _CoqProject -o Makefile.coq
all: Makefile.coq
	$(MAKE) -f Makefile.coq
clean:
	@if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; rm -f Makefile.coq; fi
Makefile.coq: _CoqProject
	$(COQMF)
.PHONY: all clean
