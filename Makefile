DIGGER=/home/debilausaure/Documents/pip/glue/tools/digger/digger

all: coq_compilation
	
coq_compilation : Makefile.coq
	+$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	+$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf *~ .*.aux *.crashcoqide
	rm -f EDF.c
	rm -f *.json

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq src/coq/*/*.v src/coq/*/*/*.v proof/*.v

%: Makefile.coq
	+$(MAKE) -f Makefile.coq $@

EDF.json: coq_compilation

EDF.c: EDF.json
	$(DIGGER) -m Monad -m Datatypes -M coq_RT -o $@ $^
#	$(DIGGER) -m Monad -m Datatypes -M coq_RT -d CNat:CNat.json -d ...  -o $@ $^ 
.PHONY: all coq_compilation clean
