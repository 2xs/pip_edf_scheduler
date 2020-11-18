DIGGER=tools/digger/digger
JSONS=EDF.json CNat.json CBool.json CRet.json State.json Primitives.json Jobs.json Entry.json JobSet.json

INCLUDES=src/include

CFLAGS+=-Wall -Wextra -I $(INCLUDES)

all: coq_compilation

coq_compilation:
	$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf *~ .*.aux *.crashcoqide
	rm -f EDF.c
	rm -f *.o
	rm -f $(JSONS)

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq src/coq/*/*.v src/coq/*/*/*.v proof/*.v

$(JSONS) &: coq_compilation ;

EDF.c: $(JSONS)
	$(DIGGER) -m Monad -m AbstractTypes -m Datatypes -M coq_RT\
		  -d CNat:CNat.json -q CNat.h\
		  -d CBool:CBool.json -q CBool.h\
		  -d CRet:CRet.json -q CRet.h\
		  -d State:State.json -q State.h\
		  -d Primitives:Primitives.json -q Primitives.h\
		  -d Jobs:Jobs.json -q Jobs.h\
		  -d Entry:Entry.json -q Entry.h\
		  -d JobSet:JobSet.json -q JobSet.h\
		  -o EDF.c EDF.json

Jobs.o: src/c/Jobs.c $(INCLUDES)/Jobs.h
	$(CC) $(CFLAGS) -c -o $@ $<

EDF.o: EDF.c $(INCLUDES)/Jobs.h $(INCLUDES)/Entry.h
	$(CC) $(CFLAGS) -c -o $@ $<

_CoqProject: ;

%: Makefile.coq
	+$(MAKE) -f Makefile.coq $@

.PHONY: all coq_compilation clean
