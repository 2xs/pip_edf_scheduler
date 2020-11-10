DIGGER=tools/digger/digger
JSONS=EDF.json CNat.json CBool.json CRet.json State.json Primitives.json Jobs.json Entry.json JobSet.json

all: coq_compilation

coq_compilation:
	$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf *~ .*.aux *.crashcoqide
	rm -f EDF.c
	rm -f $(JSONS)

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq src/coq/*/*.v src/coq/*/*/*.v proof/*.v

$(JSONS) &: coq_compilation ;

EDF.c: $(JSONS)
	$(DIGGER) -m Monad -m AbstractTypes -m Datatypes -M coq_RT -d CNat:CNat.json -d CBool:CBool.json -d CRet:CRet.json -d State:State.json -d Primitives:Primitives.json -d Jobs:Jobs.json -d Entry:Entry.json -d JobSet:JobSet.json -o EDF.c EDF.json
#	$(DIGGER) -m Monad -m Datatypes -M coq_RT -m CNat -d CNat:CNat.json -m CBool -d CBool:CBool.json -m CRet -d CRet:CRet.json -m State -d State:State.json -m Primitives -d Primitives:Primitives.json -m Jobs -d Jobs:Jobs.json -m Entry -d Entry:Entry.json -m JobSet -d JobSet:JobSet.json -o $@ $<

_CoqProject: ;

%: Makefile.coq
	+$(MAKE) -f Makefile.coq $@

.PHONY: all coq_compilation clean
