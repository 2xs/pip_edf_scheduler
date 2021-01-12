#####################################################################
##                      Proof related targets                      ##
#####################################################################

coq_compilation: Makefile.coq
	$(MAKE) -f Makefile.coq all

#####################################################################
##                    Code compilation targets                     ##
#####################################################################

JSONS=EDF.json CNat.json CBool.json CRet.json State.json Primitives.json Jobs.json Entry.json JobSet.json

DIGGER=tools/digger/digger
INCLUDES=src/interface_implementation/include
CFLAGS+=-Wall -Wextra -I $(INCLUDES)

coq_code_compilation : Makefile.coq
	$(MAKE) only TGTS="src/coq/mockup/Extraction.vo" -j

$(JSONS) &: coq_code_compilation ;

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

EDF.o: EDF.c
	$(CC) $(CFLAGS) -c -o $@ $<

mem_repr.o: src/interface_implementation/mem_repr.c $(INCLUDES)/mem_repr.h
	$(CC) $(CFLAGS) -c -o $@ $<

State.o: src/interface_implementation/State.c $(INCLUDES)/State.h
	$(CC) $(CFLAGS) -c -o $@ $<

partition.o: src/partition/main.c $(INCLUDES)/State.h
	$(CC) $(CFLAGS) -c -o $@ $<

partition: partition.o mem_repr.o State.o EDF.o
	$(CC) $(CFLAGS) -o $@ $^

####################################################################
##                        Utility targets                         ##
####################################################################

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf *~ .*.aux *.crashcoqide
	rm -f EDF.c
	rm -f *.o
	rm -f $(JSONS)
	rm -f partition

####################################################################
##                    Makefile.coq related                        ##
####################################################################

# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := Makefile.coq
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

Makefile.coq: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq src/coq/*/*.v src/coq/*/*/*.v proof/*.v

invoke-coqmakefile: Makefile.coq
	$(MAKE) --no-print-directory -f Makefile.coq $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))
# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true

.PHONY: all coq_code_compilation invoke-coqmakefile clean $(KNOWNFILES)
