include  ../toolchain.mk

SRC_DIR=src
COQ_DIR=$(SRC_DIR)/coq
ASM_DIR=$(SRC_DIR)/asm
BUILD_DIR=build

COQDEP=coqdep -c
COQC=coqc -q

SED=sed

CFLAGS=-m32 -c
CFLAGS+=-nostdlib  --freestanding
CFLAGS+=-I$(LIBPIP)/include/
CFLAGS+=-I$(LIBPIP)/arch/x86/include/
CFLAGS+=-fno-stack-protector -fno-pic -no-pie
CFLAGS+=-I$(SRC_DIR)/include/

ASFLAGS=$(CFLAGS)

LDFLAGS=-L$(LIBPIP)/lib -melf_i386  -Tlink.ld
LDFLAGS+=-lpip

COQOPTS= -Q proof Proof
COQOPTS+=-Q $(COQ_DIR)/model Model
COQOPTS+=-Q $(COQ_DIR)/main Main

ASSOURCES=$(wildcard $(ASM_DIR)/*.s)
CSOURCES=$(BUILD_DIR)/main.c
VSOURCES=$(foreach dir, $(COQ_DIR)/main $(COQ_DIR)/model proof, $(wildcard $(dir)/*.v))

ASOBJ=$(ASSOURCES:.s=.o)
COBJ=$(CSOURCES:.c=.o)
VOBJ=$(VSOURCES:.v=.vo)

COBJ:=$(patsubst %,$(BUILD_DIR)/%, $(notdir $(COBJ)))
ASOBJ:=$(patsubst %,$(BUILD_DIR)/%, $(notdir $(ASOBJ)))

EXEC=gallina_hello_world.bin

all: $(EXEC)
	@echo  Done.

clean: clean-coq clean-c

clean-coq:
	rm -f *.json
	rm -f $(VOBJ) $(VSOURCES:.v=.v.d) $(VSOURCES:.v=.glob)

clean-c:
	rm -rf $(ASOBJ) $(COBJ) $(EXEC) *.dep $(BUILD_DIR)

$(EXEC): $(BUILD_DIR) $(ASOBJ) $(COBJ)
	$(LD) $(ASOBJ) $(COBJ) -o $@ $(LDFLAGS)

proofs: $(VOBJ)

$(BUILD_DIR)/main.c: Main.json
	$(DIGGER) -m Monad -M coq_Ms -R returnM -B bindM                  \
	    -m Datatypes -r Coq_true:true -r Coq_false:false -r Coq_tt:tt \
	    -m String -q base.h -q Monad.h -q Internals.h                 \
	    -m Internals -d :Internals.json                               \
	    --ignore HelloWorld -r coq_HelloWorld:HelloWorld		  \
	    -o $@ $<

-include $(addsuffix .d,$(VSOURCES))

$(addsuffix .d,$(VSOURCES)): %.v.d: %.v
	@$(COQDEP) $(COQOPTS) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

# Generate build directory
$(BUILD_DIR):
	mkdir -p $@

Main.json: $(COQ_DIR)/model/Extraction.vo

%.vo: %.v
	$(COQC) $(COQOPTS) $<

# Use GCC to generate rules, convert multi-lines rules to single lines, remove empty lines and use $(BUILD_DIR) as target
#makefile-bin.dep:
#	$(CC) $(CFLAGS) -MM $(CSOURCES) | perl -pe 's/(\\[\r\n]+)//' | awk 'NF > 0' | $(SED) "s|^|$(BUILD_DIR)/|g" > $@
#include makefile-bin.dep

%.o: %.c
	$(AS) $(ASFLAGS) $< -o $@

$(BUILD_DIR)/%.o: $(ASM_DIR)/%.s
	$(CC) $(CFLAGS) $< -o $@
