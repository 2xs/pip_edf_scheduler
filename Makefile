
#####################################################################
##                       Directory variables                       ##
#####################################################################

# Sources directory
SRC_DIR=src

# C sources related directories
C_INTERFACE_IMPL_DIR=$(SRC_DIR)/interface_implementation
C_INTERFACE_INCL_DIR=$(C_INTERFACE_IMPL_DIR)/include
C_PARTITION_MOCK_DIR=$(SRC_DIR)/partition

# Coq sources related directories
COQ_SRC_DIR=$(SRC_DIR)/coq
#COQ_MAIN_DIR=$(COQ_SRC_DIR)/main #Not yet used
COQ_MOCKUP_DIR=$(COQ_SRC_DIR)/mockup
COQ_PARTITION_MOCKUP_DIR=$(COQ_MOCKUP_DIR)/partition
COQ_SCHEDULING_MOCKUP_DIR=$(COQ_MOCKUP_DIR)/scheduling
COQ_MODEL_DIR=$(COQ_SRC_DIR)/model
COQ_SCHEDULER_DIR=$(COQ_SRC_DIR)/scheduler
COQ_EXTRACTION_DIR=$(COQ_SRC_DIR)/extraction

# Coq proofs related directories
COQ_PROOF_DIR=proof

# Build directory
BUILD_DIR=build

#####################################################################
##                      Build files variables                      ##
#####################################################################

# Coq source files
COQ_SRC_FILES=$(foreach dir, $(COQ_MAIN_DIR)\
                             $(COQ_MODEL_DIR)\
                             $(COQ_PARTITION_MOCKUP_DIR)\
                             $(COQ_SCHEDULING_MOCKUP_DIR)\
                             $(COQ_SCHEDULER_DIR),\
                   $(wildcard $(dir)/*.v)\
               )
# Coq file needed for extraction
COQ_EXTRACTION_FILES=$(wildcard $(COQ_EXTRACTION_DIR)/*.v)

# Coq prooof files
COQ_PROOF_FILES=$(wildcard $(COQ_PROOF_DIR)/*.v)

# C source files
C_GENERATED_SRC=$(BUILD_DIR)/EDF.c
C_INTERFACE_IMPL_SRC=$(wildcard $(C_INTERFACE_IMPL_DIR)/*.c)
C_PARTITION_MOCK_SRC=$(wildcard $(C_PARTITION_MOCK_DIR)/*.c)

# C header files
C_INTERFACE_IMPL_HEADERS=$(wildcard $(C_INTERFACE_IMPL_DIR)/*.h)

# C object files
C_GENERATED_OBJ=$(C_GENERATED_SRC:.c=.o)
C_INTERFACE_IMPL_OBJ=$(patsubst %.c,$(BUILD_DIR)/%.o, $(notdir $(C_INTERFACE_IMPL_SRC)))
C_PARTITION_MOCK_OBJ=$(patsubst %.c,$(BUILD_DIR)/%.o, $(notdir $(C_PARTITION_MOCK_SRC)))

# Jsons (Coq extracted AST)
JSONS=EDF.json CNat.json CBool.json CRet.json State.json Primitives.json Jobs.json Entry.json JobSet.json
JSONS:=$(patsubst %,$(BUILD_DIR)/%, $(JSONS))

MAKEFLAGS+=-j

#####################################################################
##                         Default target                          ##
#####################################################################

all : proofs $(BUILD_DIR)/partition_mockup

#####################################################################
##                    Code compilation targets                     ##
#####################################################################


DIGGER=tools/digger/digger
CFLAGS+=-Wall -Wextra

# Rely on Makefile.coq to handle dependencies of coq code and
# compile it. Extracts necessary information for generation of C files
coq_code_extraction : Makefile.coq $(BUILD_DIR)
	$(MAKE) --no-print-directory -f Makefile.coq only TGTS="src/coq/extraction/Extraction.vo" -j

# All jsons are generated once Extraction.v is compiled
$(JSONS) &: coq_code_extraction ;

$(BUILD_DIR)/EDF.c: $(JSONS)
	$(DIGGER) -m Monad -m AbstractTypes -m Datatypes -M coq_RT\
		  -d CNat:$(BUILD_DIR)/CNat.json -q CNat.h\
		  -d CBool:$(BUILD_DIR)/CBool.json -q CBool.h\
		  -d CRet:$(BUILD_DIR)/CRet.json -q CRet.h\
		  -d State:$(BUILD_DIR)/State.json -q State.h\
		  -d Primitives:$(BUILD_DIR)/Primitives.json -q Primitives.h\
		  -d Jobs:$(BUILD_DIR)/Jobs.json -q Jobs.h\
		  -d Entry:$(BUILD_DIR)/Entry.json -q Entry.h\
		  -d JobSet:$(BUILD_DIR)/JobSet.json -q JobSet.h\
		  -o $(BUILD_DIR)/EDF.c $(BUILD_DIR)/EDF.json

# Static pattern rule for constructing object files from generated C files
$(C_GENERATED_OBJ): $(BUILD_DIR)/%.o : $(BUILD_DIR)/%.c $(C_INTERFACE_IMPL_HEADERS)
	$(CC) $(CFLAGS) -I $(C_INTERFACE_INCL_DIR) -c -o $@ $<

# Static pattern rule for constructing interface implementation objects files
$(C_INTERFACE_IMPL_OBJ): $(BUILD_DIR)/%.o : $(C_INTERFACE_IMPL_DIR)/%.c $(C_INTERFACE_IMPL_HEADERS)
	$(CC) $(CFLAGS) -I $(C_INTERFACE_INCL_DIR) -c -o $@ $<

#Static pattern rule for constructing partition mockup objects
$(C_PARTITION_MOCK_OBJ): $(BUILD_DIR)/%.o : $(C_PARTITION_MOCK_DIR)/%.c $(C_INTERFACE_IMPL_HEADERS)
	$(CC) $(CFLAGS) -I $(C_INTERFACE_INCL_DIR) -c -o $@ $<

# Rule to create the partition mockup binary
$(BUILD_DIR)/partition_mockup: $(C_GENERATED_OBJ) $(C_INTERFACE_IMPL_OBJ) $(C_PARTITION_MOCK_OBJ)
	$(CC) $(CFLAGS) -o $@ $^

#####################################################################
##                      Proof related targets                      ##
#####################################################################

proofs: Makefile.coq $(BUILD_DIR) $(COQ_SRC_FILES) $(COQ_PROOF_FILES) $(COQ_EXTRACTION_FILES)
	$(MAKE) -f Makefile.coq all

%.vo : Makefile.coq $(BUILD_DIR)
	$(MAKE) --no-print-directory -f Makefile.coq only TGTS="$@" -j

####################################################################
##                        Utility targets                         ##
####################################################################

Makefile.coq: Makefile _CoqProject $(COQ_EXTRACTION_FILES) $(COQ_SRC_FILES) $(COQ_PROOF_FILES)
	coq_makefile -f _CoqProject -o Makefile.coq $(COQ_EXTRACTION_FILES) $(COQ_SRC_FILES) $(COQ_PROOF_FILES)

$(BUILD_DIR):
	mkdir -p $@

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf *~ .*.aux *.crashcoqide
	rm -rf $(BUILD_DIR)


.PHONY: all coq_code_extraction proofs clean
