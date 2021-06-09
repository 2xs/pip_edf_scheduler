
#####################################################################
##                       Directory variables                       ##
#####################################################################

# Sources directory
SRC_DIR=src

# C sources related directories
C_INTERFACE_IMPL_DIR=$(SRC_DIR)/interface_implementation
C_INTERFACE_INCL_DIR=$(C_INTERFACE_IMPL_DIR)/include
C_PARTITION_MOCK_DIR=$(SRC_DIR)/partition_mockup
C_PARTITION_DIR=$(SRC_DIR)/partition
C_PARTITION_INCL_DIR=$(C_PARTITION_DIR)/include
C_TASK_DIR=$(C_PARTITION_DIR)/task

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

# Common C source files
C_GENERATED_SRC=$(BUILD_DIR)/EDF.c
C_INTERFACE_IMPL_SRC=$(wildcard $(C_INTERFACE_IMPL_DIR)/*.c)

# Common C header files
C_INTERFACE_IMPL_HEADERS=$(wildcard $(C_INTERFACE_INCL_DIR)/*.h)

# Partition mockup exclusive C sources
C_PARTITION_MOCK_SRC=$(wildcard $(C_PARTITION_MOCK_DIR)/*.c)

# Pip partition exclusive C sources
C_PARTITION_SRC=$(wildcard $(C_PARTITION_DIR)/*.c)
C_TASK_SRC=$(wildcard $(C_TASK_DIR)/*.c)

# Pip partition exclusive assembly sources
AS_PARTITION_PIP_SRC=$(wildcard $(C_PARTITION_DIR)/*.s)

# Pip partition exclusive C header files
C_PARTITION_HEADERS=$(wildcard $(C_PARTITION_INCL_DIR)/*.h)

# C object files
# Partition mock objects
C_GENERATED_OBJ=$(C_GENERATED_SRC:.c=.o)
C_INTERFACE_IMPL_OBJ=$(patsubst %.c,$(BUILD_DIR)/%.o, $(notdir $(C_INTERFACE_IMPL_SRC)))
C_PARTITION_MOCK_OBJ=$(patsubst %.c,$(BUILD_DIR)/%.o, $(notdir $(C_PARTITION_MOCK_SRC)))

# Pip partition objects
C_GENERATED_PIP_OBJ=$(patsubst %.c, $(BUILD_DIR)/%-pip32.o, $(notdir $(C_GENERATED_SRC)))
C_INTERFACE_IMPL_PIP_OBJ=$(patsubst %.c,$(BUILD_DIR)/%-pip32.o, $(notdir $(C_INTERFACE_IMPL_SRC)))
C_PARTITION_PIP_OBJ=$(patsubst %.c,$(BUILD_DIR)/%-pip32.o, $(notdir $(C_PARTITION_SRC)))
C_TASK_PIP_OBJ=$(patsubst %.c, $(BUILD_DIR)/%-pip32.o, $(notdir $(C_TASK_SRC)))

# Pip partition assembly object files
AS_PARTITION_PIP_OBJ=$(patsubst %.s,$(BUILD_DIR)/%-pip32.o, $(notdir $(AS_PARTITION_PIP_SRC)))

# Task partition binary
TASK_BIN=$(BUILD_DIR)/task.bin

# Pip partition objects
PIP_OBJ=$(AS_PARTITION_PIP_OBJ) $(C_GENERATED_PIP_OBJ) $(C_INTERFACE_IMPL_PIP_OBJ) $(C_PARTITION_PIP_OBJ)

# Jsons (Coq extracted AST)
JSONS=EDF.json CNat.json CBool.json CRet.json State.json Primitives.json Jobs.json Entry.json JobSet.json
JSONS:=$(patsubst %,$(BUILD_DIR)/%, $(JSONS))

MAKEFLAGS+=-j

#####################################################################
##                         Default target                          ##
#####################################################################

all : proofs pip-edf-scheduler.bin $(BUILD_DIR)/partition_mockup

#####################################################################
##                    Code compilation targets                     ##
#####################################################################

DIGGER=tools/digger/digger
LIBPIP_DIR=src/partition/lib/libpip
LIBPIP_COMMON_INC_DIR=$(LIBPIP_DIR)/include
LIBPIP_ARCH_INC_DIR=$(LIBPIP_DIR)/arch/x86/include
LIBPIP=$(LIBPIP_DIR)/lib/libpip.a

CFLAGS=-Wall -Wextra
PIP_CFLAGS=-m32 --freestanding -nostdlib -no-pie -fno-pic -fno-stack-protector

PIP_LDFLAGS=-m elf_i386

# Rely on Makefile.coq to handle dependencies of coq code and
# compile it. Extracts necessary information for generation of C files
coq_code_extraction : Makefile.coq | $(BUILD_DIR)
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

###################### Partition mockup compilation rules #######################

# Static pattern rule for constructing partition mockup object files from generated C files
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

######################## Pip partition compilation rules ########################

# Static pattern rule for constructing pip partition object files from generated C files
$(C_GENERATED_PIP_OBJ): $(BUILD_DIR)/%-pip32.o : $(BUILD_DIR)/%.c $(C_INTERFACE_IMPL_HEADERS)
	$(CC) $(CFLAGS) $(PIP_CFLAGS) -I $(C_INTERFACE_INCL_DIR) -c -o $@ $<

# Static pattern rule for constructing interface implementation objects files
$(C_INTERFACE_IMPL_PIP_OBJ): $(BUILD_DIR)/%-pip32.o : $(C_INTERFACE_IMPL_DIR)/%.c $(C_INTERFACE_IMPL_HEADERS) 
	$(CC) $(CFLAGS) $(PIP_CFLAGS) -I $(C_INTERFACE_INCL_DIR) -c -o $@ $<

#Static pattern rule for constructing partition objects
$(C_PARTITION_PIP_OBJ): $(BUILD_DIR)/%-pip32.o : $(C_PARTITION_DIR)/%.c $(C_INTERFACE_IMPL_HEADERS) $(C_PARTITION_HEADERS)
	$(CC) $(CFLAGS) $(PIP_CFLAGS) -I $(C_INTERFACE_INCL_DIR) -I $(C_PARTITION_INCL_DIR)\
		                      -I $(LIBPIP_COMMON_INC_DIR) -I $(LIBPIP_ARCH_INC_DIR)\
				      -c -o $@ $<

# Static pattern rule for constructing task partition objects
$(C_TASK_PIP_OBJ): $(BUILD_DIR)/%-pip32.o : $(C_TASK_DIR)/%.c
	$(CC) $(CFLAGS) $(PIP_CFLAGS) -c -o $@ $<

# Static pattern rule for constructing partition assembly objects
$(BUILD_DIR)/task_wrapper-pip32.o: $(TASK_BIN)
$(AS_PARTITION_PIP_OBJ): $(BUILD_DIR)/%-pip32.o : $(C_PARTITION_DIR)/%.s
	$(CC) $(CFLAGS) $(PIP_CFLAGS) -c -o $@ $<

# Rule to build the task binary
$(TASK_BIN): $(C_TASK_DIR)/link.ld $(C_TASK_PIP_OBJ)
	$(LD) $(LDFLAGS) $(PIP_LDFLAGS) -T $< $(C_TASK_PIP_OBJ) -o $@

pip-edf-scheduler.bin: $(C_PARTITION_DIR)/link.ld $(PIP_OBJ) $(LIBPIP)
	$(LD) $(LDFLAGS) $(PIP_LDFLAGS) -L $(dir $(LIBPIP)) $(PIP_OBJ) -T $< -o $@ -lpip

#####################################################################
##                      Proof related targets                      ##
#####################################################################

proofs: Makefile.coq $(COQ_SRC_FILES) $(COQ_PROOF_FILES) $(COQ_EXTRACTION_FILES)\
      | $(BUILD_DIR)
	$(MAKE) -f Makefile.coq all

%.vo : Makefile.coq | $(BUILD_DIR)
	$(MAKE) --no-print-directory -f Makefile.coq only TGTS="$@" -j

####################################################################
##                        Utility targets                         ##
####################################################################

Makefile.coq: Makefile _CoqProject $(COQ_EXTRACTION_FILES) $(COQ_SRC_FILES) $(COQ_PROOF_FILES)
	coq_makefile -f _CoqProject -o Makefile.coq $(COQ_EXTRACTION_FILES) $(COQ_SRC_FILES) $(COQ_PROOF_FILES)

# Targets that are built in $(BUILD_DIR) have an order-only dependency to it
$(JSONS) $(C_GENERATED_SRC) $(C_GENERATED_OBJ) $(C_INTERFACE_IMPL_OBJ)\
$(C_PARTITION_MOCK_OBJ) $(BUILD_DIR)/partition_mockup $(C_GENERATED_PIP_OBJ)\
$(C_INTERFACE_IMPL_PIP_OBJ) $(C_PARTITION_PIP_OBJ) $(C_TASK_PIP_OBJ)\
$(AS_PARTITION_PIP_OBJ) $(TASK_BIN): | $(BUILD_DIR)

$(BUILD_DIR):
	mkdir -p $@

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf *~ .*.aux *.crashcoqide pip-edf-scheduler.bin
	rm -rf $(BUILD_DIR)

.PHONY: all coq_code_extraction proofs clean
