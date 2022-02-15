# Formally Verified EDF scheduler

This repository holds the code and proofs of a formally verified, userland, job-based, earliest deadline first scheduler running on top of the Pip kernel.  You can find more about the Pip protokernel at its [website](http://pip.univ-lille1.fr).
This scheduler features a formally proven election function written in Gallina (the specification language of the Coq Proof Assistant).

The repository also hold sources for a program (back-end) that acts as a simulation of the scheduler, that prints relevant information regarding the internal state of the election function.

The source code is covered by CeCILL-A licence.

## VM based installation/execution

The easiest way to run the scheduler is to download and run the provided virtual machine image. It includes the Pip kernel sources, the scheduler sources, has the environment set up so that you can build and execute both the kernel and the scheduler. The image also contains useful programming tools (firefox, VSCode, CoqIDE) so that you can tinker with the sources.

The virtual machine is also able to compile and run the simulation of our scheduler, if you are more interested in seeing a detailed trace and having insight on how the scheduler works.

If you would rather go through the painful process of setting up the compilation toolchain yourself, please see the environment set up section. Please note that the execution of the kernel along with its scheduler will still happen on a virtual machine, although the compilation process will not.

### How to run the simulation of the scheduler

Once the VM has booted, start a terminal and `cd` to this repository.
```
$ cd ~/pip/pipcore/src/arch/x86_multiboot/partitions/pip-edf-scheduler
```

Compile the simulation by simply running :
```
$ make build/partition_mockup
```

Then just run the produced binary :
```
$ build/partition_mockup
```

It outputs - for each time slot - the internal state of the scheduler and should help you understand how the scheduler works, and stops after the 4th job completed its execution.

### How to run the scheduler on the Pip kernel

Once the VM has booted, start a terminal and `cd` to Pip's repository.
```
$ cd ~/pip/pipcore/
```

Compile the kernel, which will also trigger the scheduler's compilation :
```
$ make
```

Then, run the produced kernel's elf through Qemu :
```
$ make qemu-elf
```

The kernel will execute until it spends more than 10 time periods idle (i.e. there were no jobs to schedule the last 10 time slots). The scheduler then issues a shutdown request to Qemu, in order to prevent flooding.
The first part of the execution is log from the kernel booting and starting the scheduler. When the execution reaches `The scheduler is booting...`, a second part begins, where the back-end sets up a virtual address space for each task. Once `Scheduler ready ! Now waiting for interrupts...` is reached, the actual interrupt driven scheduling starts, and each elected job outputs its ID. You can see that the output produced by the scheduler matches the one from the simulation.

### Proof verification with Coq

We built our proof using the Coq proof assistant. In order to verify the proofs, you should compile the proof scripts.
We provide a `make` target that allows you to compile all our scripts, simply run :

```sh
$ make proofs
```

Simply compiling the proof scripts isn't very informative, we encourage that you read them. We give more detail about what to expect from the proof scripts in the next section.

## Source inspection
### Project structure

The project is structured as follows :

```
├── ...
├── build
├── proof
│   ├── Assumptions.v
│   ├── EdfPolicy.v
│   ├── FunctionalEdf.v
│   ├── Hoare.v
│   ├── JobsAxioms.v
│   ├── Lib.v
│   ├── MonadicEdf.v
│   └── Refinement.v
├── src
│   ├── coq
│   │   └── ...
│   ├── interface_implementation
│   │   └── ...
│   ├── partition
│   │   └── ...
│   └── partition_mockup
│   │   └── ...
└── tools
    └── digger
```

### Implementation

Under the `src` folder, you will find the sources for both the models and the implementation of various part of the scheduler.
In particular:
* the `src/coq` folder contains the implementation of the verified election function, as well as the entire set of models involved in the final implementation.
* the `src/interface_implementation` folder contains the implementation details common to both back-ends, mostly being the implementation of the interface.
* the `src/partition` folder contains the sources to the actual scheduler back-end running on top of the Pip kernel.
* the `src/partition_mockup` folder contain the sources for the scheduler simulation back-end, that builds as a simple executable binary.

In the `tools` folder lies digger, the tool we use to translate the gallina code into compilable C. If you wish to see the C code of our election function (translated by Digger from the Gallina code), use `make` inside this repository to build the file : 
```sh
$ make build/ElectionFunction.c
```
Then open the file `build/ElectionFunction.c` with your favorite editor.

### Proof scripts

Under the `proof` folder, you will find the properties and proof scripts written for the election function.
In particular :
* `JobsAxiom.v` contains the assumptions on Jobs. These must remain true at any time true otherwise the proof does not hold.
* `Assumptions.v` contains assumptions that hold for the policy. These are transformed into definitions and lemmas once the policy is refined into an algorithm.
* `EdfPolicy.v` contains proofs related to the EDF scheduling policy. It notably contains the schedulability property, as well as the main scheduling policy property proof outlined in section V-B-1.
* `FunctionalEdf.v` contains proofs related to the functional election function algorithm. It notably contains the proof that the functional algorithm implements the policy, as well as the correction property proof as outlined in section V-B-2.
* `MonadicEdf.v` contains proofs related to the monadic election function code that refines the functional algorithm. It notably contains the hoare triple property stating that the output of the monadic code as the same output as the functional algorithm, as well as the correction property proof of the monadic code, as outlined in section V-B-3.
* `Refinement.v` contains proofs on the refinement of the functional algorithm by the monadic code.


## Host based compilation and execution

It seems that you have chosen the hard path. The process should be somewhere between boring and painful depending on how up to date your distribution's packages are.

Please note that even though you will compile the binaries on your own system, the Pip kernel will execute on QEMU.

### Pre-required tools

Before configuring the environment, you should install the following  :
* GNU `make` (at least version 4.3 - tested on version 4.3)
* `gcc`/`ld` for 32 bits intel architectures (any reasonably recent version should work - tested on 11.2.0)
* `nasm` (any reasonably recent version should work - tested on 2.15.05)
* `QEMU` 32 bits Intel emulator (qemu-system-i386 : recommended version 6.2.0, older version installed through the Debian packet manager is known to cause issues)
* The Coq Proof Assistant (at least version 8.15 - tested on version 8.15.0)
* Haskell's `stack` (tested on version 2.7.3)

### Environment set up

First, clone and compile the Pip userland library :
```sh
git clone --depth 1 --branch EDF_scheduler https://github.com/2xs/libpip
make -C libpip
```

First, clone the Pip kernel :
```sh
git clone --depth 1 --branch EDF_scheduler https://github.com/2xs/pipcore
```

Remember the absolute path to both these folders, you will need them later.

Then, `cd` into the `pipcore` folder and clone the scheduler repository inside the relevant folder.
```sh
cd pipcore
git clone --depth 1 --branch EDF_scheduler https://github.com/2xs/pip-edf-scheduler src/arch/x86_multiboot/partitions/pip-edf-scheduler
```

Tell Pip which toolchain you'd like to use. Fill the `<...>` bits with the absolute path to your folders/binaries (if the binaries are in your `PATH`, you may write only the binary name) :
```sh
./configure.sh --architecture=x86 --partition-name=pip-edf-scheduler --libpip=<libpip folder> --c-compiler=<x86 gcc> --linker=<x86 ld> --assembler=<nasm> --coq-compiler=<coqc> --coqdep=<coqdep> --coqdoc=<coqdoc> --qemu=<qemu-system-i386> --no-command-check
```

Now, compile Digger (we recommend you go get a coffee) :
```sh
git submodule init
git submodule update
make -C tools/digger/
```

Once Digger is compiled, `cd` into the scheduler folder :
```sh
cd src/arch/x86_multiboot/partitions/
```
You will now need to edit the locations of the `digger` binary and of the Libpip folder inside the `Makefile`. This is where you will need the absolute path to both the folders from earlier in this guide.
Specifically, edit the DIGGER and LIBPIP variables. You will find them below the `Code compilation targets` banner. They must respectively hold the absolute path to the digger binary (just prepend the absolute path to the pipcore folder) and the absolute path to the folder where you cloned the Libpip earlier :
```
DIGGER=<pipcore folder>/tools/digger/digger
LIBPIP_DIR=<libpip folder>
```

Congratulations, everything is set up ! You may either `make` inside this folder to build the simulation and execute it, or come back to the `pipcore` folder and `make` the whole kernel. Once it is compiled, run `make qemu-elf` to execute the kernel.

## Authors

This partition's development team :
* Florian Vanhems <florian.vanhems@univ-lille.fr>
* Vlad Rusu <vlad.rusu@inria.fr>
* David Nowak <david.nowak@univ-lille.fr>
* Gilles Grimaud <gilles.grimaud@univ-lille.fr>

Userland partition skeleton code and kernel services call library last updated by Damien Amara <damien.amara.etu@univ-lille.fr> during its internship in the 2XS team.
Userland coq code compilation proof of concept written by David Redon <david.redon.etu@univ-lille.fr> during its internship in the 2XS team.
