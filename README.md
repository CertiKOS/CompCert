# CompCertO with State Composition and Encapsulation

## Setup

You will need a version of Coq and various other tools supported by
CompCert v3.6. If you are using `opam` (recommended),

    $ opam init
    $ opam install coq.8.12.0 menhir.20200211

You first need to build the prerequisite Coqrel by:

    $ (cd coqrel && ./configure && make)

Then you can build the CompCertO compiler with the development for the state composition and encapsulation, and the proof for the running example in our paper by:

    $ ./configure x86_64-linux
    $ make

## Formalization

Our constructions are mainly in the `clightp/` directory

* The formalization to equip the CompCertO with a notion of compositional state and a structure of double category. CategoricalComp.v defines the layered composition in the paper, and TensorComp.v and FlatComp.v defines two styles of horizontal composition that are used in Certified Abstraction Layers:
```
  clightp/Lifting.v
  clightp/TensorComp.v
  common/CategoricalComp.v
  common/FlatComp.v
```

* The development for Certified Abstraction Layers:
```
  clightp/AbRel.v
  clightp/CModule.v
  clightp/SkelLinking.v
  clightp/Composition.v
```

* The development for memory separation
```
  cklr/Join.v
```

* The development for state encapsulation
```
  clightp/Encapsulation.v
```

* The development for ClightP semantics and composition
```
  clightp/PEnv.v
  clightp/ClightP.v
  clightp/ClightPComp.v
  clightp/ClightPLink.v
```

* The ring buffer and bounded queue example using ClightP and encapsulation
```
  clightp/Example.v
```

* The rot13 example with loaders verified using only C program
```
  process/With.v
  process/Pipe.v
  process/InitMem.v
  process/Pipe.v
  process/CAsm.v
  process/Process.v
```

* The following file additionally provide a proof of for the secret module 
  written in assembly and can be plugged into the rot13 example above
```
  process/Secret.v
```


---

Original README.md from CompCertO below

# CompCertO

A version of CompCert featuring an open module semantics, designed to
target the framework of *refinement-based game semantics*.

## Overview

This is a modified version of CompCert v3.6. The language semantics
and correctness proofs have been updated to describe the behavior of
individual compilation units. Most passes from Clight to Asm have
been update, for the x86 architecture.

## Building

Since our compiler uses Clight as the source language, the first few
passes are not available and the full extracted compiler cannot be
built. However the Coq version of the Clight to Asm compiler can be
compiled in the following way.

### Requirements

Build requirements are identical to those of CompCert v3.6. We recommend
using the `opam` package manager to set up a build environment. We have
tested CompCertO on Linux with the following `opam` installation:

    % opam list
    # Packages matching: installed
    # Name          # Installed # Synopsis
    base-bigarray   base
    base-threads    base
    base-unix       base
    camlp5          7.14        Preprocessor-pretty-printer of OCaml
    conf-findutils  1           Virtual package relying on findutils
    conf-m4         1           Virtual package relying on m4
    conf-perl       1           Virtual package relying on perl
    conf-pkg-config 1.3         Virtual package relying on pkg-config installation
    coq             8.9.1       pinned to version 8.9.1
    coq-coq2html    1.2         Generates HTML documentation from Coq source files.  Alternative to coqdoc
    dune            2.8.2       Fast, portable, and opinionated build system
    menhir          20201216    An LR(1) parser generator
    menhirLib       20201216    Runtime support library for parsers generated by Menhir
    menhirSdk       20201216    Compile-time library for auxiliary tools related to Menhir
    num             1.4         The legacy Num library for arbitrary-precision integer and rational arithmetic
    ocaml           4.08.1      The OCaml compiler (virtual package)
    ocaml-config    1           OCaml Switch Configuration
    ocaml-system    4.08.1      The OCaml compiler (system version, from outside of opam)
    ocamlfind       1.8.1       A library manager for OCaml

You should be able to reproduce this installation with the following
sequence of shell commands:

    # Initialize opam (if you haven't used it before)
    opam init --bare

    # Create an "opam switch" dedicated to building CompCertO
    opam switch create compcerto ocaml-base-compiler.4.08.1

    # Install the necessary packages
    opam repository add coq-released https://coq.inria.fr/opam/released
    opam install coq.8.9.1 camlp5.7.14 menhir.20201216 coq-coq2html.1.2

    # Configure the current shell to use the newly created opam switch
    eval $(opam env)

### Build instructions

In addition,
our modifications rely on the Coqrel library, which must be built
first. We will include Coqrel in any self-contained archive we
distribute, but if you are working in a git clone, you must first
retreive it with the following commands:

    % git submodule init
    % git submodule update

In any case, to build Coqrel, proceed in the following way:

    % (cd coqrel && ./configure && make)

You can then build the updated proof as follows:

    % ./configure x86_64-linux
    % make
    % make documentation

If appropriate to your setting, we recommend you use a -j option when
invoking make so as to enable parallel compilation.

## Documentation

After running `make documentation` you will be able to browse the
generated [documentation](doc/index.html). We have annotated the
index file to highlight the changes and additions made in CompCertO.

The remainder of this document is the original `README.md` distributed
with CompCert v3.6.

---

# CompCert
The formally-verified C compiler.

## Overview
The CompCert C verified compiler is a compiler for a large subset of the
C programming language that generates code for the PowerPC, ARM, x86 and
RISC-V processors.

The distinguishing feature of CompCert is that it has been formally
verified using the Coq proof assistant: the generated assembly code is
formally guaranteed to behave as prescribed by the semantics of the
source C code.

For more information on CompCert (supported platforms, supported C
features, installation instructions, using the compiler, etc), please
refer to the [Web site](https://compcert.org/) and especially
the [user's manual](https://compcert.org/man/).

## License
CompCert is not free software.  This non-commercial release can only
be used for evaluation, research, educational and personal purposes.
A commercial version of CompCert, without this restriction and with
professional support and extra features, can be purchased from
[AbsInt](https://www.absint.com).  See the file `LICENSE` for more
information.

## Copyright
The CompCert verified compiler is Copyright Institut National de
Recherche en Informatique et en Automatique (INRIA) and 
AbsInt Angewandte Informatik GmbH.


## Contact
General discussions on CompCert take place on the
[compcert-users@inria.fr](https://sympa.inria.fr/sympa/info/compcert-users)
mailing list.

For inquiries on the commercial version of CompCert, please contact
info@absint.com
