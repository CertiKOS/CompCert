# CompCert-RBGS
A version of CompCert featuring an open module semantics, designed to
target the framework of *refinement-based game semantics*.

## Note on anonymity
The text below includes links to [github.com](http://github.com).
They have been obfuscated using [tinyurl.com](http://tinyurl.com)
to allow reviewers to avoid any identifying information.
Our understanding is that anonymity does not need to be preserved
after the first round of review, so we encourage reviewers to proceed
nonetheless.

## Overview
This is a modified version of CompCert v3.5. The language semantics
have been updated to model open modules, and a correctness theorem
has been rederived in this updated setting. Our compiler is mostly
restricted to translation passes, and to the x86 architecture.

## Building
Our modifications rely on the Coqrel library, which must be built
first. We will include Coqrel in any self-contained archive we
distribute, but if you are working in a git clone, you must first
retreive it with the following commands:

    % git submodule init
    % git submodule update

In any case, to build Coqrel, proceed in the following way:

    % (cd coqrel && ./configure && make)

You can then build the updated proof as follows:

    % ./configure x86_64-linux
    % make driver/Compiler.vo

If appropriate to your setting, we recommend you use a -j option when
invoking make so as to enable parallel compilation.

## Changes to CompCert
Our changes build on a modified version of the CompCert memory model.
This version partitions the block namespace into global blocks
(named after the corresponding global identifier), and dynamically
allocated blocks (which are assigned a `positive` identifier in the
usual way). This ensures that components agree on the `Genv.find_symbol`
mapping.

We will include two diffs when distributing this development:

  * `globmem.diff` contains the changes to the memory model described
    above. Please refer to [this page](https://preview.tinyurl.com/yy8etrou)
    for further discussion.
  * `composable-compcert.diff` contains our changes to the semantic
    model and our updated proofs. The most notable ones are discussed
    below.

(XXX: Do that here.)

## Github repositories
This code is available [on github](https://preview.tinyurl.com/y5rv37k8)
(note this link points to a specific branch).

A [more up-to-date version](https://preview.tinyurl.com/y6ot5rmk)
of our work can be found there as well.

The up-to-date verson covers more passes and features a
`Smallstep`-level semantic linking operator. This operator preserves
backward simulations. We also relate it to the syntactic linking of
assembly programs defined in CompCert in the context of separate
compilation: we show that the semantics of the linked assembly program
is a refinement of the linked semantics of its components. This is the
post important property in the context of compositional verification:
the semantic linking operator serves as a specification for the
linking of assembly components programs once they have been compiled.

Our work on refinement-based game semantics can be found
[here](https://preview.tinyurl.com/y6d6m54d).
It (XXX: will soon) include a formalization of the interaction monad.

The remainder of this document is the original `README.md` distributed
with CompCert v3.5.

---

# CompCert
The verified C compiler.

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
refer to the [Web site](http://compcert.inria.fr/) and especially
the [user's manual](http://compcert.inria.fr/man/).

## License
CompCert is not free software.  This non-commercial release can only
be used for evaluation, research, educational and personal purposes.
A commercial version of CompCert, without this restriction and with
professional support, can be purchased from
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
