# TRANSFINITE IRIS COQ DEVELOPMENT

This is the Coq development of the Transfinite Iris project. 
It is based on the Coq development of the [Iris Project](http://iris-project.org),
which includes [MoSeL](http://iris-project.org/mosel/), a general proof mode
for carrying out separation logic proofs in Stdlib.

For using Transfinite Iris and inspecting the development interactively, it needs to be compiled.

## Building Transfinite Iris

### Prerequisites

This version is known to compile with:

 - Rocq 9.0.1
 - std++ `dev.2026-09-17.0.d510b616` ([std++](https://gitlab.mpi-sws.org/iris/stdpp))
 - Iris master at commit `8e4909593a3a84f850d224a344cbd3a380672088`, plus the
   four commits of the Iris branch `robbert/transfinite` that change the BI laws
   to support Transfinite step-indexing (`later_exist_false`/`later_sep_1` only
   for finite step-indices, the new laws `later_false_impl_exist` and
   `later_false_impl_sep`, and `Timeless P := <only0> P ⊢ P`).

The development no longer depends on the parametric-index fork of Iris: it uses
upstream Iris's step-index interface `sidx` (`iris.algebra.stepindex`) and its
`bi`/`Sbi` interfaces, and instantiates them with the Transfinite `uPred` model
for any step-index type (in particular, the ordinals `ordI`).

### Installation

Install the dependencies above (e.g., with opam, see the `opam` file; for a local
checkout of Iris/std++, add the corresponding `-Q` paths to `_CoqProject`), then
run `make -jN` to build the full development, where `N` is the number of threads
to use for the build process, and `make install` to install it as the Rocq library
`transfinite` (this is what the opam package `rocq-iris-transfinite` does).

Until the Iris branch `robbert/transfinite` is merged upstream, the `rocq-iris` this
development needs is the patched one: upstream Iris at the commit above with those four
commits (and one local fix) on top, pinned as
`rocq-iris.dev.2026-09-24.0.8e490959+transfinite.<commit>`. The Makefile is a plain
`coq_makefile` wrapper; the same `_CoqProject` serves an installed Iris and a local one.

## Directory Structure

* The folder [program_logic](theories/program_logic) is upstream Iris's program logic
  (`language`, `weakestpre`, `lifting`, `adequacy`) over the transfinite base logic,
  generic in the step index `SI : sidx` (the only proof change is the well-founded
  induction in `wp_ne`, which is over `SI` instead of `nat`); `wp_strong_adequacy` holds
  at every index, in particular at the ordinals `ordI`.

* The folder [ordinals](theories/algebra/ordinals) contains a formalisation of 
  von Neumann ordinals and basic ordinal arithmetic. 
* The folder [algebra](theories/algebra) contains step-index types, 
  the COFE and CMRA constructions as well as the solver for recursive domain equations.
* The folder [base_logic](theories/base_logic) defines the Iris base logic and
  the primitive connectives.  It also contains derived constructions that are
  entirely independent of the choice of resources.
  * The subfolder [lib](theories/base_logic/lib) contains some generally useful
    derived constructions.  Most importantly, it defines composeable
    dynamic resources and ownership of them; the other constructions depend
    on this setup.
* The folder [program_logic](theories/program_logic) specializes the base logic
  to build Iris, the program logic. This includes weakest preconditions that
  are defined for any language satisfying some generic axioms, and some derived
  constructions that work for any such language.
* The folder [refinement](theories/program_logic/refinement) contains the definition
  of a program logic for termination-preserving refinement and termination.
* The folder [bi](theories/bi) contains the BI++ laws, as well as derived
  connectives, laws and constructions that are applicable for general BIS.
* The folder [proofmode](theories/proofmode) contains
  [MoSeL](http://iris-project.org/mosel/), which extends Coq with contexts for
  intuitionistic and spatial BI++ assertions. It also contains tactics for
  interactive proofs. Documentation can be found in
  [ProofMode.md](ProofMode.md).
* The folder [heap_lang](theories/heap_lang) defines the ML-like concurrent heap
  language.
* The folder [examples](theories/examples) contains examples executed in 
  Transfinite Iris. See below for a detailed summary.

## Examples

The following is a list of examples we have done in Transfinite Iris.
* The key notions of simulations and generalized simulations used for the 
  key ideas section of the paper are formalized in [keyideas](theories/examples/keyideas).
* Counterexamples for some negative statements in the paper are formalized in 
  [counterexamples.v](theories/examples/counterexamples.v)
* [safety](theories/examples/safety) contains examples for safety reasoning taken 
  from existing work that we have ported to Transfinite Iris.
* [termination](theories/examples/termination) contains proofs of termination:
  * [eventloop](theories/examples/termination/eventloop.v) contains the verification
    of the eventloop example from the paper.
  * [thunk](theories/examples/termination/thunk.v) contains the verification of a thunk example.
  * [logrel](theories/examples/termination/logrel.v) formalizes and extends the 
    logical relation for termination by Spies et al, "Transfinite Step-Indexing for Termination" 
* [refinements](theories/examples/refinements) contains the termination-preserving refinement
  examples from the paper.
  * [derived] (theories/examples/refinements/derived.v) contains the derived Hoare triples shown in the paper.
  * [refinement](theories/examples/refinements/refinement.v) contains the HeapLang source language.
  * [memoization](theories/examples/refinement/memoization.v) provides memoization functions and 
    the following examples:
    * Fibonacci function
    * Levenshtein distance


## Theorems referenced in the paper

We have fully mechanized the soundness of Iris and the examples in §3.4 and §4.2.
The following table references the corresponding theorems as well as some additional mechanized lemmas.

| Paper | Coq |
| ------ | ------ |
| Lemma 2.1 | [simulations/sim_is_rpr](theories/examples/keyideas/simulations.v) |
| Lemma 2.2 | [simulations/sim_is_tpr](theories/examples/keyideas/simulations.v) |
| Hoare Proof Rules of Figure 1 | [derived](theories/examples/refinements/derived.v) |
| Theorem 3.3 (Refinement Adequacy) | [heap_lang_ref_adequacy](theories/examples/refinements/refinement.v) | 
| Definition of memo_rec | [mem_rec](theories/examples/refinements/memoization.v) | 
| PureMemoRec (simpl) | [natfun_mem_rec_spec](theories/examples/refinements/memoization.v) | 
| Levenshtein and Fibonacci | [memoization](theories/examples/refinements/memoization.v) | 
| Theorem 4.1 (Time Credits Adequacy) | [heap_lang_ref_adequacy](theories/examples/termination/adequacy.v) | 
| Reentrant Event Loop | [event_loop](theories/examples/termination/eventloop.v) | 
| Logical Relation for Termination | [logrel_adequacy](theories/examples/termination/logrel.v) | 
| Ordinals validate the existential property | [set_model_large_index](theories/algebra/ordinals/ord_stepindex.v) |
| Theorem 5.3 | [fixpoint](theories/algebra/ofe.v) | 
| Model Construction (Theorem 5.4) | [iprop](theories/base_logic/lib/iprop.v) | 
| Theorem 5.5 | [no_later_existential_commuting](theories/examples/counterexamples.v) | 

## Acknowledgements

The mechanization of set-theoretic ordinals and the underlying ZF model construction 
has been based on Coq code by Dominik Kirst and Gert Smolka, available at: 

* "Large Model Constructions for Second-Order ZF in Dependent Type Theory"
  by Dominik Kirst and Gert Smolka, CPP 2018
  See https://www.ps.uni-saarland.de/Publications/details/KirstSmolka:2017:Large-Model.html.
* "Formalised Set Theory: Well-Orderings and the Axiom of Choice", Dominik Kirst. 
  See https://www.ps.uni-saarland.de/~kirst/bachelor.php 
