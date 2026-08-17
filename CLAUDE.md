# CLAUDE.md

This file provides guidance to Claude when working with code in this repository.

## About this repository

This repository contains an Agda formalisation of *algebraic type theory*: an
algebraic account of what a type theory is. The ideas here are inspired by First
Order Logic with Dependent Sorts, with Applications to Category Theory - M.
Makkai.

The framework is built up in several steps.

**Dependent sort vocabulary** (`DependentSortVocabulary.agda`) — a set valued
semicategory `𝒥`. The objects are the *judgment forms* available in the type
theory (e.g. `Ty`, `El` for MLTT), and the morphisms are *dependencies* between
them (e.g. `typeOf : El → Ty` for MLTT). In order to make a sound type theory,
the judgmentform semicategory should be wellfounded, i.e. there should not be a
circular or infinite dependency chain. However, this has not yet been added to
the `DependentSortVocabulary` type, as we have not yet had need for it in the
later constructions. It might be included later.

**Context** (`Context.agda`) — a set-valued presheaf `𝒥 → hSet`. `Γ ⟨ j ⟩` is
the set of context elements of judgment form `j`; `Γ ⟨ f ⟩` computes an
element's dependencies (given an element of form `El`, the type `Ty` it is an
element of). `ContextMorphism`/`_⇒_` is a seminatural transformation: elements
are mapped to elements of the same type in a way that is coherent with the
dependencies. Contexts and their morphisms are given
`Composable`/`AssociativeComposition`/`Identity` instances, and the identity
type of `_⇒_` is characterised via `ContextMorphismEquality` and structure
identity (requires `FunExt`).

**Yoneda contexts** — `𝒴 j` is the generic context of arguments to a judgment
of form `j`: it contains one element for each dependency of the judgment form.
`𝒴⁺⁺ j` adds *two* distinguished copies of `j` (`Hom 𝒥 j j₁ + ((j₁ ＝ j) + (j₁
＝ j))`); `𝒴⁺ j` adds one.

**Extension and collapse** — The idea is that when one has a context, one may do
two things: extend the context with an element, or realise that two elements
were the same, i.e. collapse them. When extending a context with an element of a
judgmentform `j`, one has to say how its dependencies are realised in the
context. This is done with a natural transformation from `𝒴 j` into the
context. So `Extension Γ` consists of a judgment form plus a natural
transformation `𝒴 judgmentForm ⇒ Γ`. For collapses, one has to say which two
elements (that are of the same judgmentform and has the same dependencies) are
equal. This is done with a natural transformation from `𝒴⁺⁺ j` into the
context. So `Collapse Γ` is a judgment form plus `𝒴⁺⁺ judgmentForm ⇒ Γ`.

When one has the data of an extension or a collapse of a context, one may
perform the actual extension or collapse with the operator `_⋊_`. There is also
an inclusion/surjection from the original context to the extended/collapsed
context: `→⋊`.

**Sequent** (`Sequent.agda`) — a sequent is a context plus an extension or collapse
of it. It corresponds to what type theorists usually write as `x : A ⊢ d : A × A`.
The `x : A` is the context, the `d : A × A` is the extension or collapse. It is 
worth noting that as we have set it up, one does not add definitional equality as
judgmentforms, rather one can always invoke the ambient meta-equality to definitionally
identify elements in the theory. This differs from Martin-Löfs presentation of his
type theory. However, it has the benefit of not having to add the structural rules
for definitional equalities: these hold automatically because they hold for the
ambient meta-equality. (One may of course define propositional equality
inside the type theory.)

**SequentMorphism** (`Sequent.agda`) — a `ContextMorphism` from the extended
context of one sequent into the extended context of another. One example is when
referencing the result of one sequent in the context of another. For example,
the sequent `x : Ob, f g : Hom x 1 ⊢ f = g` references the (result of) the
sequent `⊢ 1 Ob` in its context. This is done by a context sequent morphism from
the latter sequent to the first sequent. In this case, the morphism lands in the
original (non-extended) context of the target sequent. But in the premises of
rules we will also need to be able to have the conclusion of a sequent be an
application of a previous sequent, hence why a sequent morphism is allowed to
land in the extension of the target sequent (not just the context). Sequents and
sequent morphisms yields `SequentSemicategory 𝒥 i`.

Elements of a context that are the image of the extension/collapse of another
sequent we will call *terms*. I.e. these are elements in the context that have
been constructed by applying an operation to (some of) the elements of the
context.

**SequentStructure** (`SequentStructure.agda`) — a sequent structure is a
structure of sequents with dependencies on one another. It consists of a
semicategory `dependency` (objects are operations/sequent names) together with a
`Semifunctor (dependency ᵒᵖ) (SequentSemicategory 𝒥 i)`, i.e. a coherent
realisation of each dependency into a sequent morphism. Each operation gets a
sequent; each dependency between operations gets a sequent morphism.

**SequentStructureWithExtension and ContextWithTerms** — there are two very
similar constructions on sequent structures that have been abstracted out into a
common construction: `SequentDependencyStructure`. This is the data needed to
extend a sequent structure with a new sequent, in the case of
`SequentStructureWithExtension`, or to define a context where some of the
elements might be terms (applications of other sequents), in the case of
`ContextWithTerms`. The data needed is:
- a head (either a sequent or a context)
- a sequent structure
- the dependencies of the head on other sequents
- a context morphism for each dependency into the context of the head (the
  extension/collapse of a sequent, the identity for a context)
- a coherence condition on how the added dependencies interact with the
  dependencies from the sequent structure

**Rule** (`Rule.agda`) — a rule is simply a sequent structure with extension.
The premises of the rule make up the sequent structure and the conclusion of the
rule make up the data for the extension. I.e. a rule states how we can extend
sequent structures with another sequent. This is analogous to how a sequent
states how we can extend a context with another element. The difference of
course being that we only allow extensions on the level of rules, not collapses,
as we do on the level of sequents.

**RuleMorphism** — rule morphisms are intended to capture the notion of applying
one rule in the premises of another rule. Such an application consists of giving
a coherent set of sequent morphisms from the sequents in the extended sequent
structure of the source rule into the premise sequents of the target rule. The
contexts of the target sequents do not need to be exactly the form of the
contexts of the source sequents. However, there should be one context with terms
that one can add to all contexts in the source sequents such that there is an
isomorphism of contexts between the sequents in the source rule and the sequents
in the target rule.

## Build & check

Everything must be run from the repository root; Agda resolves `src` and the
`UniLib` dependency through `AlgebraicTypeTheory.agda-lib` in the working
directory, so invoking `agda` on a file from elsewhere fails with "file not
found in include path".

```bash
agda --build-library          # typecheck the whole library (the "full build")
agda src/Sequent.agda         # typecheck one module and its dependencies
```

Silent output with exit 0 means success. Interface files land in
`_build/2.8.0/agda/`.

Agda 2.8.0 and the `UniLib` dependency are provided by the nix flake; a shell is
usually already inside `nix develop`. `nix build` reproduces the same typecheck
under nix, but `UniLib` is fetched over SSH from `git.app.uib.no` and needs
working credentials. There is a cache with build files, so when fetching the
latest from the main branch, the library does not have to be type checked
locally.

Library-wide flags (from `AlgebraicTypeTheory.agda-lib`): `--no-import-sorts
--without-K --guardedness`.

### Examples

The `src/Example/` directory contains examples of type theories defined in the
framework defined in `src/`.

- `src/Example/Category.agda` : category theory.
- `src/Example/MLTT.agda` : Martin-Löf type theory.

## Working with UniLib

Every import that is not a module of this repo comes from UniLib (source: the
store path in the flake, `.../UniLib-0.0.1-unstable/src/`). Reading the relevant
UniLib module is usually faster than guessing; its records carry explanatory
comments. The library is in an early stage and changes often. It can be found at
https://git.app.uib.no/Hakon.Gylterud/unilib/ and has claude code instructions
in the `CLAUDE.md` file. Browse here if necessary, when you need information
about the workings of `UniLib`.

## Conventions in this repo

- Records should be constructed using `record { … }` syntax.
- Naturality is stated as an equality of functions and proved by `funExt ∘
  natural~`, where `natural~` is a pointwise homotopy defined by pattern
  matching in a `where` block.
- Use `Foundation.Reasoning` for coherence proofs as a rule of thumb. However,
  there are instances where this slows down type checking as opposed to just
  composing the paths. In such cases, use path composition. But try with the
  equational reasoning first and only swap if there is a reason.
- Keep comments to a minimum, adding them only if *absolutely necessary*, and keep
  them diegetic.
