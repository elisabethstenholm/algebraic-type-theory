# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

An Agda formalisation of *algebraic type theory*: an algebraic account of what a type theory is. There is no executable program and no test suite — **typechecking is the build, and it is the only check**.

## Build & check

Everything must be run from the repository root; Agda resolves `src` and the `UniLib` dependency through `AlgebraicTypeTheory.agda-lib` in the working directory, so invoking `agda` on a file from elsewhere fails with "file not found in include path".

```bash
agda --build-library          # typecheck the whole library (the "full build")
agda src/Sequent.agda         # typecheck one module and its dependencies
```

Silent output with exit 0 means success. Interface files land in `_build/2.8.0/agda/`.

Agda 2.8.0 and the `UniLib` dependency are provided by the nix flake; a shell is normally already inside `nix develop`. `nix build` reproduces the same typecheck under nix, but `UniLib` is fetched over SSH from `git.app.uib.no` and needs working credentials.

Library-wide flags (from `AlgebraicTypeTheory.agda-lib`): `--no-import-sorts --without-K --guardedness`.

## The theory being formalised

The layers build strictly on one another; reading them in this order is the fastest way in.

**Dependent sort vocabulary** (`WellfoundedSemicategory.agda`, `DependentSortVocabulary.agda`) — a wellfounded semicategory `𝒥`. Objects are *judgment forms*, morphisms are *dependencies* between them. For MLTT: `Ty`, `El`, and `typeOf : El → Ty`. For categories: `Ob`, `Hom`, and `Hom-sc`, `Hom-tg : Hom → Ob`. Wellfoundedness rules out circular dependency; in practice the vocabulary is a finite `data` type with a hand-written `Accessible` proof per judgment form.

**Context** (`Sequent.agda`) — a semifunctor `𝒥 → Type`. `Γ ⟨ j ⟩` is the set of context entries of judgment form `j`; `Γ ⟨ f ⟩` computes an entry's dependencies (given an entry of form `Hom`, its source and target `Ob` entries). `ContextMorphism`/`_⇒_` is a seminatural transformation. Contexts and their morphisms are given `Composable`/`AssociativeComposition`/`Identity` instances, and the identity type of `_⇒_` is characterised via `ContextMorphismEquality` and structure identity (requires `FunExt`).

**Yoneda contexts** — `𝒴 j` (representable, i.e. `SemiCoYoneda`) is the generic context of arguments to a judgment of form `j`. `𝒴⁺⁺ j` adds *two* distinguished copies of `j` (`Hom 𝒥 j j₁ + ((j₁ ＝ j) + (j₁ ＝ j))`); `𝒴⁺ j` adds one. These are the "shapes" that extensions and collapses are maps out of.

**Extension and collapse** — an `Extension Γ` is a judgment form plus `𝒴 judgmentForm ⇒ Γ`: it names one new entry and says what its dependencies are. A `Collapse Γ` is a judgment form plus `𝒴⁺⁺ judgmentForm ⇒ Γ`: it names two existing entries to be identified. `Γ ⋊ₑ ext` is the extended context (`Γ ⟨ j ⟩ + (j ＝ judgmentForm)`) with inclusion `ι`; `Γ ⋊ₖ col` is the set quotient by `CollapseRelation` (requires `AllSetQuotients`) with quotient map `σ`.

**Sequent** — `context` plus an `ExtensionOrCollapse` of it: either "Γ ⊢ a new entry of form j" or "Γ ⊢ these two entries of form j are equal". `_⋊_` dispatches over the two; `→⋊` produces the canonical `Γ ⇒ Γ ⋊ …` (`ι` or `σ`).

**SequentMorphism** (`SequentStructure.agda`) — a `ContextMorphism` out of the *extended* context of the source into the context of the target. Composition threads through `→⋊`, which is why the associativity proof is nontrivial. This yields `SequentSemicategory 𝒥 i`.

**SequentStructure** — a semicategory `sequentDependency` (objects are *operations*/rule names) together with `Semifunctor (sequentDependency ᵒᵖ) (SequentSemicategory 𝒥 i)`. Each operation gets a sequent; each dependency between operations gets a sequent morphism.

**SequentStructureExtension** (`SequentStructureExtension.agda`) — the data for adjoining one new operation: a `dependency` semifunctor into `Type` (which existing operations the new one draws on, and how many ways), a `head` sequent, `realiseDependency` turning each such arrow into a sequent morphism, and `coherenceRealisation` making that assignment functorial. `extendSequentStructure` performs the adjunction by freely adding `newOb` to the dependency semicategory, with `hom' newOb (injOb x) = dependency e ⟨ x ⟩` and no arrows out of `newOb` into itself or into `newOb` at all.

**Rule** (`Rule.agda`) — `premises : SequentStructure` plus `extension : SequentStructureExtension premises`. A rule states how one can extend a sequent structure by one operation.

### Examples

The `src/Example/` directory contains examples of type theories defined in the framework defined in `src/`.

- `src/Example/Category.agda` : category theory.
- `src/Example/MLTT.agda` : Martin-Löf type theory.

## Working with UniLib

Every `Foundation.*` import comes from UniLib (source: the store path in the flake, `.../UniLib-1.0.0/src/`). Reading the relevant UniLib module is usually faster than guessing; its records carry explanatory comments.

**Notation.** `_＝_` (full-width) is the identity type. `_⟨_⟩` is instance-resolved application (`Appliable`) — it covers semifunctor-on-objects, semifunctor-on-morphisms, and, via instances declared in `Sequent.agda`/`SequentStructure.agda`, `Γ ⟨ j ⟩`, `Γ ⟨ f ⟩` and `ϵ ⟨ j ⟩`. `_⨾_` is diagrammatic composition (left to right), `_∙_` is the usual order (`f ∙ g` = `g` then `f`); both come from `Composable`, so a missing instance shows up as an unsolved `_⨾_`/`_∙_` rather than a type error at the call site. `∑[ x ∶ A ]` is Σ; `𝟘`/`𝟙`/`★` are the empty and unit types.

**Building a semicategory.** Sometimes you should use instances for `Composable`, `AssociativeComposition` and `Semicategorical` + `asSemicategory` to define a semicategory. Sometimes you should fill the `Semicategory` record directly. As a rule of thumb, if the semicategory in question has objects and/or arrows on several type levels (e.g. indexed by `Level`) we want the instances in scope so you should use the `asSemicategory` method. If the semicategory in question only has objects and arrows on one level (as in the `src/Examples` files), you should take the other approach. The same holds for other structures such as `Semifunctor` for example.

**Reasoning modules.** `Hom` and composition sit behind non-invertible projections, so instances cannot be found for a semicategory held in a variable. Open `Semicategory.Reasoning 𝒞` / `Semifunctor.Reasoning F` locally to bring them into scope — the source does this inside `where` blocks, frequently opening several at different levels in one block.

**Axioms are instance arguments, not postulates.** `⦃ _ : FunExt ⦄` and `⦃ _ : AllSetQuotients ⦄` are threaded through every definition that needs them. Adding a use of `funExt` or of the quotient means adding the constraint to the signature and to every caller.

**Set quotients.** Open `FromAllSetQuotients A R` to get `[_]`, `⁄-rec`, `⁄-elim`, `⁄-rec-β`, `respects`. Instance resolution for `isSet` is fragile here — see the note at `src/Sequent.agda:431`; opening the module for each object level involved is what makes it go through.

**Equational proofs** use `Foundation.Reasoning`: `begin x ⟪ p ⟫ y ⟪ q ⟫ z ∎`.

## Conventions in this repo

- Universe levels are explicit and pervasive: `o a` for the vocabulary semicategory, `i` for contexts, `so sa` for the sequent-dependency semicategory. Extension raises a context's level from `i` to `o ⊔ i`.
- Records get a `constructor`, and are frequently defined by copattern matching on the projections (`context idSequent = …` / `extensionOrCollapse idSequent = …`) rather than as a `record { … }` literal.
- Naturality is stated as an equality of functions and proved by `funExt ∘ natural~`, where `natural~` is a pointwise homotopy defined by pattern matching in a `where` block. Follow that split; the pointwise version is where the actual case analysis lives.
- Use `Foundation.Reasoning` for coherence proofs.
- Keep comments to a minimum, adding them only if absolutely necessary, and keep them diegetic.
