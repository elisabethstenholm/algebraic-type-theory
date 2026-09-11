module RuleMorphism.Composition where

open import Prelude
open import Axioms
open import Homotopy.SetQuotient.Nominal
open import Algebra.Wild.Semicategory
open import Algebra.Wild.Semifunctor
open import Syntax.Arrowable
open import Homotopy.Equality
open import Homotopy.Levels
open import Homotopy.StructuredType
open import Homotopy.Fibre
open import Foundation.DependentPair.Equivalence
open import Foundation.Identity.Equivalence
open import Structure.Composable
open import Structure.Identity
open import Structure.Symmetric
open import Structure.Associativity
open Semicategory

open import DependentSortVocabulary
open import Context
open import Context.Morphism
open import Context.Extension
open import Context.ExtensionMorphism
open import Sequent
open import Sequent.Morphism
open import SequentStructure
open import SequentStructure.Equality
open import SequentDependencyStructure
open import SequentDependencyStructure.Equality
open import ContextWithTerms
open import Weakening.Sequent
open import Weakening.SequentStructure
open import SequentStructureMorphism
open import SequentStructureMorphism.Equality
open import Rule
open SequentDependencyStructure.SequentDependencyStructure
open ContextWithTerms.ContextWithTerms
open import Weakening.Sum
open import Weakening.SequentStructureMorphism
open import RuleMorphism
open RuleMorphism.RuleMorphism


-- =============== The premise inclusion ===============

module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a} where

  private
    opaque
      idSquareᴿ : {l₀ l₁ : Level} {s₀ : Sequent 𝒥 l₀} {s₁ : Sequent 𝒥 l₁}
                  (α : SequentMorphism s₀ s₁)
                → toSequentMorphism (sequentEquivalence-identity {s = s₁}) ∙ α
                  ＝ α ∙ toSequentMorphism (sequentEquivalence-identity {s = s₀})
      idSquareᴿ {s₀ = s₀} {s₁ = s₁} α =
        ap mkSequentMorphism (eq (record { component≈ = λ j → funExt (λ z →
             toSequentMorphism-identity-at {s = s₁} j ((SequentMorphism.sequentMorphism α ⟨ j ⟩) z)
          ⨾  sym (ap (SequentMorphism.sequentMorphism α ⟨ j ⟩)
                     (toSequentMorphism-identity-at {s = s₀} j z))) }))

  premiseInclusion : (r : Rule 𝒥 so sa i)
                   → SequentStructureMorphism (premises r) (⋊ₛ r)
  premiseInclusion r =
    record
      { dependencyMorphism = record
          { onDependencies = onDep
          ; dependenciesEquivalence = depsEq }
      ; sequentEquivalence = λ x → sequentEquivalence-identity {s = ℱ ⟨ x ⟩}
      ; natural = λ {x} {y} f → idSquareᴿ (ℱ ⟨ f ⟩) }
    where
      𝒟 = SequentStructure.dependency (premises r)
      ℱ = SequentStructure.sequent (premises r)

      onDep : Semifunctor 𝒟 (SequentStructure.dependency (⋊ₛ r))
      onDep =
        record
          { onObjects = ExtendedSequentStructure.injOb
          ; semifunctorial = record
              { mappable = record { map = λ {x} {y} f → ExtendedSequentStructure.include f }
              ; preservesComposition = record
                  { preserves-composition = λ f g → refl } } }

      depsEq : (x : Ob 𝒟) → isEquivalence (mapDependencies onDep x)
      depsEq x =
        record
          { section = record { sectionBack = back ; isSection = sect }
          ; retraction = record { retractionBack = back ; isRetraction = retr } }
        where
          back : dependenciesOf (SequentStructure.dependency (⋊ₛ r))
                   (ExtendedSequentStructure.injOb x)
               → dependenciesOf 𝒟 x
          back (ExtendedSequentStructure.injOb y , ExtendedSequentStructure.include f) = y , f
          back (ExtendedSequentStructure.newOb , ExtendedSequentStructure.include ())

          sect : (d : dependenciesOf (SequentStructure.dependency (⋊ₛ r))
                        (ExtendedSequentStructure.injOb x))
               → mapDependencies onDep x (back d) ＝ d
          sect (ExtendedSequentStructure.injOb y , ExtendedSequentStructure.include f) = refl
          sect (ExtendedSequentStructure.newOb , ExtendedSequentStructure.include ())

          retr : (d : dependenciesOf 𝒟 x) → back (mapDependencies onDep x d) ＝ d
          retr (y , f) = refl


-- =============== Composition of rule morphisms ===============

module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a} where

  ruleAssocSSM : (b₁ b₀ : ContextWithTerms 𝒥 so sa i) (X : SequentStructure 𝒥 so sa i)
               → SequentStructureMorphism ((b₁ ⧺ᶜ b₀) ⧺ X) (b₁ ⧺ (b₀ ⧺ X))
  ruleAssocSSM b₁ b₀ X = equivToSSM (⧺-assocEquality b₁ b₀ X)

  infixl 15 _⨾ᴿ_
  _⨾ᴿ_ : {r₀ r₁ r₂ : Rule 𝒥 so sa i}
       → RuleMorphism r₀ r₁ → RuleMorphism r₁ r₂ → RuleMorphism r₀ r₂
  _⨾ᴿ_ {r₀ = r₀} {r₁ = r₁} {r₂ = r₂} φ ψ =
    mkRuleMorphism
      (baseContext ψ ⧺ᶜ baseContext φ)
      (sequentStructureMorphism-⨾
        (ruleAssocSSM (baseContext ψ) (baseContext φ) (⋊ₛ r₀))
        (sequentStructureMorphism-⨾
          (baseContext ψ ⧺ˢ ruleMorphism φ)
          (sequentStructureMorphism-⨾
            (baseContext ψ ⧺ˢ premiseInclusion r₁)
            (ruleMorphism ψ))))


