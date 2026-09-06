module Context where

open import Prelude
open import Axioms
open import Homotopy.Equality
open import Homotopy.Equality.StructureIdentity
open import Homotopy.Fibre
open import Foundation.DependentFunction.Equivalence
open import Foundation.DependentPair.Equivalence
open import Homotopy.Levels
open import Structure.Reasoning
open import Homotopy.StructuredMap
open import Homotopy.StructuredType
open import Structure.Composable
open import Structure.Associativity
open import Structure.Identity
open import Structure.PreservesComposition
open import Structure.Symmetric
open import Structure.Unit
open import Structure.Whiskerable
open import Algebra.Wild.Semi
open import Algebra.Wild.TruncatedTypeSemicategory
open import Homotopy.SetQuotient
open import Syntax.Arrowable

open import DependentSortVocabulary
open DependentSortVocabulary.DependentSortVocabulary


-- ============ Contexts ===============

record Context
  {o a : Level}
  (𝒥 : DependentSortVocabulary o a)
  (i : Level)
  : Type (o ⊔ a ⊔ lsuc i) where
  constructor mkContext
  field
    semifunctor : Semifunctor (semicategory 𝒥) (hSet-Semicategory i)

module _ {o a i : Level} {𝒥 : DependentSortVocabulary o a} where

  instance
    appliableOnObjectsContext : Appliable (Context 𝒥 i) (type (Judgment 𝒥)) (λ _ _ → hSet i)
    appliableOnObjectsContext = record { function = λ Γ j₀ → Context.semifunctor Γ ⟨ j₀ ⟩ }

    appliableOnMorphismsContext : {j₀ j₁ : type (Judgment 𝒥)} → Appliable (Context 𝒥 i) (type (JudgmentDependency 𝒥 j₀ j₁)) (λ Γ _ → ⌞ Γ ⟨ j₀ ⟩ ⌟ → ⌞ Γ ⟨ j₁ ⟩ ⌟)
    appliableOnMorphismsContext = record { function = λ Γ f → Context.semifunctor Γ ⟨ f ⟩ }

emptyContext : {o a : Level} (𝒥 : DependentSortVocabulary o a) (i : Level) → Context 𝒥 i
emptyContext 𝒥 i =
  record
    { semifunctor = record
      { onObjects = λ j → 𝟘
      ; semifunctorial = record
          { mappable = record { map = λ f () }
          ; preservesComposition = record { preserves-composition = λ f g → refl } } } }

module _ ⦃ _ : FunExt ⦄ {o a : Level} {𝒥 : DependentSortVocabulary o a} where

  sumContext : {i j : Level} → Context 𝒥 i → Context 𝒥 j → Context 𝒥 (i ⊔ j)
  sumContext {i} {j} Γ Δ =
    record { semifunctor = record
               { onObjects = onObjects
               ; semifunctorial = record
                   { mappable = record { map = onMorphisms }
                   ; preservesComposition = record
                       { preserves-composition = λ f g → funExt (preservesComposition~ f g) } } } }
    where
      open Semicategory.Reasoning (semicategory 𝒥)

      onObjects : type (Judgment 𝒥) → hSet (i ⊔ j)
      onObjects j₀ = (⌞ Γ ⟨ j₀ ⟩ ⌟ + ⌞ Δ ⟨ j₀ ⟩ ⌟) has-level itIsSet
        where
          opaque
            itIsSet : isSet (⌞ Γ ⟨ j₀ ⟩ ⌟ + ⌞ Δ ⟨ j₀ ⟩ ⌟)
            itIsSet = +-level (level-proof (Γ ⟨ j₀ ⟩)) (level-proof (Δ ⟨ j₀ ⟩))

      onMorphisms : ∀ {j₀ j₁} → type (JudgmentDependency 𝒥 j₀ j₁) → ⌞ onObjects j₀ ⌟ → ⌞ onObjects j₁ ⌟
      onMorphisms f (inl x) = inl ((Γ ⟨ f ⟩) x)
      onMorphisms f (inr y) = inr ((Δ ⟨ f ⟩) y)

      preservesComposition~ : ∀ {j₀ j₁ j₂} (f : type (JudgmentDependency 𝒥 j₀ j₁)) (g : type (JudgmentDependency 𝒥 j₁ j₂))
                            → onMorphisms (g ∙ f) ~ onMorphisms g ∘ onMorphisms f
      preservesComposition~ f g (inl x) = ap (λ h → inl (h x)) (preserves-composition f g)
        where
          open Semifunctor.Reasoning (Context.semifunctor Γ)
          open Semicategory.Reasoning (hSet-Semicategory i)
      preservesComposition~ f g (inr y) = ap (λ h → inr (h y)) (preserves-composition f g)
        where
          open Semifunctor.Reasoning (Context.semifunctor Δ)
          open Semicategory.Reasoning (hSet-Semicategory j)

  instance
    addableSumContext : Addable Level (Context 𝒥) _⊔_
    addableSumContext = record { addition = sumContext }



