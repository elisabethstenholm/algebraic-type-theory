module Rule where

open import Prelude
open import Axioms
open import Homotopy.SetQuotient
open import Algebra.Wild.Semi

open import SequentStructure
open import SequentStructureExtension

record Rule
  ⦃ _ : FunExt ⦄
  ⦃ _ : AllSetQuotients ⦄
  {o a : Level}
  (𝒥 : Semicategory o a)
  (so sa i : Level)
  : Type (o ⊔ a ⊔ lsuc so ⊔ lsuc sa ⊔ lsuc i) where
  constructor mkRule
  field
    premises : SequentStructure 𝒥 so sa i
    extension : SequentStructureExtension premises
open Rule

-- =============== Morphisms of rules ===============

record RuleMorphism
  ⦃ _ : FunExt ⦄
  ⦃ _ : AllSetQuotients ⦄
  {o a so₀ sa₀ i₀ so₁ sa₁ i₁ : Level}
  {𝒥 : Semicategory o a}
  (r₀ : Rule 𝒥 so₀ sa₀ i₀)
  (r₁ : Rule 𝒥 so₁ sa₁ i₁)
  : Type (so₀ ⊔ sa₀ ⊔ so₁ ⊔ sa₁) where
  constructor mkRuleMorphism
  field
    ruleMorphism : SequentStructureMorphism (premises r₀ ⋊ₛ extension r₀) (premises r₁)
open RuleMorphism

