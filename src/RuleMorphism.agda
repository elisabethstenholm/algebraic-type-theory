module RuleMorphism where

open import Prelude
open import Axioms
open import Homotopy.SetQuotient
open import Algebra.Wild.Semi

open import ContextWithTerms
open import DependentSortVocabulary
open import SequentStructure
open import SequentStructureMorphism
open import Rule


-- =============== Morphisms of rules ===============

record RuleMorphism
  ⦃ _ : FunExt ⦄
  ⦃ _ : AllSetQuotients ⦄
  {o a so₀ sa₀ i₀ so₁ sa₁ i₁ : Level}
  {𝒥 : DependentSortVocabulary {o} {a}}
  (r₀ : Rule 𝒥 so₀ sa₀ i₀)
  (r₁ : Rule 𝒥 so₁ sa₁ i₁)
  : Type (o ⊔ a ⊔ lsuc so₀ ⊔ lsuc sa₀ ⊔ lsuc i₀ ⊔ so₁ ⊔ sa₁ ⊔ lsuc i₁) where
  constructor mkRuleMorphism
  field
    baseContext : ContextWithTerms 𝒥 so₀ sa₀ i₀
    ruleMorphism : SequentStructureMorphism
                     (addContextWithTermsToSequentStructure baseContext (⋊ₛ r₀))
                     (SequentDependencyStructure.sequentStructure (Rule.rule r₁))
open RuleMorphism

