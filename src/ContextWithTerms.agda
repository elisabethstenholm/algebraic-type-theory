module ContextWithTerms where

open import Prelude
open import Axioms
open import Homotopy.SetQuotient.Nominal
open import Structure.Associativity
open import Structure.Composable
open import Structure.Identity
open import Structure.PreservesComposition
open import Structure.Symmetric
open import Homotopy.StructuredType
open import Algebra.Wild.Semicategory
open import Algebra.Wild.Semifunctor
open Semicategory
open import Algebra.Wild.TruncatedTypeSemicategory
open import Homotopy.Equality
open import Homotopy.Levels
open import Foundation.Sum.Equivalence
open import Structure.Bimappable

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
open import Weakening.Sequent
open SequentDependencyStructure.SequentDependencyStructure


-- =============== Contexts with terms =================

record ContextWithTerms
  ⦃ _ : FunExt ⦄
  ⦃ _ : AllSetQuotients ⦄
  {o a : Level}
  (𝒥 : DependentSortVocabulary o a)
  (so sa i : Level)
  : Type (o ⊔ a ⊔ lsuc so ⊔ lsuc sa ⊔ lsuc i) where
  constructor mkContextWithTerms
  field
    contextWithTerms : SequentDependencyStructure 𝒥 so sa i (Context 𝒥 i) id
open ContextWithTerms


toContextWithTerms : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄ {o a i : Level} {𝒥 : DependentSortVocabulary o a}
                   → (so sa : Level) → Context 𝒥 i → ContextWithTerms 𝒥 so sa i
toContextWithTerms {i = i} {𝒥 = 𝒥} so sa Γ =
  mkContextWithTerms
    record
      { head = Γ
      ; sequentStructure = emptySequentStructure 𝒥 so sa i
      ; dependency = emptySemifunctor (hSet-Semicategory sa) so sa
      ; realiseDependency = λ ()
      ; coherenceRealisation = λ { {()} } }

emptyContextWithTerms : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄ {o a : Level} (𝒥 : DependentSortVocabulary o a)
                      → (so sa i : Level) → ContextWithTerms 𝒥 so sa i
emptyContextWithTerms 𝒥 so sa i = toContextWithTerms so sa (emptyContext 𝒥 i)


-- =============== Equality of contexts with terms ===============


record ContextWithTermsEquality
  ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a}
  (c₀ c₁ : ContextWithTerms 𝒥 so sa i)
  : Type (o ⊔ a ⊔ so ⊔ sa ⊔ lsuc i) where
  constructor mkContextWithTermsEquality
  field
    contextWithTerms≈ : SequentDependencyStructureEquality 
                          ContextEquivalence
                          id
                          (contextWithTerms c₀)
                          (contextWithTerms c₁)

module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a} where

  instance
    sameyContextWithTerms : Samey 𝟙₀ (λ _ → ContextWithTerms 𝒥 so sa i)
    sameyContextWithTerms = record { samey = ContextWithTermsEquality }

  private
    contextWithTermsTotalSpace-Contractible :
        (c₀ : ContextWithTerms 𝒥 so sa i)
      → Contractible (∑[ c₁ ∶ ContextWithTerms 𝒥 so sa i ] ContextWithTermsEquality c₀ c₁)
    contextWithTermsTotalSpace-Contractible c₀ =
      retract-Contractible toData fromData roundTrip
        (equality-Contractible ⦃ w = equalitySequentDependencyStructure
                                       {A-refl≈ = λ _ → identity}
                                       {A-total = contextTotalSpace-Contractible}
                                       {headContext≈-refl = λ _ _ _ → refl} ⦄
           (contextWithTerms c₀))
      where
        toData : (∑[ c₁ ∶ ContextWithTerms 𝒥 so sa i ] ContextWithTermsEquality c₀ c₁)
               → ∑[ d₁ ∶ SequentDependencyStructure 𝒥 so sa i (Context 𝒥 i) id ]
                   SequentDependencyStructureEquality ContextEquivalence id (contextWithTerms c₀) d₁
        toData (mkContextWithTerms d₁ , mkContextWithTermsEquality w) = d₁ , w

        fromData : (∑[ d₁ ∶ SequentDependencyStructure 𝒥 so sa i (Context 𝒥 i) id ]
                      SequentDependencyStructureEquality ContextEquivalence id (contextWithTerms c₀) d₁)
                 → ∑[ c₁ ∶ ContextWithTerms 𝒥 so sa i ] ContextWithTermsEquality c₀ c₁
        fromData (d₁ , w) = mkContextWithTerms d₁ , mkContextWithTermsEquality w

        roundTrip : fromData ∘ toData ~ id
        roundTrip (mkContextWithTerms d₁ , mkContextWithTermsEquality w) = refl

  instance
    equalityContextWithTerms : Equality 𝟙₀ (λ _ → ContextWithTerms 𝒥 so sa i)
    equalityContextWithTerms =
      record { characterisation =
                 fundamentalTheorem ContextWithTermsEquality
                   (λ c → record { contextWithTerms≈ =
                            refl≈ ⦃ w = equalitySequentDependencyStructure
                                          {A-refl≈ = λ _ → identity}
                                          {A-total = contextTotalSpace-Contractible}
                                          {headContext≈-refl = λ _ _ _ → refl} ⦄
                              {x = contextWithTerms c} })
                   contextWithTermsTotalSpace-Contractible }


