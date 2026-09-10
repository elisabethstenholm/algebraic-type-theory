module RuleSemicategory where

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
open import Weakening.Reassociation
open import Weakening.SequentStructureMorphism
open import RuleMorphism
open import RuleMorphism.Composition
open import RuleMorphism.Equality
open RuleMorphism.RuleMorphism


-- =============== Associativity of rule-morphism composition ===============

module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a}
  {r₀ r₁ r₂ r₃ : Rule 𝒥 so sa i} where

  opaque
    unfolding castSSM

    ⨾ᴿ-associative :
        (φ : RuleMorphism r₀ r₁) (ψ : RuleMorphism r₁ r₂) (χ : RuleMorphism r₂ r₃)
      → ((φ ⨾ᴿ ψ) ⨾ᴿ χ) ＝ (φ ⨾ᴿ (ψ ⨾ᴿ χ))
    ⨾ᴿ-associative φ ψ χ =
      sym (eq ⦃ equalityRuleMorphism ⦄
           {x = φ ⨾ᴿ (ψ ⨾ᴿ χ)} {y = (φ ⨾ᴿ ψ) ⨾ᴿ χ}
           (record
             { baseContext≈ =
                 ⧺ᶜ-assocEquality (baseContext χ) (baseContext ψ) (baseContext φ)
             ; ruleMorphism≈ = record
               { dependencyMorphism≈ = record
                   { onObjects≈ = λ
                       { (inl (inl (inl w))) → refl
                       ; (inl (inl (inr v))) → refl
                       ; (inl (inr u)) → refl
                       ; (inr c) → refl }
                   ; witness≈ =
                       (λ { (inl (inl (inl w))) (inl (inl (inl w'))) f → refl
                          ; (inl (inl (inr v))) (inl (inl (inr v'))) f → refl
                          ; (inl (inr u)) (inl (inr u')) f → refl
                          ; (inr c) (inr c') f → refl
                          ; (inl (inl (inr v))) (inl (inl (inl w))) f → refl
                          ; (inl (inr u)) (inl (inl (inl w))) f → refl
                          ; (inl (inr u)) (inl (inl (inr v))) f → refl
                          ; (inr c) (inl (inl (inl w))) f → refl
                          ; (inr c) (inl (inl (inr v))) f → refl
                          ; (inr c) (inl (inr u)) f → refl
                          ; (inl (inl (inl w))) (inl (inl (inr v))) ()
                          ; (inl (inl (inl w))) (inl (inr u)) ()
                          ; (inl (inl (inl w))) (inr c) ()
                          ; (inl (inl (inr v))) (inl (inr u)) ()
                          ; (inl (inl (inr v))) (inr c) ()
                          ; (inl (inr u)) (inr c) () })
                     , (λ A B E g h →
                          allEqual ⦃ ＝-isLevel ⦃ SequentStructure.dependency-Hom-isSet
                                                    (SequentDependencyStructure.sequentStructure (Rule.rule r₃)) _ _ ⦄ ⦄ _ _) }
               ; sequentEquivalence≈ = λ
                   { (inl (inl (inl w))) →
                       record { contextEquivalence≈ = record { morphism≈ =
                         record { component≈ = λ j → refl } } }
                   ; (inl (inl (inr v))) →
                       record { contextEquivalence≈ = record { morphism≈ =
                         record { component≈ = λ j → funExt (λ
                           { (inl h) → refl ; (inr zz) → refl }) } } }
                   ; (inl (inr u)) →
                       record { contextEquivalence≈ = record { morphism≈ =
                         record { component≈ = λ j → funExt (λ
                           { (inl (inl h)) → refl ; (inl (inr h')) → refl ; (inr zz) → refl }) } } }
                   ; (inr c) →
                       record { contextEquivalence≈ = record { morphism≈ =
                         record { component≈ = λ j → funExt (λ
                           { (inl (inl (inl h))) → refl
                           ; (inl (inl (inr h'))) → refl
                           ; (inl (inr h'')) → refl
                           ; (inr zz) → refl }) } } } } } }))


-- =============== The semicategory of rules ===============

RuleSemicategory : ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
                 → {o a : Level} (𝒥 : DependentSortVocabulary o a) (so sa i : Level)
                 → Semicategory (o ⊔ a ⊔ lsuc so ⊔ lsuc sa ⊔ lsuc i)
                                (o ⊔ a ⊔ lsuc so ⊔ lsuc sa ⊔ lsuc i)
RuleSemicategory 𝒥 so sa i =
  record
    { Ob = Rule 𝒥 so sa i
    ; Hom = RuleMorphism
    ; semicategorical =
        record
          { composable = record { composition = _⨾ᴿ_ }
          ; associativeComposition =
              record { ⨾-associative = λ {A} {B} {C} {D} {f} {g} {h} →
                ⨾ᴿ-associative f g h } } }
