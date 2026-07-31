module SequentStructure where

open import Foundation
open import Foundation.Axioms
open import Foundation.Reasoning
open import Foundation.Structure.Wild.Semi
open Semicategory.Semicategory

open import Sequent

record SequentMorphism
  ⦃ _ : FunExt ⦄
  ⦃ _ : AllSetQuotients ⦄
  {o a i₁ i₂ : Level}
  {𝒥 : Semicategory o a}
  (s₁ : Sequent 𝒥 i₁)
  (s₂ : Sequent 𝒥 i₂)
  : Type (o ⊔ a ⊔ lsuc i₁ ⊔ lsuc i₂) where
  constructor mkSequentMorphism
  field
    sequentMorphism : ContextMorphism
                        (Sequent.context s₁ ⋊ Sequent.extensionOrCollapse s₁)
                        (Sequent.context s₂)
open SequentMorphism

module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄ {o a : Level} {𝒥 : Semicategory o a} where

  instance
    appliableSequentMorphism : ∀ {i₁ i₂} {s₁ : Sequent 𝒥 i₁} {s₂ : Sequent 𝒥 i₂}
                             → Appliable (SequentMorphism s₁ s₂) (Ob 𝒥)
                                 (λ _ j → Sequent.context s₁ ⋊ Sequent.extensionOrCollapse s₁ ⟨ j ⟩ → Sequent.context s₂ ⟨ j ⟩)
    appliableSequentMorphism = record { function = ContextMorphism.component ∘ sequentMorphism }

    composableSequentMorphism : Composable _ (Sequent 𝒥) SequentMorphism
    composableSequentMorphism =
      record
        { composition = λ {B = B} f g → record
          { sequentMorphism = sequentMorphism g ∙ →⋊ B ∙ sequentMorphism f } }

    associativeCompositionSequentMorphism : AssociativeComposition (SequentMorphism { 𝒥 = 𝒥 }) (λ _ _ → _＝_)
    associativeCompositionSequentMorphism =
      record
        { ⨾-associative = λ {B = B} {C = C} {f = f} {g = g} {h = h} → ap mkSequentMorphism
            (begin
              (sequentMorphism h ∙ →⋊ C) ∙ ((sequentMorphism g ∙ →⋊ B) ∙ sequentMorphism f)  ⟦ ∙-associative {g = sequentMorphism g ∙ →⋊ B} ⟧
              ((sequentMorphism h ∙ →⋊ C) ∙ (sequentMorphism g ∙ →⋊ B)) ∙ sequentMorphism f  ⟦ ap (_∙ sequentMorphism f) (∙-associative {g = sequentMorphism g}) ⟧
              (((sequentMorphism h ∙ →⋊ C) ∙ sequentMorphism g) ∙ →⋊ B) ∙ sequentMorphism f  ∎) }

    sequentSemicategorical : Semicategorical _ (Sequent 𝒥) SequentMorphism (λ _ _ → _＝_)
    sequentSemicategorical = record {}

SequentSemicategory : ⦃ _ : FunExt ⦄
                    → ⦃ _ : AllSetQuotients ⦄
                    → {o a : Level} (𝒥 : Semicategory o a) (i : Level)
                    → Semicategory (o ⊔ a ⊔ lsuc i) (o ⊔ a ⊔ lsuc i)
SequentSemicategory 𝒥 i = asSemicategory (Sequent 𝒥) SequentMorphism i

record SequentStructure
  ⦃ _ : FunExt ⦄
  ⦃ _ : AllSetQuotients ⦄
  {o a : Level}
  (𝒥 : Semicategory o a)
  (so sa i : Level)
  : Type (o ⊔ a ⊔ lsuc so ⊔ lsuc sa ⊔ lsuc i) where
  constructor mkSequentStructure
  field
    sequentDependency : Semicategory so sa
    sequent : Semifunctor (sequentDependency ᵒᵖ) (SequentSemicategory 𝒥 i)

