module Sequent where

open import Prelude
open import Axioms
open import Homotopy.SetQuotient
open import Structure.Associativity
open import Structure.Composable
open import Structure.Reasoning
open import Algebra.Wild.Semi
open Semicategory.Semicategory

open import Context


-- ================ Sequents ===============

record Sequent
  ⦃ _ : FunExt ⦄
  {o a : Level}
  (𝒥 : Semicategory o a)
  (i : Level)
  : Type (o ⊔ a ⊔ lsuc i) where
  constructor mkSequent
  field
    context : Context 𝒥 i
    extensionOrCollapse : ExtensionOrCollapse context

→⋊ : ⦃ _ : FunExt ⦄
   → ⦃ _ : AllSetQuotients ⦄
   → {o a i : Level} {𝒥 : Semicategory o a}
   → (s : Sequent 𝒥 i)
   → Sequent.context s ⇒ Sequent.context s ⋊ Sequent.extensionOrCollapse s
→⋊ (mkSequent context (extend x)) = ι
→⋊ (mkSequent context (collapse x)) = σ


-- ============= Sequent morphisms ==============

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
                                 (λ _ j → (Sequent.context s₁ ⋊ Sequent.extensionOrCollapse s₁) ⟨ j ⟩ → Sequent.context s₂ ⟨ j ⟩)
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
            sequentMorphism h ∙ (→⋊ C ∙ (sequentMorphism g ∙ (→⋊ B ∙ sequentMorphism f)))  ⟪ ap (sequentMorphism h ∙_) (∙-associative {g = sequentMorphism g}) ⟫
            sequentMorphism h ∙ ((→⋊ C ∙ sequentMorphism g) ∙ (→⋊ B ∙ sequentMorphism f))  ⟪ ∙-associative {g = →⋊ C ∙ sequentMorphism g} ⟫
            (sequentMorphism h ∙ (→⋊ C ∙ sequentMorphism g)) ∙ (→⋊ B ∙ sequentMorphism f)  ∎) }

    sequentSemicategorical : Semicategorical _ (Sequent 𝒥) SequentMorphism (λ _ _ → _＝_)
    sequentSemicategorical = record {}

SequentSemicategory : ⦃ _ : FunExt ⦄
                    → ⦃ _ : AllSetQuotients ⦄
                    → {o a : Level} (𝒥 : Semicategory o a) (i : Level)
                    → Semicategory (o ⊔ a ⊔ lsuc i) (o ⊔ a ⊔ lsuc i)
SequentSemicategory 𝒥 i = asSemicategory (Sequent 𝒥) SequentMorphism i
