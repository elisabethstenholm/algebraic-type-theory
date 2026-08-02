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

data EmptyOb (so : Level) : Type so where

EmptyHom' : {so : Level} (sa : Level) → EmptyOb so → EmptyOb so → Type sa
EmptyHom' sa () ()

data EmptyHom {so : Level} (sa : Level) (x y : EmptyOb so) : Type sa where
  emptyHom : EmptyHom' sa x y → EmptyHom sa x y

emptySemicategory : (so sa : Level) → Semicategory so sa
emptySemicategory so sa =
  record
    { Ob = EmptyOb so
    ; Hom = EmptyHom sa
    ; semicategorical = record
      { composable = record { composition = λ { {A = ()} _ _ } }
      ; associativeComposition = record { ⨾-associative = λ { {A = ()} } } } }

module _ {co ca : Level} (𝒞 : Semicategory co ca) where

  open Semicategory.Reasoning 𝒞

  emptySemifunctorOnObjects : {so : Level} → EmptyOb so → Ob 𝒞
  emptySemifunctorOnObjects ()

  emptySemifunctor : (so sa : Level) → Semifunctor (emptySemicategory so sa ᵒᵖ) 𝒞
  emptySemifunctor so sa =
    record
      { onObjects = emptySemifunctorOnObjects
      ; semifunctorial = record
        { mappable = record { map = λ { {A = ()} } }
        ; preservesComposition = record { preserves-composition = λ { {A = ()} } } } }

emptySequentStructure : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄ {o a : Level}
                      → (𝒥 : Semicategory o a) (so sa i : Level)
                      → SequentStructure 𝒥 so sa i
SequentStructure.sequentDependency (emptySequentStructure 𝒥 so sa i) = emptySemicategory so sa
SequentStructure.sequent (emptySequentStructure 𝒥 so sa i) = emptySemifunctor (SequentSemicategory 𝒥 i) so sa
