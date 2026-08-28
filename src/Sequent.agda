module Sequent where

open import Prelude
open import Axioms
open import Homotopy.SetQuotient
open import Structure.Associativity
open import Structure.Composable
open import Structure.Identity
open import Structure.Reasoning
open import Homotopy.StructuredType
open import Syntax.Arrowable
open import Algebra.Wild.Semi
open Semicategory.Semicategory

open import DependentSortVocabulary
open import Context


-- ================ Sequents ===============

record Sequent
  ⦃ _ : FunExt ⦄
  {o a : Level}
  (𝒥 : DependentSortVocabulary o a)
  (i : Level)
  : Type (o ⊔ a ⊔ lsuc i) where
  constructor mkSequent
  field
    context : Context 𝒥 i
    extensionOrCollapse : ExtensionOrCollapse context
open Sequent

module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a i : Level} {𝒥 : DependentSortVocabulary o a} where

  extendedContext : Sequent 𝒥 i → Context 𝒥 (o ⊔ i)
  extendedContext s = Sequent.context s ⋊ Sequent.extensionOrCollapse s

  ⋊ₑₛ : Sequent 𝒥 i → Context 𝒥 (o ⊔ i)
  ⋊ₑₛ = extendedContext

  →⋊ : (s : Sequent 𝒥 i) → Sequent.context s ⇒ extendedContext s
  →⋊ (mkSequent context (extend x)) = ι
  →⋊ (mkSequent context (collapse x)) = σ


-- ============= Sequent morphisms ==============

record SequentMorphism
  ⦃ _ : FunExt ⦄
  ⦃ _ : AllSetQuotients ⦄
  {o a i₁ i₂ : Level}
  {𝒥 : DependentSortVocabulary o a}
  (s₁ : Sequent 𝒥 i₁)
  (s₂ : Sequent 𝒥 i₂)
  : Type (o ⊔ a ⊔ lsuc i₁ ⊔ lsuc i₂) where
  constructor mkSequentMorphism
  field
    sequentMorphism : ContextMorphism (extendedContext s₁) (extendedContext s₂)
open SequentMorphism


module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄ {o a : Level} {𝒥 : DependentSortVocabulary o a} where

  instance
    sequentsAreArrowable : Arrowable Level Level (Sequent 𝒥) (λ i → Type i)
                             (λ i₁ i₂ → o ⊔ a ⊔ lsuc i₁ ⊔ lsuc i₂)
    sequentsAreArrowable = record { arrow = SequentMorphism }

    appliableSequentMorphism : ∀ {i₁ i₂} {s₁ : Sequent 𝒥 i₁} {s₂ : Sequent 𝒥 i₂}
                             → Appliable (SequentMorphism s₁ s₂) (type (Judgment 𝒥))
                                 (λ _ j → ⌞ (extendedContext s₁) ⟨ j ⟩ ⌟ → ⌞ (extendedContext s₂) ⟨ j ⟩ ⌟)
    appliableSequentMorphism = record { function = ContextMorphism.component ∘ sequentMorphism }

    composableSequentMorphism : Composable _ (Sequent 𝒥) SequentMorphism
    composableSequentMorphism =
      record
        { composition = λ {B = B} f g → record
          { sequentMorphism = sequentMorphism g  ∙ sequentMorphism f } }

    associativeCompositionSequentMorphism : AssociativeComposition (SequentMorphism { 𝒥 = 𝒥 }) (λ _ _ → _＝_)
    associativeCompositionSequentMorphism =
      record
        { ⨾-associative = λ {B = B} {C = C} {f = f} {g = g} {h = h} → ap mkSequentMorphism
          (begin
            sequentMorphism h ∙ (sequentMorphism g ∙ sequentMorphism f)  ⟪ ∙-associative {g = sequentMorphism g} ⟫
            (sequentMorphism h ∙ sequentMorphism g) ∙ sequentMorphism f  ∎) }

    sequentSemicategorical : Semicategorical _ (Sequent 𝒥) SequentMorphism (λ _ _ → _＝_)
    sequentSemicategorical = record {}

SequentSemicategory : ⦃ _ : FunExt ⦄
                    → ⦃ _ : AllSetQuotients ⦄
                    → {o a : Level} (𝒥 : DependentSortVocabulary o a) (i : Level)
                    → Semicategory (o ⊔ a ⊔ lsuc i) (o ⊔ a ⊔ lsuc i)
SequentSemicategory 𝒥 i = asSemicategory (Sequent 𝒥) SequentMorphism i


-- =================== Sequent equivalences ===================

-- A sequent equivalence is an equivalence of sequents up to renaming
record SequentEquivalence
  ⦃ _ : FunExt ⦄
  ⦃ _ : AllSetQuotients ⦄
  {o a i₀ i₁ : Level}
  {𝒥 : DependentSortVocabulary o a}
  (s₀ : Sequent 𝒥 i₀)
  (s₁ : Sequent 𝒥  i₁)
  : Type (o ⊔ a ⊔ lsuc i₀ ⊔ lsuc i₁ ) where
  constructor mkStrictSequentEquivalence
  field
    contextEquivalence : Sequent.context s₀ ≈ Sequent.context s₁
    extensionOrCollapseEquality : mapExtensionOrCollapse
                                    (ContextEquivalence.morphism contextEquivalence)
                                    (Sequent.extensionOrCollapse s₀)
                                ≈ Sequent.extensionOrCollapse s₁

module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄ {o a : Level} {𝒥 : DependentSortVocabulary o a} where

  equivalenceMorphism : {i₀ i₁ : Level} {s₀ : Sequent 𝒥 i₀} {s₁ : Sequent 𝒥 i₁}
                      → SequentEquivalence s₀ s₁ → Sequent.context s₀ ⇒ Sequent.context s₁
  equivalenceMorphism = ContextEquivalence.morphism ∘ SequentEquivalence.contextEquivalence

  toSequentMorphism : {i₀ i₁ : Level} {s₀ : Sequent 𝒥 i₀} {s₁ : Sequent 𝒥 i₁}
                    → SequentEquivalence s₀ s₁ → SequentMorphism s₀ s₁
  toSequentMorphism {s₀ = s₀} {s₁ = s₁} e =
    record
      { sequentMorphism =
          map⋊ (equivalenceMorphism e)
               (Sequent.extensionOrCollapse s₀) (Sequent.extensionOrCollapse s₁)
               (SequentEquivalence.extensionOrCollapseEquality e) }

  sequentEquivalence-⨾ : {i₀ i₁ i₂ : Level} {s₀ : Sequent 𝒥 i₀} {s₁ : Sequent 𝒥 i₁} {s₂ : Sequent 𝒥 i₂}
                       → SequentEquivalence s₀ s₁ → SequentEquivalence s₁ s₂ → SequentEquivalence s₀ s₂
  sequentEquivalence-⨾ {s₀ = s₀} {s₁ = s₁} {s₂ = s₂} e₀ e₁ =
    record
      { contextEquivalence = SequentEquivalence.contextEquivalence e₀ ⨾ SequentEquivalence.contextEquivalence e₁
      ; extensionOrCollapseEquality =
          mapExtensionOrCollapse-⨾ (equivalenceMorphism e₀) (equivalenceMorphism e₁)
                                   (Sequent.extensionOrCollapse s₀)
                                   (Sequent.extensionOrCollapse s₁)
                                   (Sequent.extensionOrCollapse s₂)
                                   (SequentEquivalence.extensionOrCollapseEquality e₀)
                                   (SequentEquivalence.extensionOrCollapseEquality e₁) }

  sequentEquivalence-identity : {i : Level} {s : Sequent 𝒥 i} → SequentEquivalence s s
  sequentEquivalence-identity {s = s} =
    record
      { contextEquivalence = identity
      ; extensionOrCollapseEquality = mapExtensionOrCollapse-identity (Sequent.extensionOrCollapse s) }

  instance
    composableSequentEquivalence : Composable _ (Sequent 𝒥) SequentEquivalence
    composableSequentEquivalence = record { composition = sequentEquivalence-⨾ }

    identitySequentEquivalence : Identity _ (Sequent 𝒥) SequentEquivalence
    identitySequentEquivalence = record { identity = sequentEquivalence-identity }

  toSequentMorphism-⨾ : {i₀ i₁ i₂ : Level} {s₀ : Sequent 𝒥 i₀} {s₁ : Sequent 𝒥 i₁} {s₂ : Sequent 𝒥 i₂}
                        (e₀ : SequentEquivalence s₀ s₁) (e₁ : SequentEquivalence s₁ s₂)
                      → toSequentMorphism (e₀ ⨾ e₁) ＝ toSequentMorphism e₀ ⨾ toSequentMorphism e₁
  toSequentMorphism-⨾ {s₀ = s₀} {s₁ = s₁} {s₂ = s₂} e₀ e₁ =
    ap mkSequentMorphism
       (map⋊-⨾ (equivalenceMorphism e₀) (equivalenceMorphism e₁)
               (Sequent.extensionOrCollapse s₀)
               (Sequent.extensionOrCollapse s₁)
               (Sequent.extensionOrCollapse s₂)
               (SequentEquivalence.extensionOrCollapseEquality e₀)
               (SequentEquivalence.extensionOrCollapseEquality e₁))
