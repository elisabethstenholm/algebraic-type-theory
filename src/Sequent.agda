module Sequent where

open import Foundation.Axioms
open import Foundation
import Foundation.Structure.Wild.Semicategory as Semicategory
open Semicategory using (Semicategory)
open Semicategory.Semicategory
import Foundation.Structure.Categorical as Categorical
open Categorical using (Categorical)
import Foundation.Structure.Wild.Semifunctor as Semifunctor
open Semifunctor using (Semifunctor)
import Foundation.Structure.Semifunctorial as Semifunctorial
open import Foundation.HomotopyLevels.Semicategorical
open import Foundation.Structure.Wild.SeminaturalTransformation
open import Foundation.StructuredType
open import Foundation.Structure.Associativity using (∙-associative)
open import Foundation.Structure.Wild.SemiYoneda
open import Foundation.Structure.Wild.TypeSemicategory
open import Foundation.Structure.PreservesComposition
  using (PreservesComposition; preserves-composition)
open import Foundation.Structure.Semifunctorial using (Semifunctorial)
import Foundation.Structure.Wild.SeminaturalTransformation as SeminaturalTransformation
open Foundation.Structure.Wild.SeminaturalTransformation using (natural)
import Foundation.Structure.Natural as Natural
open import Foundation.Structure.Natural using (Natural)
open import Foundation.Structure.Composable using (Composable)
open import Foundation.Structure.Appliable using (Appliable)
open import Foundation.Structure.Identity using (Identity)

open import DependentSortVocabulary

record Context
  {o a : Level}
  (𝒥 : Semicategory o a)
  (i : Level)
  : Type (o ⊔ a ⊔ lsuc i) where
  constructor mkContext
  field
    semifunctor : Semifunctor 𝒥 (TypeSemicategory i)

module _ {o a i : Level} {𝒥 : Semicategory o a} where

  instance
    appliableOnObjectsContext : Appliable (Context 𝒥 i) (Ob 𝒥) (λ _ _ → Type i)
    appliableOnObjectsContext = record { function = λ Γ j → Context.semifunctor Γ ⟨ j ⟩ }

    appliableOnMorphismsContext : {j j' : Ob 𝒥} → Appliable (Context 𝒥 i) (Hom 𝒥 j j') (λ Γ _ → Γ ⟨ j ⟩ → Γ ⟨ j' ⟩)
    appliableOnMorphismsContext = record { function = λ Γ f → Context.semifunctor Γ ⟨ f ⟩ }

record ContextMorphism
  {o a i j : Level}
  {𝒥 : Semicategory o a}
  (Γ : Context 𝒥 i)
  (Δ : Context 𝒥 j)
  : Type (o ⊔ a ⊔ i ⊔ j) where
  constructor mkContextMorphism
  field
    component : (j : Ob 𝒥) → Γ ⟨ j ⟩ → Δ ⟨ j ⟩
    naturality : {j j' : Ob 𝒥} (f : Hom 𝒥 j j')
               → Δ ⟨ f ⟩ ∘ component j ＝ component j' ∘ Γ ⟨ f ⟩

infixl -10 _⇒_
_⇒_ : ∀ {o a i j} {𝒥 : Semicategory o a}
     → Context 𝒥 i → Context 𝒥 j → Type (o ⊔ a ⊔ i ⊔ j)
Γ ⇒ Δ = ContextMorphism Γ Δ

module _ {o a : Level} {𝒥 : Semicategory o a} where

  instance
    appliableContextMorphism : ∀ {i j} {Γ : Context 𝒥 i} {Δ : Context 𝒥 j}
                             → Appliable (ContextMorphism Γ Δ) (Ob 𝒥) (λ _ j → Γ ⟨ j ⟩ → Δ ⟨ j ⟩)
    appliableContextMorphism = record { function = λ ϵ → ContextMorphism.component ϵ }

    composableContext : Composable _ _ _ (Context 𝒥) ContextMorphism
    composableContext =
      record
        { composition = λ ϵ δ → record
            { component = λ j → δ ⟨ j ⟩ ∙ ϵ ⟨ j ⟩ 
            ; naturality = λ {j j'} f
                → ap (δ ⟨ j' ⟩ ∘_) (ContextMorphism.naturality ϵ f)
                ∙ ap (_∘ ϵ ⟨ j ⟩) (ContextMorphism.naturality δ f) } }

    identityContextMorphism : Identity _ _ _ (Context 𝒥) ContextMorphism
    identityContextMorphism =
      record
        { identity = record
            { component = λ j → id
            ; naturality = identity } }

𝒴 : ⦃ FunExt ⦄ → ∀ {o a} {𝒥 : Semicategory o a} (j : Ob 𝒥) → Context 𝒥 a
𝒴 {𝒥 = 𝒥} j = record { semifunctor = SemiCoYoneda 𝒥 j }

record Extension
  ⦃ _ : FunExt ⦄
  {o a i : Level}
  {𝒥 : Semicategory o a}
  (Γ : Context 𝒥 i)
  : Type (o ⊔ a ⊔ i) where
  constructor mkExtension
  field
    judgmentForm : Ob 𝒥
    arguments : 𝒴 judgmentForm ⇒ Γ

record Sequent
  ⦃ _ : FunExt ⦄
  {o a i : Level}
  (𝒥 : Semicategory o a)
  : Type (o ⊔ a ⊔ lsuc i) where
  constructor mkSequent
  field
    context : Context 𝒥 i
    extension : Extension context

infix 20 _⋊_
_⋊_ : ⦃ _ : FunExt ⦄
    → {o a i : Level} {𝒥 : Semicategory o a}
    → (Γ : Context 𝒥 i) → Extension Γ → Context 𝒥 (o ⊔ i)
_⋊_ {o} {a} {i} {𝒥} Γ ext =
  record { semifunctor = record
             { onObjects = onObjects
             ; semifunctorial = record
                 { mappable = record { map = onMorphisms }
                 ; preservesComposition = record
                     { preserves-composition = λ f g → funExt (preservesComposition~ f g) } } } }
  where
    open Semicategory.Reasoning 𝒥
    open Semifunctor.Reasoning (Context.semifunctor Γ)

    onObjects : Ob 𝒥 → Type (o ⊔ i)
    onObjects j = (Γ ⟨ j ⟩) + (j ＝ Extension.judgmentForm ext)

    onMorphisms : ∀ {j j'} → Hom 𝒥 j j' → onObjects j → onObjects j'
    onMorphisms f (inl x) = inl ((Γ ⟨ f ⟩) x)
    onMorphisms {j' = j'} f (inr refl) = inl ((Extension.arguments ext ⟨ j' ⟩) f)

    preservesComposition~ : ∀ {j j' j''} (f : Hom 𝒥 j j') (g : Hom 𝒥 j' j'')
                          → onMorphisms (g ∙ f) ~ onMorphisms g ∘ onMorphisms f
    preservesComposition~ f g (inl x) = ap (λ h → inl (h x)) (preserves-composition f g)
      where open Semicategory.Reasoning (TypeSemicategory i)
    preservesComposition~ f g (inr refl) = ap (λ h → inl (h f)) (sym (ContextMorphism.naturality (Extension.arguments ext) g))

ι : ⦃ _ : FunExt ⦄
  → {o a i : Level} {𝒥 : Semicategory o a}
  → {Γ : Context 𝒥 i} {ϵ : Extension Γ}
  → Γ ⇒ Γ ⋊ ϵ
ι = record
      { component = λ j → inl
      ; naturality = identity }

YonedaExtension : ⦃ _ : FunExt ⦄
                → {o a : Level} {𝒥 : Semicategory o a}
                → (j : Ob 𝒥)
                → Extension (𝒴 {𝒥 = 𝒥} j)
YonedaExtension j =
  record
    { judgmentForm = j
    ; arguments = identity }

𝒴⁺ : ⦃ _ : FunExt ⦄
     → {o a : Level} {𝒥 : Semicategory o a}
     → (j : Ob 𝒥)
     → Context 𝒥 (o ⊔ a)
𝒴⁺ j = 𝒴 j ⋊ YonedaExtension j

ext⁺ : ⦃ _ : FunExt ⦄
     → {o a i : Level} {𝒥 : Semicategory o a}
     → {Γ : Context 𝒥 i} (ϵ : Extension Γ)
     → 𝒴⁺ (Extension.judgmentForm ϵ) ⇒ Γ ⋊ ϵ
ext⁺ {𝒥 = 𝒥} {Γ = Γ} ϵ =
  record
    { component = component
    ; naturality = funExt ∘ naturality~ }
  where
    component : (j : Ob 𝒥) → (𝒴⁺ {𝒥 = 𝒥} (Extension.judgmentForm ϵ)) ⟨ j ⟩ → (Γ ⋊ ϵ) ⟨ j ⟩
    component j (inl x) = inl ((Extension.arguments ϵ ⟨ j ⟩) x)
    component j (inr refl) = inr refl

    naturality~ : {j j' : Ob 𝒥} (f : Hom 𝒥 j j')
                → (Γ ⋊ ϵ) ⟨ f ⟩ ∘ component j ~ component j' ∘ (𝒴⁺ {𝒥 = 𝒥} (Extension.judgmentForm ϵ)) ⟨ f ⟩
    naturality~ f (inl x) = ap (λ h → inl (h x)) (ContextMorphism.naturality (Extension.arguments ϵ) f)
    naturality~ f (inr refl) = refl
