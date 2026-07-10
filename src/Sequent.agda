module Sequent where

open import Foundation
open import Foundation.Axioms
open import Foundation.Equality
open import Foundation.Equality.StructureIdentity
open import Foundation.DependentFunction.Equivalence
open import Foundation.DependentPair.Equivalence
open import Foundation.HomotopyLevels
open import Foundation.Reasoning
open import Foundation.StructuredMap
open import Foundation.Structure.Whiskerable
open import Foundation.Structure.Wild.Semi
open Semicategory.Semicategory
open import Foundation.Structure.Wild.TypeSemicategory
open import Foundation.Structure.Wild.SemiYoneda
open import Foundation.SetQuotient


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
    appliableOnObjectsContext = record { function = λ Γ j₀ → Context.semifunctor Γ ⟨ j₀ ⟩ }

    appliableOnMorphismsContext : {j₀ j₁ : Ob 𝒥} → Appliable (Context 𝒥 i) (Hom 𝒥 j₀ j₁) (λ Γ _ → Γ ⟨ j₀ ⟩ → Γ ⟨ j₁ ⟩)
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
    natural : {j₀ j₁ : Ob 𝒥} (f : Hom 𝒥 j₀ j₁)
            → Δ ⟨ f ⟩ ∘ component j₀ ＝ component j₁ ∘ Γ ⟨ f ⟩

ContextMorphism≃Σ :
    ∀ {o a i j} {𝒥 : Semicategory o a} {Γ : Context 𝒥 i} {Δ : Context 𝒥 j}
  → ContextMorphism Γ Δ
    ≃ ∑[ ϵ ∶ ((j : Ob 𝒥) → Γ ⟨ j ⟩ → Δ ⟨ j ⟩) ]
        ({j₀ j₁ : Ob 𝒥} (f : Hom 𝒥 j₀ j₁) → Δ ⟨ f ⟩ ∘ ϵ j₀ ＝ ϵ j₁ ∘ Γ ⟨ f ⟩)
ContextMorphism≃Σ .there ε =
  ContextMorphism.component ε , ContextMorphism.natural ε
ContextMorphism≃Σ .section .sectionBack (component , nat) =
  record { component = component ; natural = nat }
ContextMorphism≃Σ .section .isSection _ = refl
ContextMorphism≃Σ .retraction .retractionBack (component , nat) =
  record { component = component ; natural = nat }
ContextMorphism≃Σ .retraction .isRetraction _ = refl

-- A natural transformation is a structured map whose underlying datum is its
-- component family, a *dependent* map `(A : Ob C) → Hom D (Γ A) (Δ A)`: `ε [ A ]`
-- is the component at `A`, and `structureOf ε` recovers the naturality witness.
instance
  ContextMorphism-isStructuredMap :
    ∀ {o a i j} {𝒥 : Semicategory o a} {Γ : Context 𝒥 i} {Δ : Context 𝒥 j}
    → StructuredMap (ContextMorphism Γ Δ)
  ContextMorphism-isStructuredMap {o = o}
    .StructuredMap.iₗ = o
  ContextMorphism-isStructuredMap {o = o} {i = i} {j = j}
    .StructuredMap.jₗ = i ⊔ j
  ContextMorphism-isStructuredMap {o = o} {a = a}{i = i} {j = j}
    .StructuredMap.kₗ = o ⊔ a ⊔ i ⊔ j
  ContextMorphism-isStructuredMap {𝒥 = 𝒥}
    .StructuredMap.Domain = Ob 𝒥
  ContextMorphism-isStructuredMap {𝒥 = 𝒥} {Γ = Γ} {Δ = Δ}
    .StructuredMap.Codomain j = Γ ⟨ j ⟩ → Δ ⟨ j ⟩
  ContextMorphism-isStructuredMap {𝒥 = 𝒥} {Γ = Γ} {Δ = Δ}
    .StructuredMap.Structure ϵ = {j₀ j₁ : Ob 𝒥} (f : Hom 𝒥 j₀ j₁) → Δ ⟨ f ⟩ ∘ ϵ j₀ ＝ ϵ j₁ ∘ Γ ⟨ f ⟩
  ContextMorphism-isStructuredMap
    .StructuredMap.structured = ContextMorphism≃Σ

infixl -10 _⇒_
_⇒_ : ∀ {o a i j} {𝒥 : Semicategory o a}
     → Context 𝒥 i → Context 𝒥 j → Type (o ⊔ a ⊔ i ⊔ j)
Γ ⇒ Δ = ContextMorphism Γ Δ

record ContextMorphismEquality
  {o a i j :  Level}
  {𝒥 : Semicategory o a}
  {Γ : Context 𝒥 i} {Δ : Context 𝒥 j}
  (α β : Γ ⇒ Δ)
  : Type (o ⊔ a ⊔ i ⊔ j) where
  constructor mkContextMorphismEquality
  field
    component≈ : ContextMorphism.component α ~ ContextMorphism.component β
    natural≈   : {j₀ j₁ : Ob 𝒥} (h : Hom 𝒥 j₀ j₁)
               → ContextMorphism.natural α h ⨾ ((Γ ⟨ h ⟩) ◁ component≈ j₁)
               ＝ (component≈ j₀ ▷ Δ ⟨ h ⟩) ⨾ ContextMorphism.natural β h

open ContextMorphismEquality

-- Characterisation of the identity type on ContextMorphism

module _ {o a i j} {𝒥 : Semicategory o a} {Γ : Context 𝒥 i} {Δ : Context 𝒥 j} where

  private
    Component : Type (o ⊔ i ⊔ j)
    Component = (j : Ob 𝒥) → Γ ⟨ j ⟩ → Δ ⟨ j ⟩

  naturalWitness-refl : {c : Component} (n : {j₀ j₁ : Ob 𝒥} (f : Hom 𝒥 j₀ j₁) → Δ ⟨ f ⟩ ∘ c j₀ ＝ c j₁ ∘ Γ ⟨ f ⟩)
                      → {j₀ j₁ : Ob 𝒥} (h : Hom 𝒥 j₀ j₁) → n h ⨾ refl ＝ n h
  naturalWitness-refl n h = ∙-unitₗ

  ContextMorphismEquality≃Σ : {α β : Γ ⇒ Δ}
    → ContextMorphismEquality α β
      ≃ (∑[ ϵ ∶ ContextMorphism.component α ~ ContextMorphism.component β ]
           ({j₀ j₁ : Ob 𝒥} (h : Hom 𝒥 j₀ j₁)
               → ContextMorphism.natural α h ⨾ (Γ ⟨ h ⟩ ◁ ϵ j₁)
               ＝ (ϵ j₀ ▷ Δ ⟨ h ⟩) ⨾ ContextMorphism.natural β h))
  ContextMorphismEquality≃Σ .there w = (component≈ w , natural≈ w)
  ContextMorphismEquality≃Σ .section .sectionBack (p , q) = record { component≈ = p; natural≈ = q }
  ContextMorphismEquality≃Σ .section .isSection _ = refl
  ContextMorphismEquality≃Σ .retraction .retractionBack (p , q) = record { component≈ = p; natural≈ = q }
  ContextMorphismEquality≃Σ .retraction .isRetraction _ = refl

  module _ ⦃ _ : FunExt ⦄ where

    private
      naturalWitness-Contractible : {c : Component} (n : {j₀ j₁ : Ob 𝒥} (f : Hom 𝒥 j₀ j₁) → Δ ⟨ f ⟩ ∘ c j₀ ＝ c j₁ ∘ Γ ⟨ f ⟩)
        → Contractible (∑[ n' ∶ ({j₀ j₁ : Ob 𝒥} (f : Hom 𝒥 j₀ j₁) → Δ ⟨ f ⟩ ∘ c j₀ ＝ c j₁ ∘ Γ ⟨ f ⟩) ]
                         ({j₀ j₁ : Ob 𝒥} (h : Hom 𝒥 j₀ j₁) → n h ⨾ refl ＝ n' h))
      naturalWitness-Contractible {c} n =
        ≃-Contractible
          (sym (equiv-∑
                 (equiv-Π (λ j → equiv-implicit-Π) ∙ equiv-implicit-Π)
                 (λ g → equiv-Π (λ j → equiv-implicit-Π) ∙ equiv-implicit-Π)))
          (Π-witness-Contractible _ λ j₀ →
           Π-witness-Contractible _ λ j₁ →
           Π-witness-Contractible _ λ h →
           singleton-Contractible (n h ⨾ refl))

    instance
      equalityContextMorphism : Equality (Γ ⇒ Δ)
      equalityContextMorphism =
        mapWitness ContextMorphismEquality
          (transferEquality ContextMorphism≃Σ
            (∑-structureEquality
              _~_
              (λ c → ~-refl)
              (λ nε p nδ → {j₀ j₁ : Ob 𝒥} (h : Hom 𝒥 j₀ j₁) → nε h ⨾ (Γ ⟨ h ⟩ ◁ p j₁) ＝ (p j₀ ▷ Δ ⟨ h ⟩) ⨾ nδ h)
              naturalWitness-refl
              homotopy-Contractible
              naturalWitness-Contractible))
          ContextMorphismEquality≃Σ

module _ ⦃ _ : FunExt ⦄ {o a : Level} {𝒥 : Semicategory o a} where

  instance
    appliableContextMorphism : ∀ {i j} {Γ : Context 𝒥 i} {Δ : Context 𝒥 j}
                             → Appliable (ContextMorphism Γ Δ) (Ob 𝒥) (λ _ j → Γ ⟨ j ⟩ → Δ ⟨ j ⟩)
    appliableContextMorphism = record { function = λ ϵ → ContextMorphism.component ϵ }

    composableContextMorphism : Composable _ (Context 𝒥) ContextMorphism
    composableContextMorphism =
      record
        { composition = λ ϵ δ → record
            { component = λ j → δ ⟨ j ⟩ ∙ ϵ ⟨ j ⟩ 
            ; natural = λ {j₀ j₁} f
                → ap (δ ⟨ j₁ ⟩ ∘_) (ContextMorphism.natural ϵ f)
                ∙ ap (_∘ ϵ ⟨ j₀ ⟩) (ContextMorphism.natural δ f) } }

    associativeCompositionContextMorphism : AssociativeComposition (ContextMorphism { 𝒥 = 𝒥 }) (λ _ _ → _＝_)
    associativeCompositionContextMorphism =
      record
        { ⨾-associative = λ {A = A} {B = B} {C = C} {D = D} {f = α} {g = β} {h = γ} →
            eq (record
                 { component≈ = identity
                   ; natural≈ = λ {j₀} {j₁} f →
                       lemma (α ⟨ j₀ ⟩) (α ⟨ j₁ ⟩) (β ⟨ j₀ ⟩) (β ⟨ j₁ ⟩) (γ ⟨ j₀ ⟩) (γ ⟨ j₁ ⟩)
                             (A ⟨ f ⟩) (B ⟨ f ⟩) (C ⟨ f ⟩) (D ⟨ f ⟩)
                             (α ⟨ j₁ ⟩ ∘ A ⟨ f ⟩) refl
                             (D ⟨ f ⟩ ∘ γ ⟨ j₀ ⟩) refl
                             (ContextMorphism.natural α f)
                             (ContextMorphism.natural β f)
                             (ContextMorphism.natural γ f)
                       ∙ ∙-unitₗ }) }
      where
        lemma : ∀ {k l m n} {Aj₀ Aj₁ : Type k} {Bj₀ Bj₁ : Type l}
              → {Cj₀ Cj₁ : Type m} {Dj₀ Dj₁ : Type n}
              → (αj₀ : Aj₀ → Bj₀) (αj₁ : Aj₁ → Bj₁)
              → (βj₀ : Bj₀ → Cj₀) (βj₁ : Bj₁ → Cj₁)
              → (γj₀ : Cj₀ → Dj₀) (γj₁ : Cj₁ → Dj₁)
              → (Af : Aj₀ → Aj₁) (Bf : Bj₀ → Bj₁)
              → (Cf : Cj₀ → Cj₁) (Df : Dj₀ → Dj₁)
              → (αj₁Af : Aj₀ → Bj₁)
              → (αj₁Af= : αj₁ ∘ Af ＝ αj₁Af)
              → (Dfγj₀ : Cj₀ → Dj₁)
              → (Dfγj₀= : Df ∘ γj₀ ＝ Dfγj₀)
              → (nα : Bf ∘ αj₀ ＝ αj₁Af)
              → (nβ : Cf ∘ βj₀ ＝ βj₁ ∘ Bf)
              → (nγ : Dfγj₀ ＝ γj₁ ∘ Cf)
              → (ap (_∘ (βj₀ ∘ αj₀)) nγ) ⨾ (ap (γj₁ ∘_) ((ap (_∘ αj₀) nβ) ⨾ (ap (βj₁ ∘_) nα)))
                ＝ (ap (_∘ αj₀) ((ap (_∘ βj₀) nγ) ⨾ (ap (γj₁ ∘_) nβ))) ⨾ (ap ((γj₁ ∘ βj₁) ∘_) nα)
        lemma αj₀ _ _ _ _ γj₁ _ _ _ _ _ _ _ _ refl nβ refl =
          begin
            ap (γj₁ ∘_) ((ap (_∘ αj₀) nβ) ⨾ refl)    ⟦ ap (ap (γj₁ ∘_)) ∙-unitₗ ⟧
            ap (γj₁ ∘_) (ap (_∘ αj₀) nβ)            ⟦ sym (ap-∘ (γj₁ ∘_) (_∘ αj₀) nβ) ⟧
            ap (λ g → γj₁ ∘ g ∘ αj₀) nβ             ⟦ ap-∘ (_∘ αj₀) (γj₁ ∘_) nβ ⟧
            ap (_∘ αj₀) (ap (γj₁ ∘_) nβ)            ⟦ sym ∙-unitₗ ⟧
            (ap (_∘ αj₀) (ap (γj₁ ∘_) nβ)) ⨾ refl    ∎

    identityContextMorphism : Identity _ (Context 𝒥) ContextMorphism
    identityContextMorphism =
      record
        { identity = record
            { component = λ j → id
            ; natural = identity } }

𝒴 : ⦃ _ : FunExt ⦄ {o a : Level} {𝒥 : Semicategory o a} (j : Ob 𝒥) → Context 𝒥 a
𝒴 {𝒥 = 𝒥} j = record { semifunctor = SemiCoYoneda 𝒥 j }

𝒴⁺⁺ : ⦃ _ : FunExt ⦄ {o a : Level} {𝒥 : Semicategory o a} (j : Ob 𝒥) → Context 𝒥 (o ⊔ a)
𝒴⁺⁺ {o} {a} {𝒥} j = 
  record { semifunctor = record
           { onObjects = onObjects
           ; semifunctorial = record
               { mappable = record { map = onMorphisms }
               ; preservesComposition = record
                   { preserves-composition = λ f g → funExt (preservesComposition~ f g) } } } }
  where
  open Semicategory.Reasoning 𝒥

  onObjects : Ob 𝒥 → Type (o ⊔ a)
  onObjects j₁ = Hom 𝒥 j j₁ + ((j₁ ＝ j) + (j₁ ＝ j))

  onMorphisms : ∀ {j₁ j₂} → Hom 𝒥 j₁ j₂ → onObjects j₁ → onObjects j₂
  onMorphisms f (inl g) = inl (f ∙ g)
  onMorphisms f (inr (inl refl)) = inl f
  onMorphisms f (inr (inr refl)) = inl f

  preservesComposition~ : ∀ {j₁ j₂ j₃} (f : Hom 𝒥 j₁ j₂) (g : Hom 𝒥 j₂ j₃)
                        → onMorphisms (g ∙ f) ~ onMorphisms g ∘ onMorphisms f
  preservesComposition~ f g (inl h) = ap inl (sym ∙-associative)
  preservesComposition~ f g (inr (inl refl)) = refl
  preservesComposition~ f g (inr (inr refl)) = refl

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

record Collapse
  ⦃ _ : FunExt ⦄
  {o a i : Level}
  {𝒥 : Semicategory o a}
  (Γ : Context 𝒥 i)
  : Type (o ⊔ a ⊔ i) where
  constructor mkCollapse
  field
    judgmentForm : Ob 𝒥
    arguments : 𝒴⁺⁺ judgmentForm ⇒ Γ

data ExtensionOrCollapse
  ⦃ _ : FunExt ⦄
  {o a i : Level}
  {𝒥 : Semicategory o a}
  (Γ : Context 𝒥 i)
  : Type (o ⊔ a ⊔ i) where
  extend : Extension Γ → ExtensionOrCollapse Γ
  collapse : Collapse Γ → ExtensionOrCollapse Γ

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

infix 20 _⋊ₑ_
_⋊ₑ_ : ⦃ _ : FunExt ⦄
    → {o a i : Level} {𝒥 : Semicategory o a}
    → (Γ : Context 𝒥 i) → Extension Γ → Context 𝒥 (o ⊔ i)
_⋊ₑ_ {o} {a} {i} {𝒥} Γ ext =
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

    onMorphisms : ∀ {j₀ j₁} → Hom 𝒥 j₀ j₁ → onObjects j₀ → onObjects j₁
    onMorphisms f (inl x) = inl ((Γ ⟨ f ⟩) x)
    onMorphisms {j₁ = j₁} f (inr refl) = inl ((Extension.arguments ext ⟨ j₁ ⟩) f)

    preservesComposition~ : ∀ {j₀ j₁ j₂} (f : Hom 𝒥 j₀ j₁) (g : Hom 𝒥 j₁ j₂)
                          → onMorphisms (g ∙ f) ~ onMorphisms g ∘ onMorphisms f
    preservesComposition~ f g (inl x) = ap (λ h → inl (h x)) (preserves-composition f g)
      where open Semicategory.Reasoning (TypeSemicategory i)
    preservesComposition~ f g (inr refl) = ap (λ h → inl (h f)) (sym (ContextMorphism.natural (Extension.arguments ext) g))

ι : ⦃ _ : FunExt ⦄
  → {o a i : Level} {𝒥 : Semicategory o a}
  → {Γ : Context 𝒥 i} {ϵ : Extension Γ}
  → Γ ⇒ Γ ⋊ₑ ϵ
ι = record
      { component = λ j → inl
      ; natural = identity }

module _ ⦃ _ : FunExt ⦄ {o a : Level} {𝒥 : Semicategory o a} where

  YonedaExtension : (j : Ob 𝒥) → Extension (𝒴 {𝒥 = 𝒥} j)
  YonedaExtension j =
    record
      { judgmentForm = j
      ; arguments = identity }

  𝒴⁺ : (j : Ob 𝒥) → Context 𝒥 (o ⊔ a)
  𝒴⁺ j = 𝒴 j ⋊ₑ YonedaExtension j

  ⇒⋊ₑ : {i : Level} {Γ : Context 𝒥 i} (ϵ : Extension Γ)
      → 𝒴⁺ (Extension.judgmentForm ϵ) ⇒ Γ ⋊ₑ ϵ
  ⇒⋊ₑ {Γ = Γ} ϵ =
    record
      { component = component
      ; natural = funExt ∘ natural~ }
    where
      component : (j : Ob 𝒥) → (𝒴⁺ (Extension.judgmentForm ϵ)) ⟨ j ⟩ → (Γ ⋊ₑ ϵ) ⟨ j ⟩
      component j (inl x) = inl ((Extension.arguments ϵ ⟨ j ⟩) x)
      component j (inr refl) = inr refl

      natural~ : {j₀ j₁ : Ob 𝒥} (f : Hom 𝒥 j₀ j₁)
               → (Γ ⋊ₑ ϵ) ⟨ f ⟩ ∘ component j₀ ~ component j₁ ∘ (𝒴⁺ (Extension.judgmentForm ϵ)) ⟨ f ⟩
      natural~ f (inl x) = ap (λ h → inl (h x)) (ContextMorphism.natural (Extension.arguments ϵ) f)
      natural~ f (inr refl) = refl

data CollapseRelation
  ⦃ _ : FunExt ⦄
  {o a i : Level}
  {𝒥 : Semicategory o a}
  {Γ : Context 𝒥 i}
  (c : Collapse Γ)
  : (j' : Ob 𝒥) → Γ ⟨ j' ⟩ → Γ ⟨ j' ⟩ → Type (o ⊔ i) where
  collapseRelation : CollapseRelation c
                                      (Collapse.judgmentForm c)
                                      ((Collapse.arguments c ⟨ Collapse.judgmentForm c ⟩) (inr (inl refl)))
                                      ((Collapse.arguments c ⟨ Collapse.judgmentForm c ⟩) (inr (inr refl)))

infix 20 _⋊ₖ_
_⋊ₖ_ : ⦃ _ : FunExt ⦄
     → ⦃ _ : AllSetQuotients ⦄
     → {o a i : Level} {𝒥 : Semicategory o a}
     → (Γ : Context 𝒥 i) → Collapse Γ → Context 𝒥 (o ⊔ i)
_⋊ₖ_ {o} {a} {i} {𝒥} Γ col =
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
    onObjects j = (Γ ⟨ j ⟩) ⁄ CollapseRelation col j
      where
        open FromAllSetQuotients (Γ ⟨ j ⟩) (CollapseRelation col j)

    onMorphisms : ∀ {j₀ j₁} → Hom 𝒥 j₀ j₁ → onObjects j₀ → onObjects j₁
    onMorphisms {j₀} {j₁} f = rec ([_] ∘ (Γ ⟨ f ⟩)) respectsCollapseRelation
      where
        open FromAllSetQuotients (Γ ⟨ j₀ ⟩) (CollapseRelation col j₀) hiding (isSet-setQuotient)
        open FromAllSetQuotients (Γ ⟨ j₁ ⟩) (CollapseRelation col j₁)

        respectsCollapseRelation : {x y : Γ ⟨ j₀ ⟩}
                                 → CollapseRelation col j₀ x y → [ (Γ ⟨ f ⟩) x ] ＝ [ (Γ ⟨ f ⟩) y ]
        respectsCollapseRelation collapseRelation =
          ap [_]
             (sym (ap (λ σ → σ (inr (inr refl))) (ContextMorphism.natural (Collapse.arguments col) f))
             ∙ ap (λ σ → σ (inr (inl refl))) (ContextMorphism.natural (Collapse.arguments col) f))

    preservesComposition~ : ∀ {j₀ j₁ j₂} (f : Hom 𝒥 j₀ j₁) (g : Hom 𝒥 j₁ j₂)
                          → onMorphisms (g ∙ f) ~ onMorphisms g ∘ onMorphisms f
    preservesComposition~ {j₀} {j₁} {j₂} f g x = 
      elim
        (λ x → onMorphisms (g ∙ f) x ＝ onMorphisms g (onMorphisms f x))
        set
        preserves
        resp
        x
      where
        -- TODO: find out why it cannot figure out which isSet instance to use without hiding
        open FromAllSetQuotients (Γ ⟨ j₀ ⟩) (CollapseRelation col j₀) hiding (isSet-setQuotient)
        open FromAllSetQuotients (Γ ⟨ j₁ ⟩) (CollapseRelation col j₁) hiding (isSet-setQuotient)
        open FromAllSetQuotients (Γ ⟨ j₂ ⟩) (CollapseRelation col j₂)
        open Semifunctor.Reasoning (Context.semifunctor Γ)
        open Semicategory.Reasoning (TypeSemicategory i)

        set : ∀ q → isSet (onMorphisms (g ∙ f) q ＝ onMorphisms g (onMorphisms f q))
        set q = raise-level (pathLevel (onMorphisms (g ∙ f) q) (onMorphisms g (onMorphisms f q)))

        preserves : (x : Γ ⟨ j₀ ⟩) → onMorphisms (g ∙ f) ([ x ]) ＝ onMorphisms g (onMorphisms f ([ x ]))
        preserves x =
          begin
            onMorphisms (g ∙ f) ([ x ])            ⟦ rec-β ([_] ∘ (Γ ⟨ g ∙ f ⟩)) _ x ⟧
            [ (Γ ⟨ g ∙ f ⟩) x ]                    ⟦ ap (λ σ → [ σ x ]) (preserves-composition f g) ⟧
            [ (Γ ⟨ g ⟩) ((Γ ⟨ f ⟩) x) ]            ⟦ sym (rec-β ([_] ∘ (Γ ⟨ g ⟩)) _ ((Γ ⟨ f ⟩) x)) ⟧
            onMorphisms g ([ (Γ ⟨ f ⟩) x ])        ⟦ ap (onMorphisms g) (sym p) ⟧
            onMorphisms g (onMorphisms f ([ x ]))  ∎
          where
            p : onMorphisms f ([ x ]) ＝ [ (Γ ⟨ f ⟩) x ]
            p = rec-β ⦃ bset = FromAllSetQuotients.isSet-setQuotient (Γ ⟨ j₁ ⟩) (CollapseRelation col j₁) ⦄ ([_] ∘ (Γ ⟨ f ⟩)) _ x

        resp : {x y : Γ ⟨ j₀ ⟩} (r : CollapseRelation col j₀ x y)
             → tr (λ x → onMorphisms (g ∙ f) x ＝ onMorphisms g (onMorphisms f x))
                  (respects r)
                  (preserves x)
               ＝ preserves y
        resp r = allEqual _ _

σ : ⦃ _ : FunExt ⦄
  → ⦃ _ : AllSetQuotients ⦄
  → {o a i : Level} {𝒥 : Semicategory o a}
  → {Γ : Context 𝒥 i} {c : Collapse Γ}
  → Γ ⇒ Γ ⋊ₖ c
σ {𝒥 = 𝒥} {Γ = Γ} {c = c} = record
  { component = component
  ; natural = funExt ∘ natural }
  where
    component : ∀ j → Γ ⟨ j ⟩ → Γ ⋊ₖ c ⟨ j ⟩
    component j = [_]
      where
        open FromAllSetQuotients (Γ ⟨ j ⟩) (CollapseRelation c j)

    natural : ∀ {j₀ j₁} (f : Hom 𝒥 j₀ j₁) → Γ ⋊ₖ c ⟨ f ⟩ ∘ component j₀ ~ component j₁ ∘ Γ ⟨ f ⟩
    natural {j₀} {j₁} f = rec-β ([_] ∘ (Γ ⟨ f ⟩)) _
      where
        open FromAllSetQuotients (Γ ⟨ j₀ ⟩) (CollapseRelation c j₀) hiding (isSet-setQuotient)
        open FromAllSetQuotients (Γ ⟨ j₁ ⟩) (CollapseRelation c j₁)

infix 20 _⋊_
_⋊_ : ⦃ _ : FunExt ⦄
    → ⦃ _ : AllSetQuotients ⦄
    → {o a i : Level} {𝒥 : Semicategory o a}
    → (Γ : Context 𝒥 i) → ExtensionOrCollapse Γ → Context 𝒥 (o ⊔ i)
Γ ⋊ extend ext = Γ ⋊ₑ ext
Γ ⋊ collapse col = Γ ⋊ₖ col

→⋊ : ⦃ _ : FunExt ⦄
   → ⦃ _ : AllSetQuotients ⦄
   → {o a i : Level} {𝒥 : Semicategory o a}
   → (s : Sequent 𝒥 i)
   → Sequent.context s ⇒ Sequent.context s ⋊ Sequent.extensionOrCollapse s
→⋊ (mkSequent context (extend x)) = ι
→⋊ (mkSequent context (collapse x)) = σ
