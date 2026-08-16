module Context where

open import Prelude
open import Axioms
open import Homotopy.Equality
open import Homotopy.Equality.StructureIdentity
open import Foundation.DependentFunction.Equivalence
open import Foundation.DependentPair.Equivalence
open import Homotopy.Levels
open import Structure.Reasoning
open import Homotopy.StructuredMap
open import Homotopy.StructuredType
open import Structure.Composable
open import Structure.Associativity
open import Structure.Identity
open import Structure.PreservesComposition
open import Structure.Symmetric
open import Structure.Unit
open import Structure.Whiskerable
open import Algebra.Wild.Semi
open import Algebra.Wild.TruncatedTypeSemicategory
open import Homotopy.SetQuotient
open import Syntax.Arrowable public using ( Arrowable ; _⇒_ )

open import DependentSortVocabulary


-- ============ Contexts ===============

record Context
  {o a : Level}
  (𝒥 : DependentSortVocabulary {o} {a})
  (i : Level)
  : Type (o ⊔ a ⊔ lsuc i) where
  constructor mkContext
  field
    semifunctor : Semifunctor (semicategory 𝒥) (hSet-Semicategory i)

module _ {o a i : Level} {𝒥 : DependentSortVocabulary {o} {a}} where

  instance
    appliableOnObjectsContext : Appliable (Context 𝒥 i) (type (Judgment 𝒥)) (λ _ _ → hSet i)
    appliableOnObjectsContext = record { function = λ Γ j₀ → Context.semifunctor Γ ⟨ j₀ ⟩ }

    appliableOnMorphismsContext : {j₀ j₁ : type (Judgment 𝒥)} → Appliable (Context 𝒥 i) (type (JudgmentDependency 𝒥 j₀ j₁)) (λ Γ _ → ⌞ Γ ⟨ j₀ ⟩ ⌟ → ⌞ Γ ⟨ j₁ ⟩ ⌟)
    appliableOnMorphismsContext = record { function = λ Γ f → Context.semifunctor Γ ⟨ f ⟩ }

emptyContext : {o a : Level} (𝒥 : DependentSortVocabulary {o} {a}) (i : Level) → Context 𝒥 i
emptyContext 𝒥 i =
  record
    { semifunctor = record
      { onObjects = λ j → 𝟘
      ; semifunctorial = record
          { mappable = record { map = λ f () }
          ; preservesComposition = record { preserves-composition = λ f g → refl } } } }

module _ ⦃ _ : FunExt ⦄ {o a : Level} {𝒥 : DependentSortVocabulary {o} {a}} where

  sumContext : {i j : Level} → Context 𝒥 i → Context 𝒥 j → Context 𝒥 (i ⊔ j)
  sumContext {i} {j} Γ Δ =
    record { semifunctor = record
               { onObjects = onObjects
               ; semifunctorial = record
                   { mappable = record { map = onMorphisms }
                   ; preservesComposition = record
                       { preserves-composition = λ f g → funExt (preservesComposition~ f g) } } } }
    where
      open Semicategory.Reasoning (semicategory 𝒥)

      onObjects : type (Judgment 𝒥) → hSet (i ⊔ j)
      onObjects j₀ = (⌞ Γ ⟨ j₀ ⟩ ⌟ + ⌞ Δ ⟨ j₀ ⟩ ⌟) has-level itIsSet
        where
          opaque
            itIsSet : isSet (⌞ Γ ⟨ j₀ ⟩ ⌟ + ⌞ Δ ⟨ j₀ ⟩ ⌟)
            itIsSet = +-level (level-proof (Γ ⟨ j₀ ⟩)) (level-proof (Δ ⟨ j₀ ⟩))

      onMorphisms : ∀ {j₀ j₁} → type (JudgmentDependency 𝒥 j₀ j₁) → ⌞ onObjects j₀ ⌟ → ⌞ onObjects j₁ ⌟
      onMorphisms f (inl x) = inl ((Γ ⟨ f ⟩) x)
      onMorphisms f (inr y) = inr ((Δ ⟨ f ⟩) y)

      preservesComposition~ : ∀ {j₀ j₁ j₂} (f : type (JudgmentDependency 𝒥 j₀ j₁)) (g : type (JudgmentDependency 𝒥 j₁ j₂))
                            → onMorphisms (g ∙ f) ~ onMorphisms g ∘ onMorphisms f
      preservesComposition~ f g (inl x) = ap (λ h → inl (h x)) (preserves-composition f g)
        where
          open Semifunctor.Reasoning (Context.semifunctor Γ)
          open Semicategory.Reasoning (hSet-Semicategory i)
      preservesComposition~ f g (inr y) = ap (λ h → inr (h y)) (preserves-composition f g)
        where
          open Semifunctor.Reasoning (Context.semifunctor Δ)
          open Semicategory.Reasoning (hSet-Semicategory j)

  instance
    addableSumContext : Addable Level (Context 𝒥) _⊔_
    addableSumContext = record { addition = sumContext }



-- ============= Context morphisms ===========

record ContextMorphism
  {o a i j : Level}
  {𝒥 : DependentSortVocabulary {o} {a}}
  (Γ : Context 𝒥 i)
  (Δ : Context 𝒥 j)
  : Type (o ⊔ a ⊔ i ⊔ j) where
  constructor mkContextMorphism
  field
    component : (j : type (Judgment 𝒥)) → ⌞ Γ ⟨ j ⟩ ⌟ → ⌞ Δ ⟨ j ⟩ ⌟
    natural : {j₀ j₁ : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀ j₁))
            → Δ ⟨ f ⟩ ∘ component j₀ ＝ component j₁ ∘ Γ ⟨ f ⟩

ContextMorphism≃Σ :
    ∀ {o a i j} {𝒥 : DependentSortVocabulary {o} {a}} {Γ : Context 𝒥 i} {Δ : Context 𝒥 j}
  → ContextMorphism Γ Δ
    ≃ ∑[ ϵ ∶ ((j : type (Judgment 𝒥)) → ⌞ Γ ⟨ j ⟩ ⌟ → ⌞ Δ ⟨ j ⟩ ⌟) ]
        ({j₀ j₁ : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀ j₁)) → Δ ⟨ f ⟩ ∘ ϵ j₀ ＝ ϵ j₁ ∘ Γ ⟨ f ⟩)
ContextMorphism≃Σ .there ε =
  ContextMorphism.component ε , ContextMorphism.natural ε
ContextMorphism≃Σ .section .sectionBack (component , nat) =
  record { component = component ; natural = nat }
ContextMorphism≃Σ .section .isSection _ = refl
ContextMorphism≃Σ .retraction .retractionBack (component , nat) =
  record { component = component ; natural = nat }
ContextMorphism≃Σ .retraction .isRetraction _ = refl

instance
  ContextMorphism-isStructuredMap :
    ∀ {o a i j} {𝒥 : DependentSortVocabulary {o} {a}} {Γ : Context 𝒥 i} {Δ : Context 𝒥 j}
    → StructuredMap (ContextMorphism Γ Δ)
  ContextMorphism-isStructuredMap {o = o}
    .StructuredMap.iₗ = o
  ContextMorphism-isStructuredMap {o = o} {i = i} {j = j}
    .StructuredMap.jₗ = i ⊔ j
  ContextMorphism-isStructuredMap {o = o} {a = a}{i = i} {j = j}
    .StructuredMap.kₗ = o ⊔ a ⊔ i ⊔ j
  ContextMorphism-isStructuredMap {𝒥 = 𝒥}
    .StructuredMap.Domain = type (Judgment 𝒥)
  ContextMorphism-isStructuredMap {𝒥 = 𝒥} {Γ = Γ} {Δ = Δ}
    .StructuredMap.Codomain j = ⌞ Γ ⟨ j ⟩ ⌟ → ⌞ Δ ⟨ j ⟩ ⌟
  ContextMorphism-isStructuredMap {𝒥 = 𝒥} {Γ = Γ} {Δ = Δ}
    .StructuredMap.Structure ϵ = {j₀ j₁ : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀ j₁)) → Δ ⟨ f ⟩ ∘ ϵ j₀ ＝ ϵ j₁ ∘ Γ ⟨ f ⟩
  ContextMorphism-isStructuredMap
    .StructuredMap.structured = ContextMorphism≃Σ

instance
  arrowableContext : ∀ {o a} {𝒥 : DependentSortVocabulary {o} {a}}
                   → Arrowable Level Level (Context 𝒥) (λ i → Type i) (λ i j → o ⊔ a ⊔ i ⊔ j)
  arrowableContext {𝒥 = 𝒥} = record { arrow = ContextMorphism {𝒥 = 𝒥} }

record ContextMorphismEquality
  {o a i j :  Level}
  {𝒥 : DependentSortVocabulary {o} {a}}
  {Γ : Context 𝒥 i} {Δ : Context 𝒥 j}
  (α β : Γ ⇒ Δ)
  : Type (o ⊔ a ⊔ i ⊔ j) where
  constructor mkContextMorphismEquality
  field
    component≈ : ContextMorphism.component α ~ ContextMorphism.component β
open ContextMorphismEquality

-- Characterisation of the identity type on context morphisms

module _ {o a i j} {𝒥 : DependentSortVocabulary {o} {a}} {Γ : Context 𝒥 i} {Δ : Context 𝒥 j} where

  private
    Component : Type (o ⊔ i ⊔ j)
    Component = (j : type (Judgment 𝒥)) → ⌞ Γ ⟨ j ⟩ ⌟ → ⌞ Δ ⟨ j ⟩ ⌟

  naturalWitness-refl : {c : Component} (n : {j₀ j₁ : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀ j₁)) → Δ ⟨ f ⟩ ∘ c j₀ ＝ c j₁ ∘ Γ ⟨ f ⟩)
                      → {j₀ j₁ : type (Judgment 𝒥)} (h : type (JudgmentDependency 𝒥 j₀ j₁)) → n h ⨾ refl ＝ n h
  naturalWitness-refl n h = ∙-unitₗ

  instance
    ContextMorphism-isSamey : Samey 𝟙₀ (λ _ → Γ ⇒ Δ)
    ContextMorphism-isSamey = record { samey = ContextMorphismEquality }

  module _ ⦃ _ : FunExt ⦄ where

    private
      naturalWitness-Contractible : {c : Component} (n : {j₀ j₁ : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀ j₁)) → Δ ⟨ f ⟩ ∘ c j₀ ＝ c j₁ ∘ Γ ⟨ f ⟩)
        → Contractible (∑[ n' ∶ ({j₀ j₁ : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀ j₁)) → Δ ⟨ f ⟩ ∘ c j₀ ＝ c j₁ ∘ Γ ⟨ f ⟩) ]
                         ({j₀ j₁ : type (Judgment 𝒥)} (h : type (JudgmentDependency 𝒥 j₀ j₁)) → n h ⨾ refl ＝ n' h))
      naturalWitness-Contractible {c} n =
        ≃-Contractible
          (sym (equiv-∑
                 (equiv-Π (λ j → equiv-implicit-Π) ∙ equiv-implicit-Π)
                 (λ g → equiv-Π (λ j → equiv-implicit-Π) ∙ equiv-implicit-Π)))
          (Π-witness-Contractible _ λ j₀ →
           Π-witness-Contractible _ λ j₁ →
           Π-witness-Contractible _ λ h →
           singleton-Contractible (n h ⨾ refl))

      naturalWitness-fibre-Contractible :
          {α β : Γ ⇒ Δ} (p : ContextMorphism.component α ~ ContextMorphism.component β)
        → Contractible
            ({j₀ j₁ : type (Judgment 𝒥)} (h : type (JudgmentDependency 𝒥 j₀ j₁))
               → ContextMorphism.natural α h ⨾ (Γ ⟨ h ⟩ ◁ p j₁)
                 ＝ (p j₀ ▷ Δ ⟨ h ⟩) ⨾ ContextMorphism.natural β h)
      naturalWitness-fibre-Contractible p =
        ≃-Contractible
          (sym (equiv-Π (λ _ → equiv-implicit-Π) ∙ equiv-implicit-Π))
          (→-Contractible λ j₀ → →-Contractible λ j₁ → →-Contractible λ h →
             prop-path-contractible ⦃ pathLevel ⦃ component-isSet ⦄ _ _ ⦄ _ _)
        where
          component-isSet : {j₀ j₁ : type (Judgment 𝒥)} → isSet (⌞ Γ ⟨ j₀ ⟩ ⌟ → ⌞ Δ ⟨ j₁ ⟩ ⌟)
          component-isSet {j₁ = j₁} = →-level (λ _ → level-proof (Δ ⟨ j₁ ⟩))

      component≈≃ : {α β : Γ ⇒ Δ}
        → (ContextMorphism.component α ~ ContextMorphism.component β) ≃ (α ≈ β)
      component≈≃ .there = mkContextMorphismEquality
      component≈≃ .section .sectionBack = component≈
      component≈≃ .section .isSection _ = refl
      component≈≃ .retraction .retractionBack = component≈
      component≈≃ .retraction .isRetraction _ = refl

      opaque
        characterisation~ : {α β : Γ ⇒ Δ} → (α ＝ β) ≃ (α ≈ β)
        characterisation~ =
             structuredMap-＝
               (λ nε p nδ → {j₀ j₁ : type (Judgment 𝒥)} (h : type (JudgmentDependency 𝒥 j₀ j₁)) → nε h ⨾ (Γ ⟨ h ⟩ ◁ p j₁) ＝ (p j₀ ▷ Δ ⟨ h ⟩) ⨾ nδ h)
               naturalWitness-refl
               naturalWitness-Contractible
          ⨾  ∑-contractible-fibres naturalWitness-fibre-Contractible
          ⨾  component≈≃

    instance
      equalityContextMorphism : Equality 𝟙₀ (λ _ → Γ ⇒ Δ)
      equalityContextMorphism = record { characterisation = characterisation~ }

module _ ⦃ _ : FunExt ⦄ {o a : Level} {𝒥 : DependentSortVocabulary {o} {a}} where

  instance
    appliableContextMorphism : ∀ {i j} {Γ : Context 𝒥 i} {Δ : Context 𝒥 j}
                             → Appliable (ContextMorphism Γ Δ) (type (Judgment 𝒥)) (λ _ j → ⌞ Γ ⟨ j ⟩ ⌟ → ⌞ Δ ⟨ j ⟩ ⌟)
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
            eq (record { component≈ = identity }) }

    identityContextMorphism : Identity _ (Context 𝒥) ContextMorphism
    identityContextMorphism =
      record
        { identity = record
            { component = λ j → id
            ; natural = identity } }

  sumContextMorphism : {i₀ i₁ j₀ j₁ : Level}
                       {Γ₀ : Context 𝒥 i₀} {Γ₁ : Context 𝒥 i₁}
                       {Δ₀ : Context 𝒥 j₀} {Δ₁ : Context 𝒥 j₁}
                     → Γ₀ ⇒ Γ₁ → Δ₀ ⇒ Δ₁ → Γ₀ + Δ₀ ⇒ Γ₁ + Δ₁
  sumContextMorphism {Γ₀ = Γ₀} {Γ₁ = Γ₁} {Δ₀ = Δ₀} {Δ₁ = Δ₁} α β =
    record
      { component = component
      ; natural = funExt ∘ natural~ }
    where
      component : (j : type (Judgment 𝒥)) → ⌞ (Γ₀ + Δ₀) ⟨ j ⟩ ⌟ → ⌞ (Γ₁ + Δ₁) ⟨ j ⟩ ⌟
      component j (inl x) = inl ((α ⟨ j ⟩) x)
      component j (inr y) = inr ((β ⟨ j ⟩) y)

      natural~ : {j₀ j₁ : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀ j₁))
               → (Γ₁ + Δ₁) ⟨ f ⟩ ∘ component j₀ ~ component j₁ ∘ (Γ₀ + Δ₀) ⟨ f ⟩
      natural~ f (inl x) = ap (λ h → inl (h x)) (ContextMorphism.natural α f)
      natural~ f (inr y) = ap (λ h → inr (h y)) (ContextMorphism.natural β f)

  inlContext : {i j : Level} {Γ : Context 𝒥 i} {Δ : Context 𝒥 j} → Γ ⇒ Γ + Δ
  inlContext =
    record
      { component = λ j → inl
      ; natural = identity }

  inrContext : {i j : Level} {Γ : Context 𝒥 i} {Δ : Context 𝒥 j} → Δ ⇒ Γ + Δ
  inrContext =
    record
      { component = λ j → inr
      ; natural = identity }


-- ============= Context equivalences ===========

record ContextEquivalence
  {o a i j : Level}
  {𝒥 : DependentSortVocabulary {o} {a}}
  (Γ : Context 𝒥 i)
  (Δ : Context 𝒥 j)
  : Type (o ⊔ a ⊔ i ⊔ j) where
  constructor mkContextEquivalence
  field
    morphism : Γ ⇒ Δ
    component-isEquivalence : (j : type (Judgment 𝒥)) → isEquivalence (ContextMorphism.component morphism j)

instance
  sameyContext : ∀ {o a} {𝒥 : DependentSortVocabulary {o} {a}} → Samey Level (Context 𝒥)
  sameyContext = record { samey = ContextEquivalence }


-- ============== Yoneda contexts ==============

𝒴 : ⦃ _ : FunExt ⦄ {o a : Level} {𝒥 : DependentSortVocabulary {o} {a}}
  → (j : type (Judgment 𝒥)) → Context 𝒥 a
𝒴 {𝒥 = 𝒥} j =
  record { semifunctor = record
           { onObjects = JudgmentDependency 𝒥 j
           ; semifunctorial = record
               { mappable = record { map = λ f g → f ∙ g }
               ; preservesComposition = record
                   { preserves-composition = λ f g → funExt (λ h → sym ⨾-associative) } } } }
  where
  open Semicategory.Reasoning (semicategory 𝒥)

𝒴⁺⁺ : ⦃ _ : FunExt ⦄ {o a : Level} {𝒥 : DependentSortVocabulary {o} {a}}
    → (j : type (Judgment 𝒥)) → Context 𝒥 (o ⊔ a)
𝒴⁺⁺ {o} {a} {𝒥} j =
  record { semifunctor = record
           { onObjects = onObjects
           ; semifunctorial = record
               { mappable = record { map = onMorphisms }
               ; preservesComposition = record
                   { preserves-composition = λ f g → funExt (preservesComposition~ f g) } } } }
  where
  open Semicategory.Reasoning (semicategory 𝒥)

  onObjects : type (Judgment 𝒥) → hSet (o ⊔ a)
  onObjects j₁ = (type (JudgmentDependency 𝒥 j j₁) + (type (j₁ ＝[ 𝒥 ] j) + type (j₁ ＝[ 𝒥 ] j)))
                 has-level itIsSet
    where
      opaque
        itIsSet : isSet (type (JudgmentDependency 𝒥 j j₁) + (type (j₁ ＝[ 𝒥 ] j) + type (j₁ ＝[ 𝒥 ] j)))
        itIsSet = +-level (judgmentDependencies-isSet 𝒥)
                    (+-level (judgmentPaths-isSet 𝒥) (judgmentPaths-isSet 𝒥))

  onMorphisms : ∀ {j₁ j₂} → type (JudgmentDependency 𝒥 j₁ j₂) → ⌞ onObjects j₁ ⌟ → ⌞ onObjects j₂ ⌟
  onMorphisms f (inl g) = inl (f ∙ g)
  onMorphisms f (inr (inl refl)) = inl f
  onMorphisms f (inr (inr refl)) = inl f

  preservesComposition~ : ∀ {j₁ j₂ j₃} (f : type (JudgmentDependency 𝒥 j₁ j₂)) (g : type (JudgmentDependency 𝒥 j₂ j₃))
                        → onMorphisms (g ∙ f) ~ onMorphisms g ∘ onMorphisms f
  preservesComposition~ f g (inl h) = ap inl (sym ∙-associative)
  preservesComposition~ f g (inr (inl refl)) = refl
  preservesComposition~ f g (inr (inr refl)) = refl


-- =============== Context extension and collapse ==============

record Extension
  ⦃ _ : FunExt ⦄
  {o a i : Level}
  {𝒥 : DependentSortVocabulary {o} {a}}
 
  (Γ : Context 𝒥 i)
  : Type (o ⊔ a ⊔ i) where
  constructor mkExtension
  field
    judgmentForm : type (Judgment 𝒥)
    arguments : 𝒴 judgmentForm ⇒ Γ

record Collapse
  ⦃ _ : FunExt ⦄
  {o a i : Level}
  {𝒥 : DependentSortVocabulary {o} {a}}
 
  (Γ : Context 𝒥 i)
  : Type (o ⊔ a ⊔ i) where
  constructor mkCollapse
  field
    judgmentForm : type (Judgment 𝒥)
    arguments : 𝒴⁺⁺ judgmentForm ⇒ Γ

data ExtensionOrCollapse
  ⦃ _ : FunExt ⦄
  {o a i : Level}
  {𝒥 : DependentSortVocabulary {o} {a}}
 
  (Γ : Context 𝒥 i)
  : Type (o ⊔ a ⊔ i) where
  extend : Extension Γ → ExtensionOrCollapse Γ
  collapse : Collapse Γ → ExtensionOrCollapse Γ

module _ ⦃ _ : FunExt ⦄
  {o a i j : Level}
  {𝒥 : DependentSortVocabulary {o} {a}}
  {Γ : Context 𝒥 i} {Δ : Context 𝒥 j}
  (α : Γ ⇒ Δ) where

  mapExtension : Extension Γ → Extension Δ
  Extension.judgmentForm (mapExtension ext) = Extension.judgmentForm ext
  Extension.arguments (mapExtension ext) = α ∙ Extension.arguments ext

  mapCollapse : Collapse Γ → Collapse Δ
  Collapse.judgmentForm (mapCollapse col) = Collapse.judgmentForm col
  Collapse.arguments (mapCollapse col) = α ∙ Collapse.arguments col

  mapExtensionOrCollapse : ExtensionOrCollapse Γ → ExtensionOrCollapse Δ
  mapExtensionOrCollapse (extend ext) = extend (mapExtension ext)
  mapExtensionOrCollapse (collapse col) = collapse (mapCollapse col)

infix 20 _⋊ₑ_
_⋊ₑ_ : ⦃ _ : FunExt ⦄
    → {o a i : Level} {𝒥 : DependentSortVocabulary {o} {a}}
    → (Γ : Context 𝒥 i) → Extension Γ → Context 𝒥 (o ⊔ i)
_⋊ₑ_ {o} {a} {i} {𝒥} Γ ext =
  record { semifunctor = record
             { onObjects = onObjects
             ; semifunctorial = record
                 { mappable = record { map = onMorphisms }
                 ; preservesComposition = record
                     { preserves-composition = λ f g → funExt (preservesComposition~ f g) } } } }
  where
    open Semicategory.Reasoning (semicategory 𝒥)
    open Semifunctor.Reasoning (Context.semifunctor Γ)

    onObjects : type (Judgment 𝒥) → hSet (o ⊔ i)
    onObjects j = (⌞ Γ ⟨ j ⟩ ⌟ + type (j ＝[ 𝒥 ] Extension.judgmentForm ext)) has-level itIsSet
      where
        opaque
          itIsSet : isSet (⌞ Γ ⟨ j ⟩ ⌟ + type (j ＝[ 𝒥 ] Extension.judgmentForm ext))
          itIsSet = +-level (level-proof (Γ ⟨ j ⟩)) (judgmentPaths-isSet 𝒥)

    onMorphisms : ∀ {j₀ j₁} → type (JudgmentDependency 𝒥 j₀ j₁) → ⌞ onObjects j₀ ⌟ → ⌞ onObjects j₁ ⌟
    onMorphisms f (inl x) = inl ((Γ ⟨ f ⟩) x)
    onMorphisms {j₁ = j₁} f (inr refl) = inl ((Extension.arguments ext ⟨ j₁ ⟩) f)

    preservesComposition~ : ∀ {j₀ j₁ j₂} (f : type (JudgmentDependency 𝒥 j₀ j₁)) (g : type (JudgmentDependency 𝒥 j₁ j₂))
                          → onMorphisms (g ∙ f) ~ onMorphisms g ∘ onMorphisms f
    preservesComposition~ f g (inl x) = ap (λ h → inl (h x)) (preserves-composition f g)
      where open Semicategory.Reasoning (hSet-Semicategory i)
    preservesComposition~ f g (inr refl) = ap (λ h → inl (h f)) (sym (ContextMorphism.natural (Extension.arguments ext) g))

ι : ⦃ _ : FunExt ⦄
  → {o a i : Level} {𝒥 : DependentSortVocabulary {o} {a}}
  → {Γ : Context 𝒥 i} {ϵ : Extension Γ}
  → Γ ⇒ Γ ⋊ₑ ϵ
ι = record
      { component = λ j → inl
      ; natural = identity }

module _ ⦃ _ : FunExt ⦄ {o a : Level} {𝒥 : DependentSortVocabulary {o} {a}} where

  YonedaExtension : (j : type (Judgment 𝒥)) → Extension (𝒴 {𝒥 = 𝒥} j)
  YonedaExtension j =
    record
      { judgmentForm = j
      ; arguments = identity }

  𝒴⁺ : (j : type (Judgment 𝒥)) → Context 𝒥 (o ⊔ a)
  𝒴⁺ j = 𝒴 j ⋊ₑ YonedaExtension j

  ⇒⋊ₑ : {i : Level} {Γ : Context 𝒥 i} (ϵ : Extension Γ)
      → 𝒴⁺ (Extension.judgmentForm ϵ) ⇒ Γ ⋊ₑ ϵ
  ⇒⋊ₑ {Γ = Γ} ϵ =
    record
      { component = component
      ; natural = funExt ∘ natural~ }
    where
      component : (j : type (Judgment 𝒥)) → ⌞ (𝒴⁺ (Extension.judgmentForm ϵ)) ⟨ j ⟩ ⌟ → ⌞ (Γ ⋊ₑ ϵ) ⟨ j ⟩ ⌟
      component j (inl x) = inl ((Extension.arguments ϵ ⟨ j ⟩) x)
      component j (inr refl) = inr refl

      natural~ : {j₀ j₁ : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀ j₁))
               → (Γ ⋊ₑ ϵ) ⟨ f ⟩ ∘ component j₀ ~ component j₁ ∘ (𝒴⁺ (Extension.judgmentForm ϵ)) ⟨ f ⟩
      natural~ f (inl x) = ap (λ h → inl (h x)) (ContextMorphism.natural (Extension.arguments ϵ) f)
      natural~ f (inr refl) = refl

data CollapseRelation
  ⦃ _ : FunExt ⦄
  {o a i : Level}
  {𝒥 : DependentSortVocabulary {o} {a}}
  {Γ : Context 𝒥 i}
  (c : Collapse Γ)
  : (j' : type (Judgment 𝒥)) → ⌞ Γ ⟨ j' ⟩ ⌟ → ⌞ Γ ⟨ j' ⟩ ⌟ → Type (o ⊔ i) where
  collapseRelation : CollapseRelation c
                                      (Collapse.judgmentForm c)
                                      ((Collapse.arguments c ⟨ Collapse.judgmentForm c ⟩) (inr (inl refl)))
                                      ((Collapse.arguments c ⟨ Collapse.judgmentForm c ⟩) (inr (inr refl)))

infix 20 _⋊ₖ_
_⋊ₖ_ : ⦃ _ : FunExt ⦄
     → ⦃ _ : AllSetQuotients ⦄
     → {o a i : Level} {𝒥 : DependentSortVocabulary {o} {a}}
     → (Γ : Context 𝒥 i) → Collapse Γ → Context 𝒥 (o ⊔ i)
_⋊ₖ_ {o} {a} {i} {𝒥} Γ col =
  record { semifunctor = record
             { onObjects = onObjects
             ; semifunctorial = record
                 { mappable = record { map = onMorphisms }
                 ; preservesComposition = record
                     { preserves-composition = λ f g → funExt (preservesComposition~ f g) } } } }
  where
    open Semicategory.Reasoning (semicategory 𝒥)
    open Semifunctor.Reasoning (Context.semifunctor Γ)

    onObjects : type (Judgment 𝒥) → hSet (o ⊔ i)
    onObjects j = ((⌞ Γ ⟨ j ⟩ ⌟) ⁄ CollapseRelation col j) has-level fromInstance
      where
        open FromAllSetQuotients (⌞ Γ ⟨ j ⟩ ⌟) (CollapseRelation col j)

    onMorphisms : ∀ {j₀ j₁} → type (JudgmentDependency 𝒥 j₀ j₁) → ⌞ onObjects j₀ ⌟ → ⌞ onObjects j₁ ⌟
    onMorphisms {j₀} {j₁} f = ⁄-rec ([_] ∘ (Γ ⟨ f ⟩)) respectsCollapseRelation
      where
        open FromAllSetQuotients (⌞ Γ ⟨ j₀ ⟩ ⌟) (CollapseRelation col j₀)
        open FromAllSetQuotients (⌞ Γ ⟨ j₁ ⟩ ⌟) (CollapseRelation col j₁)

        respectsCollapseRelation : {x y : ⌞ Γ ⟨ j₀ ⟩ ⌟}
                                 → CollapseRelation col j₀ x y → [ (Γ ⟨ f ⟩) x ] ＝ [ (Γ ⟨ f ⟩) y ]
        respectsCollapseRelation collapseRelation =
          ap [_]
             (sym (ap (λ σ → σ (inr (inr refl))) (ContextMorphism.natural (Collapse.arguments col) f))
             ∙ ap (λ σ → σ (inr (inl refl))) (ContextMorphism.natural (Collapse.arguments col) f))

    preservesComposition~ : ∀ {j₀ j₁ j₂} (f : type (JudgmentDependency 𝒥 j₀ j₁)) (g : type (JudgmentDependency 𝒥 j₁ j₂))
                          → onMorphisms (g ∙ f) ~ onMorphisms g ∘ onMorphisms f
    preservesComposition~ {j₀} {j₁} {j₂} f g x = 
      ⁄-elim
        (λ x → onMorphisms (g ∙ f) x ＝ onMorphisms g (onMorphisms f x))
        set
        preserves
        resp
        x
      where
        open FromAllSetQuotients (⌞ Γ ⟨ j₀ ⟩ ⌟) (CollapseRelation col j₀)
        open FromAllSetQuotients (⌞ Γ ⟨ j₁ ⟩ ⌟) (CollapseRelation col j₁)
        open FromAllSetQuotients (⌞ Γ ⟨ j₂ ⟩ ⌟) (CollapseRelation col j₂)
        open Semifunctor.Reasoning (Context.semifunctor Γ)
        open Semicategory.Reasoning (hSet-Semicategory i)

        set : ∀ q → isSet (onMorphisms (g ∙ f) q ＝ onMorphisms g (onMorphisms f q))
        set q = raise-level (pathLevel (onMorphisms (g ∙ f) q) (onMorphisms g (onMorphisms f q)))

        preserves : (x : ⌞ Γ ⟨ j₀ ⟩ ⌟) → onMorphisms (g ∙ f) ([ x ]) ＝ onMorphisms g (onMorphisms f ([ x ]))
        preserves x =
          begin
            onMorphisms (g ∙ f) ([ x ])            ⟪ ⁄-rec-β ([_] ∘ (Γ ⟨ g ∙ f ⟩)) _ x ⟫
            [ (Γ ⟨ g ∙ f ⟩) x ]                    ⟪ ap (λ σ → [ σ x ]) (preserves-composition f g) ⟫
            [ (Γ ⟨ g ⟩) ((Γ ⟨ f ⟩) x) ]            ⟪ sym (⁄-rec-β ([_] ∘ (Γ ⟨ g ⟩)) _ ((Γ ⟨ f ⟩) x)) ⟫
            onMorphisms g ([ (Γ ⟨ f ⟩) x ])        ⟪ ap (onMorphisms g) (sym p) ⟫
            onMorphisms g (onMorphisms f ([ x ]))  ∎
          where
            p : onMorphisms f ([ x ]) ＝ [ (Γ ⟨ f ⟩) x ]
            p = ⁄-rec-β ([_] ∘ (Γ ⟨ f ⟩)) _ x

        resp : {x y : ⌞ Γ ⟨ j₀ ⟩ ⌟} (r : CollapseRelation col j₀ x y)
             → tr (λ x → onMorphisms (g ∙ f) x ＝ onMorphisms g (onMorphisms f x))
                  (respects r)
                  (preserves x)
               ＝ preserves y
        resp r = allEqual _ _

σ : ⦃ _ : FunExt ⦄
  → ⦃ _ : AllSetQuotients ⦄
  → {o a i : Level} {𝒥 : DependentSortVocabulary {o} {a}}
  → {Γ : Context 𝒥 i} {c : Collapse Γ}
  → Γ ⇒ Γ ⋊ₖ c
σ {𝒥 = 𝒥} {Γ = Γ} {c = c} = record
  { component = component
  ; natural = funExt ∘ natural }
  where
    component : ∀ j → ⌞ Γ ⟨ j ⟩ ⌟ → ⌞ (Γ ⋊ₖ c) ⟨ j ⟩ ⌟
    component j = [_]
      where
        open FromAllSetQuotients (⌞ Γ ⟨ j ⟩ ⌟) (CollapseRelation c j)

    natural : ∀ {j₀ j₁} (f : type (JudgmentDependency 𝒥 j₀ j₁)) → (Γ ⋊ₖ c) ⟨ f ⟩ ∘ component j₀ ~ component j₁ ∘ Γ ⟨ f ⟩
    natural {j₀} {j₁} f = ⁄-rec-β ([_] ∘ (Γ ⟨ f ⟩)) _
      where
        open FromAllSetQuotients (⌞ Γ ⟨ j₀ ⟩ ⌟) (CollapseRelation c j₀)
        open FromAllSetQuotients (⌞ Γ ⟨ j₁ ⟩ ⌟) (CollapseRelation c j₁)

infix 20 _⋊_
_⋊_ : ⦃ _ : FunExt ⦄
    → ⦃ _ : AllSetQuotients ⦄
    → {o a i : Level} {𝒥 : DependentSortVocabulary {o} {a}}
    → (Γ : Context 𝒥 i) → ExtensionOrCollapse Γ → Context 𝒥 (o ⊔ i)
Γ ⋊ extend ext = Γ ⋊ₑ ext
Γ ⋊ collapse col = Γ ⋊ₖ col
