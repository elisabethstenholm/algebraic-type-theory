module Context.Morphism where

open import Prelude
open import Axioms
open import Homotopy.Equality
open import Homotopy.Equality.StructureIdentity
open import Homotopy.Fibre
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
open import Algebra.Wild.Semicategory hiding (objects≈ ; hom≈ ; composition≈ ; associative≈)
open import Algebra.Wild.Semifunctor hiding (objects≈ ; map≈)
open import Algebra.Wild.TruncatedTypeSemicategory
open import Homotopy.SetQuotient.Nominal
open import Syntax.Arrowable
open import Foundation.Sum.Equivalence
open import Structure.Bimappable

open import DependentSortVocabulary
open DependentSortVocabulary.DependentSortVocabulary


open import Context

-- ============= Context morphisms ===========

record ContextMorphism
  {o a i j : Level}
  {𝒥 : DependentSortVocabulary o a}
  (Γ : Context 𝒥 i)
  (Δ : Context 𝒥 j)
  : Type (o ⊔ a ⊔ i ⊔ j) where
  constructor mkContextMorphism
  field
    component : (j : type (Judgment 𝒥)) → ⌞ Γ ⟨ j ⟩ ⌟ → ⌞ Δ ⟨ j ⟩ ⌟
    natural : {j₀ j₁ : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀ j₁))
            → Δ ⟨ f ⟩ ∘ component j₀ ＝ component j₁ ∘ Γ ⟨ f ⟩

ContextMorphism≃Σ :
    ∀ {o a i j} {𝒥 : DependentSortVocabulary o a} {Γ : Context 𝒥 i} {Δ : Context 𝒥 j}
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
    ∀ {o a i j} {𝒥 : DependentSortVocabulary o a} {Γ : Context 𝒥 i} {Δ : Context 𝒥 j}
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
  arrowableContext : ∀ {o a} {𝒥 : DependentSortVocabulary o a}
                   → Arrowable Level Level (Context 𝒥) (λ i → Type i) (λ i j → o ⊔ a ⊔ i ⊔ j)
  arrowableContext {𝒥 = 𝒥} = record { arrow = ContextMorphism {𝒥 = 𝒥} }

record ContextMorphismEquality
  {o a i j :  Level}
  {𝒥 : DependentSortVocabulary o a}
  {Γ : Context 𝒥 i} {Δ : Context 𝒥 j}
  (α β : Γ ⇒ Δ)
  : Type (o ⊔ a ⊔ i ⊔ j) where
  constructor mkContextMorphismEquality
  field
    component≈ : ContextMorphism.component α ~ ContextMorphism.component β
open ContextMorphismEquality

-- Characterisation of the identity type on context morphisms

module _ {o a i j} {𝒥 : DependentSortVocabulary o a} {Γ : Context 𝒥 i} {Δ : Context 𝒥 j} where

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

    contextMorphismEquality-isProposition : {α β : Γ ⇒ Δ} → isProposition (α ≈ β)
    contextMorphismEquality-isProposition =
      retract-level component≈ mkContextMorphismEquality (λ _ → refl)
        (→-level λ j → ＝-isLevel ⦃ →-level (λ _ → level-proof (Δ ⟨ j ⟩)) ⦄)

    contextMorphism-isSet : isSet (Γ ⇒ Δ)
    contextMorphism-isSet = path-type (λ α β →
      ≃-level (sym observe-≃) contextMorphismEquality-isProposition)
          

module _ {o a : Level} {𝒥 : DependentSortVocabulary o a} where

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

    associativeCompositionContextMorphism : ⦃ _ : FunExt ⦄ → AssociativeComposition (ContextMorphism { 𝒥 = 𝒥 }) (λ _ _ → _＝_)
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

  sumContextMorphism : ⦃ _ : FunExt ⦄ {i₀ i₁ j₀ j₁ : Level}
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

  inlContext : ⦃ _ : FunExt ⦄ {i j : Level} {Γ : Context 𝒥 i} {Δ : Context 𝒥 j} → Γ ⇒ Γ + Δ
  inlContext =
    record
      { component = λ j → inl
      ; natural = identity }

  inrContext : ⦃ _ : FunExt ⦄ {i j : Level} {Γ : Context 𝒥 i} {Δ : Context 𝒥 j} → Δ ⇒ Γ + Δ
  inrContext =
    record
      { component = λ j → inr
      ; natural = identity }


-- ============= Context equivalences ===========

record ContextEquivalence
  {o a i j : Level}
  {𝒥 : DependentSortVocabulary o a}
  (Γ : Context 𝒥 i)
  (Δ : Context 𝒥 j)
  : Type (o ⊔ a ⊔ i ⊔ j) where
  constructor mkContextEquivalence
  field
    morphism : Γ ⇒ Δ
    component-isEquivalence : (j : type (Judgment 𝒥)) → isEquivalence (morphism ⟨ j ⟩)

instance
  sameyContext : ∀ {o a} {𝒥 : DependentSortVocabulary o a} → Samey Level (Context 𝒥)
  sameyContext = record { samey = ContextEquivalence }

module _ ⦃ _ : FunExt ⦄ {o a : Level} {𝒥 : DependentSortVocabulary o a} where

  eqContextEquivalence : {i j : Level} {Γ : Context 𝒥 i} {Δ : Context 𝒥 j}
                         (e₀ e₁ : ContextEquivalence Γ Δ)
                       → ContextEquivalence.morphism e₀ ＝ ContextEquivalence.morphism e₁
                       → e₀ ＝ e₁
  eqContextEquivalence (mkContextEquivalence α w) (mkContextEquivalence _ w') refl =
    ap (mkContextEquivalence α) (allEqual w w')

  instance
    appliableContextEquivalence : ∀ {i j} {Γ : Context 𝒥 i} {Δ : Context 𝒥 j}
                                → Appliable (ContextEquivalence Γ Δ) (type (Judgment 𝒥)) (λ _ j → ⌞ Γ ⟨ j ⟩ ⌟ → ⌞ Δ ⟨ j ⟩ ⌟)
    appliableContextEquivalence = record { function = ContextMorphism.component ∘ ContextEquivalence.morphism }

    composableContextEquivalence : Composable _ (Context 𝒥) ContextEquivalence
    composableContextEquivalence =
      record
        { composition = λ e₀ e₁ → record
            { morphism = ContextEquivalence.morphism e₀ ⨾ ContextEquivalence.morphism e₁
            ; component-isEquivalence = λ j →
                ≃→isEquivalence (  isEquivalence→≃ (ContextEquivalence.component-isEquivalence e₀ j)
                                ⨾  isEquivalence→≃ (ContextEquivalence.component-isEquivalence e₁ j)) } }

    associativeCompositionContextEquivalence : AssociativeComposition (ContextEquivalence { 𝒥 = 𝒥 }) (λ _ _ → _＝_)
    associativeCompositionContextEquivalence =
      record { ⨾-associative = eqContextEquivalence _ _ (eq (record { component≈ = identity })) }

    identityContextEquivalence : Identity _ (Context 𝒥) ContextEquivalence
    identityContextEquivalence =
      record
        { identity = record
            { morphism = identity
            ; component-isEquivalence = λ j → id→isEquivalence } }


-- ============== Equivalent contexts are equal ==============

module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄
  {o a i : Level} {𝒥 : DependentSortVocabulary o a} where

  private
    trHomOnPaths : (A A' B B' : hSet i) (r : A ＝ A') (s : B ＝ B')
                   (v : ⌞ A ⌟ → ⌞ B ⌟) (z : ⌞ A ⌟)
                 → tr-hom (hSet-Semicategory i) r s v (there (observe r) z)
                   ＝ there (observe s) (v z)
    trHomOnPaths A .A B .B refl refl v z = refl

  contextEquivalence→≈ : {Γ Δ : Context 𝒥 i}
                       → ContextEquivalence Γ Δ
                       → Context.semifunctor Γ ≈ Context.semifunctor Δ
  contextEquivalence→≈ {Γ = Γ} {Δ = Δ} w =
    record
      { objects≈ = objects≈
      ; map≈ = map≈
      ; preservesComposition≈ = λ A B E g h → allEqual ⦃ ＝-isLevel ⦃ homSet A E ⦄ ⦄ _ _ }
    where
      α = ContextEquivalence.morphism w

      e : (j : type (Judgment 𝒥)) → ⌞ Γ ⟨ j ⟩ ⌟ ≃ ⌞ Δ ⟨ j ⟩ ⌟
      e j = isEquivalence→≃ (ContextEquivalence.component-isEquivalence w j)

      objects≈ : (j : type (Judgment 𝒥)) → Γ ⟨ j ⟩ ＝ Δ ⟨ j ⟩
      objects≈ j = eq (e j)

      homSet : (A E : type (Judgment 𝒥)) → isSet (⌞ Δ ⟨ A ⟩ ⌟ → ⌞ Δ ⟨ E ⟩ ⌟)
      homSet A E = →-level (λ _ → level-proof (Δ ⟨ E ⟩))

      transportComputes : (X X' Y Y' : hSet i)
                          (d : ⌞ X ⌟ ≃ ⌞ X' ⌟) (c : ⌞ Y ⌟ ≃ ⌞ Y' ⌟)
                          (u : ⌞ X ⌟ → ⌞ Y ⌟) (x : ⌞ X ⌟)
                        → tr-hom (hSet-Semicategory i)
                                 (eq {x = X} {y = X'} d) (eq {x = Y} {y = Y'} c) u (there d x)
                          ＝ there c (u x)
      transportComputes X X' Y Y' d c u x =
           ap (λ v → tr-hom (hSet-Semicategory i) p q u (there v x))
              (sym (observe-eq ⦃ []Type-hasEquality ⦄ d))
        ⨾  trHomOnPaths X X' Y Y' p q u x
        ⨾  ap (λ v → there v (u x)) (observe-eq ⦃ []Type-hasEquality ⦄ c)
        where
          p = eq {x = X} {y = X'} d
          q = eq {x = Y} {y = Y'} c

      map≈ : (j₀ j₁ : type (Judgment 𝒥)) (f : type (JudgmentDependency 𝒥 j₀ j₁))
           → tr-hom (hSet-Semicategory i) (objects≈ j₀) (objects≈ j₁) (Γ ⟨ f ⟩) ＝ Δ ⟨ f ⟩
      map≈ j₀ j₁ f = funExt pointwise
        where
          back : ⌞ Δ ⟨ j₀ ⟩ ⌟ → ⌞ Γ ⟨ j₀ ⟩ ⌟
          back = sectionBack (section (ContextEquivalence.component-isEquivalence w j₀))

          onSection : (y : ⌞ Δ ⟨ j₀ ⟩ ⌟) → there (e j₀) (back y) ＝ y
          onSection = isSection (section (ContextEquivalence.component-isEquivalence w j₀))

          pointwise : (y : ⌞ Δ ⟨ j₀ ⟩ ⌟)
                    → tr-hom (hSet-Semicategory i) (objects≈ j₀) (objects≈ j₁) (Γ ⟨ f ⟩) y
                      ＝ (Δ ⟨ f ⟩) y
          pointwise y =
               ap (tr-hom (hSet-Semicategory i) (objects≈ j₀) (objects≈ j₁) (Γ ⟨ f ⟩))
                  (sym (onSection y))
            ⨾  transportComputes (Γ ⟨ j₀ ⟩) (Δ ⟨ j₀ ⟩) (Γ ⟨ j₁ ⟩) (Δ ⟨ j₁ ⟩)
                                 (e j₀) (e j₁) (Γ ⟨ f ⟩) (back y)
            ⨾  sym (ap (λ h → h (back y)) (ContextMorphism.natural α f))
            ⨾  ap (Δ ⟨ f ⟩) (onSection y)

  ≈→contextEquivalence : {Γ Δ : Context 𝒥 i}
                       → Context.semifunctor Γ ≈ Context.semifunctor Δ
                       → ContextEquivalence Γ Δ
  ≈→contextEquivalence {Γ = Γ} {Δ = Δ} W =
    record
      { morphism = record { component = comp ; natural = λ f → funExt (natural~ f) }
      ; component-isEquivalence = λ j → ≃→isEquivalence (obs j) }
    where
      obs : (j : type (Judgment 𝒥)) → ⌞ Γ ⟨ j ⟩ ⌟ ≃ ⌞ Δ ⟨ j ⟩ ⌟
      obs j = observe ⦃ []Type-hasEquality ⦄ (Semifunctor-Equality.objects≈ W j)

      comp : (j : type (Judgment 𝒥)) → ⌞ Γ ⟨ j ⟩ ⌟ → ⌞ Δ ⟨ j ⟩ ⌟
      comp j = there (obs j)

      natural~ : {j₀ j₁ : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀ j₁))
               → Δ ⟨ f ⟩ ∘ comp j₀ ~ comp j₁ ∘ Γ ⟨ f ⟩
      natural~ {j₀} {j₁} f x =
           ap (λ h → h (comp j₀ x)) (sym (Semifunctor-Equality.map≈ W j₀ j₁ f))
        ⨾  trHomOnPaths (Γ ⟨ j₀ ⟩) (Δ ⟨ j₀ ⟩) (Γ ⟨ j₁ ⟩) (Δ ⟨ j₁ ⟩)
                        (Semifunctor-Equality.objects≈ W j₀) (Semifunctor-Equality.objects≈ W j₁) (Γ ⟨ f ⟩) x

  ≈→contextEquivalence-isSection :
      {Γ Δ : Context 𝒥 i} (w : ContextEquivalence Γ Δ)
    → ≈→contextEquivalence (contextEquivalence→≈ w) ＝ w
  ≈→contextEquivalence-isSection {Γ} {Δ} w =
    eqContextEquivalence (≈→contextEquivalence (contextEquivalence→≈ w)) w
      (eq (record { component≈ = λ j → funExt (pointwise j) }))
    where
      e : (j : type (Judgment 𝒥)) → ⌞ Γ ⟨ j ⟩ ⌟ ≃ ⌞ Δ ⟨ j ⟩ ⌟
      e j = isEquivalence→≃ (ContextEquivalence.component-isEquivalence w j)

      pointwise : (j : type (Judgment 𝒥)) (x : ⌞ Γ ⟨ j ⟩ ⌟)
                → there (observe ⦃ []Type-hasEquality ⦄ (eq (e j))) x ＝ (w ⟨ j ⟩) x
      pointwise j x = ap (λ v → there v x) (observe-eq ⦃ []Type-hasEquality ⦄ (e j))

  contextTotalSpace-Contractible :
      (Γ : Context 𝒥 i) → Contractible (∑[ Δ ∶ Context 𝒥 i ] ContextEquivalence Γ Δ)
  contextTotalSpace-Contractible Γ =
    retract-Contractible s r ε (equality-Contractible (Context.semifunctor Γ))
    where
      s : (∑[ Δ ∶ Context 𝒥 i ] ContextEquivalence Γ Δ)
        → ∑[ Ψ ∶ Semifunctor (semicategory 𝒥) (hSet-Semicategory i) ]
            (Context.semifunctor Γ ≈ Ψ)
      s (Δ , w) = Context.semifunctor Δ , contextEquivalence→≈ w

      r : (∑[ Ψ ∶ Semifunctor (semicategory 𝒥) (hSet-Semicategory i) ]
             (Context.semifunctor Γ ≈ Ψ))
        → ∑[ Δ ∶ Context 𝒥 i ] ContextEquivalence Γ Δ
      r (Ψ , W) = mkContext Ψ , ≈→contextEquivalence W

      ε : r ∘ s ~ id
      ε (Δ , w) = ap (λ v → (Δ , v)) (≈→contextEquivalence-isSection w)


module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄
  {o a : Level} {𝒥 : DependentSortVocabulary o a} where

  instance
    equalityContext : Equality Level (Context 𝒥)
    equalityContext =
      record { characterisation = λ {i} →
        fundamentalTheorem (ContextEquivalence {i = i} {j = i} {𝒥 = 𝒥})
                           (λ _ → identity)
                           contextTotalSpace-Contractible }



-- ============== Equality of context equivalences ==============

module _ ⦃ _ : FunExt ⦄
  {o a i j : Level} {𝒥 : DependentSortVocabulary o a}
  {Γ : Context 𝒥 i} {Δ : Context 𝒥 j} where

  record ContextEquivalenceEquality (e₀ e₁ : ContextEquivalence Γ Δ)
    : Type (o ⊔ a ⊔ i ⊔ j) where
    constructor mkContextEquivalenceEquality
    field
      morphism≈ : ContextMorphismEquality (ContextEquivalence.morphism e₀)
                                          (ContextEquivalence.morphism e₁)

  identityContextEquivalenceEquality :
      (e : ContextEquivalence Γ Δ) → ContextEquivalenceEquality e e
  identityContextEquivalenceEquality e =
    record { morphism≈ = refl≈ ⦃ equalityContextMorphism ⦄ }

  instance
    sameyContextEquivalence : Samey 𝟙₀ (λ _ → ContextEquivalence Γ Δ)
    sameyContextEquivalence = record { samey = ContextEquivalenceEquality }

  private
    contextEquivalenceTotalSpace-Contractible :
        (e₀ : ContextEquivalence Γ Δ)
      → Contractible (∑[ e₁ ∶ ContextEquivalence Γ Δ ] ContextEquivalenceEquality e₀ e₁)
    contextEquivalenceTotalSpace-Contractible e₀ =
      retract-Contractible toParts fromParts roundTrip
        (∑-Contractible-over
          (equality-Contractible ⦃ w = equalityContextMorphism ⦄
             (ContextEquivalence.morphism e₀))
          (→-Contractible
             (λ j → inhabited-proposition→contractible ⦃ isEquivalenceIsProposition ⦄
                      (ContextEquivalence.component-isEquivalence e₀ j))))
      where
        Base : Type (o ⊔ a ⊔ i ⊔ j)
        Base = ∑[ α ∶ Γ ⇒ Δ ]
                 ContextMorphismEquality (ContextEquivalence.morphism e₀) α

        Parts : Type (o ⊔ a ⊔ i ⊔ j)
        Parts = ∑[ w ∶ Base ]
                  ((j' : type (Judgment 𝒥))
                   → isEquivalence (ContextMorphism.component (p₀ w) j'))

        toParts : (∑[ e₁ ∶ ContextEquivalence Γ Δ ] ContextEquivalenceEquality e₀ e₁)
                → Parts
        toParts (mkContextEquivalence α w , q) =
          (α , ContextEquivalenceEquality.morphism≈ q) , w

        fromParts : Parts
                  → ∑[ e₁ ∶ ContextEquivalence Γ Δ ] ContextEquivalenceEquality e₀ e₁
        fromParts ((α , q) , w) =
          mkContextEquivalence α w , record { morphism≈ = q }

        roundTrip : fromParts ∘ toParts ~ id
        roundTrip (mkContextEquivalence α w , q) = refl

  instance
    equalityContextEquivalence : Equality 𝟙₀ (λ _ → ContextEquivalence Γ Δ)
    equalityContextEquivalence =
      record { characterisation =
                 fundamentalTheorem ContextEquivalenceEquality
                                    identityContextEquivalenceEquality
                                    contextEquivalenceTotalSpace-Contractible }



-- ============== Closure of context equivalences under sums ==============

module _ ⦃ _ : FunExt ⦄ {o a : Level} {𝒥 : DependentSortVocabulary o a} where

  sumContextEquivalence : {i₀ i₁ j₀ j₁ : Level}
                          {Γ₀ : Context 𝒥 i₀} {Γ₁ : Context 𝒥 i₁}
                          {Δ₀ : Context 𝒥 j₀} {Δ₁ : Context 𝒥 j₁}
                        → ContextEquivalence Γ₀ Γ₁ → ContextEquivalence Δ₀ Δ₁
                        → ContextEquivalence (Γ₀ + Δ₀) (Γ₁ + Δ₁)
  sumContextEquivalence {Γ₀ = Γ₀} {Γ₁ = Γ₁} {Δ₀ = Δ₀} {Δ₁ = Δ₁} e d =
    record
      { morphism = α
      ; component-isEquivalence = λ j →
          ~transfer-isEquivalence (bimapEquiv j) (pointwise j) }
    where
      α = sumContextMorphism (ContextEquivalence.morphism e) (ContextEquivalence.morphism d)

      bimapEquiv : (j : type (Judgment 𝒥)) → ⌞ (Γ₀ + Δ₀) ⟨ j ⟩ ⌟ ≃ ⌞ (Γ₁ + Δ₁) ⟨ j ⟩ ⌟
      bimapEquiv j =
        bimap (isEquivalence→≃ (ContextEquivalence.component-isEquivalence e j))
              (isEquivalence→≃ (ContextEquivalence.component-isEquivalence d j))

      pointwise : (j : type (Judgment 𝒥)) → there (bimapEquiv j) ~ (α ⟨ j ⟩)
      pointwise j (inl x) = refl
      pointwise j (inr y) = refl

  assocSumContextEquivalence : {i j k : Level}
                            {Γ : Context 𝒥 i} {Δ : Context 𝒥 j} {Ψ : Context 𝒥 k}
                          → ContextEquivalence ((Γ + Δ) + Ψ) (Γ + (Δ + Ψ))
  assocSumContextEquivalence {Γ = Γ} {Δ = Δ} {Ψ = Ψ} =
    record
      { morphism = record
          { component = λ j → there assocSum
          ; natural = λ f → funExt (natural~ f) }
      ; component-isEquivalence = λ j → ≃→isEquivalence assocSum }
    where
      natural~ : {j₀ j₁ : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀ j₁))
               → (Γ + (Δ + Ψ)) ⟨ f ⟩ ∘ there assocSum ~ there assocSum ∘ ((Γ + Δ) + Ψ) ⟨ f ⟩
      natural~ f (inl (inl x)) = refl
      natural~ f (inl (inr y)) = refl
      natural~ f (inr z) = refl

