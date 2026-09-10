module Sequent.Morphism where

open import Prelude
open import Axioms
open import Homotopy.SetQuotient.Nominal
open import Structure.Associativity
open import Structure.Composable
open import Structure.Identity
open import Structure.Reasoning
open import Structure.Symmetric
open import Homotopy.Equality
open import Homotopy.Levels
open import Homotopy.StructuredType
open import Syntax.Arrowable
open import Algebra.Wild.Semicategory
open import Algebra.Wild.Semifunctor
open import Structure.Semicategorical using (Semicategorical)
open Semicategory

open import DependentSortVocabulary
open import Context
open import Context.Morphism
open import Context.Extension
open import Context.ExtensionMorphism
open import Sequent

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
          (∙-associative {g = sequentMorphism g}) }

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


  toSequentMorphism-identity : {i : Level} {s : Sequent 𝒥 i}
                             → SequentMorphism.sequentMorphism
                                 (toSequentMorphism (sequentEquivalence-identity {s = s}))
                               ≈ identity
  toSequentMorphism-identity {s = mkSequent Γ E} = map⋊-identity E

  toSequentMorphism-identity-at :
      {i : Level} {s : Sequent 𝒥 i} (j : type (Judgment 𝒥))
      (z : ⌞ extendedContext s ⟨ j ⟩ ⌟)
    → (SequentMorphism.sequentMorphism
         (toSequentMorphism (sequentEquivalence-identity {s = s})) ⟨ j ⟩) z
      ＝ z
  toSequentMorphism-identity-at {s = mkSequent Γ E} = map⋊-identity-at E

  toSequentMorphism-isEquivalence :
      {i₀ i₁ : Level} {s₀ : Sequent 𝒥 i₀} {s₁ : Sequent 𝒥 i₁}
      (e : SequentEquivalence s₀ s₁) (j : type (Judgment 𝒥))
    → isEquivalence (toSequentMorphism e ⟨ j ⟩)
  toSequentMorphism-isEquivalence {s₀ = mkSequent Γ E₀} {s₁ = mkSequent Δ E₁} e j =
    map⋊-isEquivalence (SequentEquivalence.contextEquivalence e)
      E₀ E₁ (SequentEquivalence.extensionOrCollapseEquality e) j

-- =================== Equality of sequents ===================

instance
  sameySequent : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
               → {o a : Level} {𝒥 : DependentSortVocabulary o a}
               → Samey Level (Sequent 𝒥)
  sameySequent = record { samey = SequentEquivalence }

module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a i : Level} {𝒥 : DependentSortVocabulary o a} where

  sequentTotalSpace-Contractible :
      (s₀ : Sequent 𝒥 i) → Contractible (∑[ s₁ ∶ Sequent 𝒥 i ] SequentEquivalence s₀ s₁)
  sequentTotalSpace-Contractible (mkSequent Γ E₀) =
    retract-Contractible toParts fromParts roundTrip
      (∑-Contractible
         (equality-Contractible Γ)
         (λ p → equality-Contractible
                  (mapExtensionOrCollapse (ContextEquivalence.morphism (p₁ p)) E₀)))
    where
      Parts : Type (o ⊔ a ⊔ lsuc i)
      Parts = ∑[ p ∶ (∑[ Δ ∶ Context 𝒥 i ] ContextEquivalence Γ Δ) ]
                ∑[ E₁ ∶ ExtensionOrCollapse (p₀ p) ]
                  (mapExtensionOrCollapse (ContextEquivalence.morphism (p₁ p)) E₀ ≈ E₁)

      toParts : (∑[ s₁ ∶ Sequent 𝒥 i ] SequentEquivalence (mkSequent Γ E₀) s₁) → Parts
      toParts (mkSequent Δ E₁ , mkStrictSequentEquivalence ce q) = (Δ , ce) , (E₁ , q)

      fromParts : Parts → ∑[ s₁ ∶ Sequent 𝒥 i ] SequentEquivalence (mkSequent Γ E₀) s₁
      fromParts ((Δ , ce) , (E₁ , q)) = mkSequent Δ E₁ , mkStrictSequentEquivalence ce q

      roundTrip : fromParts ∘ toParts ~ id
      roundTrip (mkSequent Δ E₁ , mkStrictSequentEquivalence ce q) = refl

module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a : Level} {𝒥 : DependentSortVocabulary o a} where

  instance
    equalitySequent : Equality Level (Sequent 𝒥)
    equalitySequent =
      record { characterisation = λ {i} →
        fundamentalTheorem (SequentEquivalence {i₀ = i} {i₁ = i} {𝒥 = 𝒥})
                           (λ _ → sequentEquivalence-identity)
                           sequentTotalSpace-Contractible }


-- =============== Equality of sequent morphisms ===============

record SequentMorphismEquality
  ⦃ _ : FunExt ⦄
  ⦃ _ : AllSetQuotients ⦄
  {o a i₀ i₁ : Level}
  {𝒥 : DependentSortVocabulary o a}
  {s₀ : Sequent 𝒥 i₀}
  {s₁ : Sequent 𝒥 i₁}
  (α β : SequentMorphism s₀ s₁)
  : Type (o ⊔ a ⊔ i₀ ⊔ i₁) where
  constructor mkSequentMorphismEquality
  field
    morphism≈ : SequentMorphism.sequentMorphism α ≈ SequentMorphism.sequentMorphism β
open SequentMorphismEquality

instance
  sameySequentMorphism : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
                       → {o a i₀ i₁ : Level} {𝒥 : DependentSortVocabulary o a}
                         {s₀ : Sequent 𝒥 i₀} {s₁ : Sequent 𝒥 i₁}
                       → Samey 𝟙₀ (λ _ → SequentMorphism s₀ s₁)
  sameySequentMorphism = record { samey = SequentMorphismEquality }

module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a i₀ i₁ : Level} {𝒥 : DependentSortVocabulary o a}
  {s₀ : Sequent 𝒥 i₀} {s₁ : Sequent 𝒥 i₁} where

  sequentMorphismTotalSpace-Contractible :
      (α : SequentMorphism s₀ s₁)
    → Contractible (∑[ β ∶ SequentMorphism s₀ s₁ ] SequentMorphismEquality α β)
  sequentMorphismTotalSpace-Contractible (mkSequentMorphism f) =
    retract-Contractible toParts fromParts roundTrip
      (equality-Contractible ⦃ w = equalityContextMorphism ⦄ f)
    where
      toParts : (∑[ β ∶ SequentMorphism s₀ s₁ ] SequentMorphismEquality (mkSequentMorphism f) β)
              → ∑[ g ∶ ContextMorphism (extendedContext s₀) (extendedContext s₁) ] (f ≈ g)
      toParts (mkSequentMorphism g , mkSequentMorphismEquality q) = g , q

      fromParts : (∑[ g ∶ ContextMorphism (extendedContext s₀) (extendedContext s₁) ] (f ≈ g))
                → ∑[ β ∶ SequentMorphism s₀ s₁ ] SequentMorphismEquality (mkSequentMorphism f) β
      fromParts (g , q) = mkSequentMorphism g , mkSequentMorphismEquality q

      roundTrip : fromParts ∘ toParts ~ id
      roundTrip (mkSequentMorphism g , mkSequentMorphismEquality q) = refl

  instance
    equalitySequentMorphism : Equality 𝟙₀ (λ _ → SequentMorphism s₀ s₁)
    equalitySequentMorphism =
      record { characterisation =
                 fundamentalTheorem (SequentMorphismEquality {s₀ = s₀} {s₁ = s₁})
                   (λ _ → mkSequentMorphismEquality (refl≈ ⦃ equalityContextMorphism ⦄))
                   sequentMorphismTotalSpace-Contractible }

  sequentMorphismEquality-isProposition :
      {α β : SequentMorphism s₀ s₁} → isProposition (SequentMorphismEquality α β)
  sequentMorphismEquality-isProposition =
    retract-level morphism≈ mkSequentMorphismEquality (λ _ → refl)
      contextMorphismEquality-isProposition

  sequentMorphism-isSet : isSet (SequentMorphism s₀ s₁)
  sequentMorphism-isSet =
    path-type (λ α β →
      ≃-level (sym (observe-≃ ⦃ equalitySequentMorphism ⦄))
              sequentMorphismEquality-isProposition)

module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a : Level} {𝒥 : DependentSortVocabulary o a} where

  sequentMorphismEquivalence :
      {i₀ i₁ : Level} {s₀ : Sequent 𝒥 i₀} {s₁ : Sequent 𝒥 i₁}
      (T : SequentMorphism s₀ s₁)
      (w : (j : type (Judgment 𝒥)) → isEquivalence (T ⟨ j ⟩))
    → ContextEquivalence (extendedContext s₀) (extendedContext s₁)
  sequentMorphismEquivalence T w =
    mkContextEquivalence (SequentMorphism.sequentMorphism T) w

  inverseSequentMorphism :
      {i₀ i₁ : Level} {s₀ : Sequent 𝒥 i₀} {s₁ : Sequent 𝒥 i₁}
      (T : SequentMorphism s₀ s₁)
      (w : (j : type (Judgment 𝒥)) → isEquivalence (T ⟨ j ⟩))
    → SequentMorphism s₁ s₀
  inverseSequentMorphism T w =
    mkSequentMorphism (inverseContextMorphism (sequentMorphismEquivalence T w))

  precompose-isEquivalence :
      {i₀ i₁ i₂ : Level} {s₀ : Sequent 𝒥 i₀} {s₁ : Sequent 𝒥 i₁} {s₂ : Sequent 𝒥 i₂}
      (T : SequentMorphism s₀ s₁)
      (w : (j : type (Judgment 𝒥)) → isEquivalence (T ⟨ j ⟩))
    → isEquivalence (λ (g : SequentMorphism s₁ s₂) → g ∙ T)
  precompose-isEquivalence T w =
    makeIsEquivalence
      (record { sectionBack = λ h → h ∙ inverseSequentMorphism T w
              ; isSection = isSection~ })
      (record { retractionBack = λ h → h ∙ inverseSequentMorphism T w
              ; isRetraction = isRetraction~ })
    where
      isSection~ : (h : SequentMorphism _ _) → (h ∙ inverseSequentMorphism T w) ∙ T ＝ h
      isSection~ h =
        eq (mkSequentMorphismEquality
              (record { component≈ = λ j → funExt (λ z →
                 ap (h ⟨ j ⟩)
                    (backwardsRetraction (sequentMorphismEquivalence T w) j z)) }))

      isRetraction~ : (g : SequentMorphism _ _) → (g ∙ T) ∙ inverseSequentMorphism T w ＝ g
      isRetraction~ g =
        eq (mkSequentMorphismEquality
              (record { component≈ = λ j → funExt (λ z →
                 ap (g ⟨ j ⟩)
                    (backwardsSection (sequentMorphismEquivalence T w) j z)) }))


-- ============== Equality of sequent equivalences ==============

record SequentEquivalenceEquality
  ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a i₀ i₁ : Level} {𝒥 : DependentSortVocabulary o a}
  {s₀ : Sequent 𝒥 i₀} {s₁ : Sequent 𝒥 i₁}
  (e₀ e₁ : SequentEquivalence s₀ s₁)
  : Type (o ⊔ a ⊔ i₀ ⊔ i₁) where
  constructor mkSequentEquivalenceEquality
  field
    contextEquivalence≈ :
      ContextEquivalenceEquality (SequentEquivalence.contextEquivalence e₀)
                                  (SequentEquivalence.contextEquivalence e₁)

module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a i₀ i₁ : Level} {𝒥 : DependentSortVocabulary o a}
  {s₀ : Sequent 𝒥 i₀} {s₁ : Sequent 𝒥 i₁} where

  identitySequentEquivalenceEquality :
      (e : SequentEquivalence s₀ s₁) → SequentEquivalenceEquality e e
  identitySequentEquivalenceEquality e =
    record { contextEquivalence≈ =
               identityContextEquivalenceEquality
                 (SequentEquivalence.contextEquivalence e) }

  instance
    sameySequentEquivalence : Samey 𝟙₀ (λ _ → SequentEquivalence s₀ s₁)
    sameySequentEquivalence = record { samey = SequentEquivalenceEquality }

  private
    sequentEquivalenceTotalSpace-Contractible :
        (e₀ : SequentEquivalence s₀ s₁)
      → Contractible (∑[ e₁ ∶ SequentEquivalence s₀ s₁ ]
                        SequentEquivalenceEquality e₀ e₁)
    sequentEquivalenceTotalSpace-Contractible e₀ =
      retract-Contractible toParts fromParts roundTrip
        (∑-Contractible-over
           (equality-Contractible ⦃ w = equalityContextEquivalence ⦄
              (SequentEquivalence.contextEquivalence e₀))
           (inhabited-proposition→contractible
              ⦃ extensionOrCollapseEquality-isProposition ⦄
              (SequentEquivalence.extensionOrCollapseEquality e₀)))
      where
        Base : Type (o ⊔ a ⊔ i₀ ⊔ i₁)
        Base = ∑[ ce ∶ ContextEquivalence (Sequent.context s₀) (Sequent.context s₁) ]
                 ContextEquivalenceEquality
                   (SequentEquivalence.contextEquivalence e₀) ce

        Parts : Type (o ⊔ a ⊔ i₀ ⊔ i₁)
        Parts = ∑[ w ∶ Base ]
                  ExtensionOrCollapseEquality
                    (mapExtensionOrCollapse
                       (ContextEquivalence.morphism (p₀ w))
                       (Sequent.extensionOrCollapse s₀))
                    (Sequent.extensionOrCollapse s₁)

        toParts : (∑[ e₁ ∶ SequentEquivalence s₀ s₁ ]
                     SequentEquivalenceEquality e₀ e₁)
                → Parts
        toParts (mkStrictSequentEquivalence ce k , q) =
          (ce , SequentEquivalenceEquality.contextEquivalence≈ q) , k

        fromParts : Parts
                  → ∑[ e₁ ∶ SequentEquivalence s₀ s₁ ]
                      SequentEquivalenceEquality e₀ e₁
        fromParts ((ce , q) , k) =
          mkStrictSequentEquivalence ce k , record { contextEquivalence≈ = q }

        roundTrip : fromParts ∘ toParts ~ id
        roundTrip (mkStrictSequentEquivalence ce k , q) = refl

  instance
    equalitySequentEquivalence : Equality 𝟙₀ (λ _ → SequentEquivalence s₀ s₁)
    equalitySequentEquivalence =
      record { characterisation =
                 fundamentalTheorem SequentEquivalenceEquality
                                    identitySequentEquivalenceEquality
                                    sequentEquivalenceTotalSpace-Contractible }

