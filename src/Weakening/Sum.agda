module Weakening.Sum where

open import Prelude
open import Axioms
open import Homotopy.SetQuotient
open import Structure.Associativity
open import Structure.Composable
open import Structure.Identity
open import Structure.PreservesComposition
open import Structure.Symmetric
open import Homotopy.StructuredType
open import Algebra.Wild.Semi
open Semicategory.Semicategory
open import Algebra.Wild.TruncatedTypeSemicategory
open import Homotopy.Equality
open import Homotopy.Levels
open import Foundation.Sum.Equivalence
open import Structure.Bimappable

open import DependentSortVocabulary
open import Context
open import Context.Morphism
open import Context.Extension
open import Context.ExtensionMorphism
open import Sequent
open import Sequent.Morphism
open import Weakening.Sequent


-- =============== Morphisms of weakened sequents ===============

module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄ {o a : Level} {𝒥 : DependentSortVocabulary o a} where

  weakenedSequentMorphism :
      {k₀ k₁ l₀ l₁ : Level} {H₀ : Context 𝒥 k₀} {H₁ : Context 𝒥 k₁}
      {s₀ : Sequent 𝒥 l₀} {s₁ : Sequent 𝒥 l₁}
    → H₀ ⇒ H₁ → SequentMorphism s₀ s₁
    → SequentMorphism (weakenSequent H₀ s₀) (weakenSequent H₁ s₁)
  weakenedSequentMorphism {H₀ = H₀} {H₁ = H₁} {s₀ = s₀} {s₁ = s₁} η α =
    mkSequentMorphism
      (gatherExtended H₁ s₁
        ∙ (sumContextMorphism η (SequentMorphism.sequentMorphism α)
        ∙ distributeExtended H₀ s₀))

  weakenedSequentMorphism-composition :
      {k₀ k₁ k₂ l₀ l₁ l₂ : Level}
      {H₀ : Context 𝒥 k₀} {H₁ : Context 𝒥 k₁} {H₂ : Context 𝒥 k₂}
      {s₀ : Sequent 𝒥 l₀} {s₁ : Sequent 𝒥 l₁} {s₂ : Sequent 𝒥 l₂}
      (η : H₀ ⇒ H₁) (θ : H₁ ⇒ H₂)
      (α : SequentMorphism s₀ s₁) (β : SequentMorphism s₁ s₂)
    → weakenedSequentMorphism (θ ∙ η) (α ⨾ β)
      ＝ weakenedSequentMorphism η α ⨾ weakenedSequentMorphism θ β
  weakenedSequentMorphism-composition {H₀ = H₀} {H₁ = H₁} {H₂ = H₂} {s₀ = s₀} {s₁ = s₁} {s₂ = s₂} η θ α β =
    ap mkSequentMorphism (eq (record { component≈ = λ j → funExt (pointwise j) }))
    where
      α' = SequentMorphism.sequentMorphism α
      β' = SequentMorphism.sequentMorphism β

      onSum : (j : type (Judgment 𝒥)) (u : ⌞ (H₀ + extendedContext s₀) ⟨ j ⟩ ⌟)
            → (sumContextMorphism (θ ∙ η) (β' ∙ α') ⟨ j ⟩) u
              ＝ (sumContextMorphism θ β' ⟨ j ⟩) ((sumContextMorphism η α' ⟨ j ⟩) u)
      onSum j (inl h) = refl
      onSum j (inr v) = refl

      pointwise : (j : type (Judgment 𝒥)) (w : ⌞ extendedContext (weakenSequent H₀ s₀) ⟨ j ⟩ ⌟)
                → (weakenedSequentMorphism (θ ∙ η) (α ⨾ β) ⟨ j ⟩) w
                  ＝ ((weakenedSequentMorphism η α ⨾ weakenedSequentMorphism θ β) ⟨ j ⟩) w
      pointwise j w =
           ap (gatherExtended H₂ s₂ ⟨ j ⟩) (onSum j ((distributeExtended H₀ s₀ ⟨ j ⟩) w))
        ⨾  ap (λ v → (gatherExtended H₂ s₂ ⟨ j ⟩) ((sumContextMorphism θ β' ⟨ j ⟩) v))
              (sym (distribute-gather H₁ s₁ j
                      ((sumContextMorphism η α' ⟨ j ⟩) ((distributeExtended H₀ s₀ ⟨ j ⟩) w))))

  sumExtensionEquality :
      {k₀ k₁ l₀ l₁ : Level} {H₀ : Context 𝒥 k₀} {H₁ : Context 𝒥 k₁}
      {Γ₀ : Context 𝒥 l₀} {Γ₁ : Context 𝒥 l₁}
      (η : H₀ ⇒ H₁) (ζ : Γ₀ ⇒ Γ₁)
      {e₀ : Extension Γ₀} {e₁ : Extension Γ₁}
    → mapExtension ζ e₀ ≈ e₁
    → mapExtension (sumContextMorphism η ζ) (mapExtension (inrContext {Γ = H₀} {Δ = Γ₀}) e₀)
      ≈ mapExtension (inrContext {Γ = H₁} {Δ = Γ₁}) e₁
  sumExtensionEquality η ζ {mkExtension jf a₀} {mkExtension jf₁ a₁} (mkExtensionEquality refl q) =
    mkExtensionEquality refl
      (record { component≈ = λ j → funExt (λ z →
          ap inr (ap (λ h → h z) (ContextMorphismEquality.component≈ q j))) })

  sumCollapseEquality :
      {k₀ k₁ l₀ l₁ : Level} {H₀ : Context 𝒥 k₀} {H₁ : Context 𝒥 k₁}
      {Γ₀ : Context 𝒥 l₀} {Γ₁ : Context 𝒥 l₁}
      (η : H₀ ⇒ H₁) (ζ : Γ₀ ⇒ Γ₁)
      {c₀ : Collapse Γ₀} {c₁ : Collapse Γ₁}
    → mapCollapse ζ c₀ ≈ c₁
    → mapCollapse (sumContextMorphism η ζ) (mapCollapse (inrContext {Γ = H₀} {Δ = Γ₀}) c₀)
      ≈ mapCollapse (inrContext {Γ = H₁} {Δ = Γ₁}) c₁
  sumCollapseEquality η ζ {mkCollapse jf a₀} {mkCollapse jf₁ a₁} (mkCollapseEquality refl q) =
    mkCollapseEquality refl
      (record { component≈ = λ j → funExt (λ z →
          ap inr (ap (λ h → h z) (ContextMorphismEquality.component≈ q j))) })

  sumEocEquality :
      {k₀ k₁ l₀ l₁ : Level} {H₀ : Context 𝒥 k₀} {H₁ : Context 𝒥 k₁}
      {Γ₀ : Context 𝒥 l₀} {Γ₁ : Context 𝒥 l₁}
      (η : H₀ ⇒ H₁) (ζ : Γ₀ ⇒ Γ₁)
      {E₀ : ExtensionOrCollapse Γ₀} {E₁ : ExtensionOrCollapse Γ₁}
    → mapExtensionOrCollapse ζ E₀ ≈ E₁
    → mapExtensionOrCollapse (sumContextMorphism η ζ)
        (mapExtensionOrCollapse (inrContext {Γ = H₀} {Δ = Γ₀}) E₀)
      ≈ mapExtensionOrCollapse (inrContext {Γ = H₁} {Δ = Γ₁}) E₁
  sumEocEquality η ζ {E₀ = extend e₀} (extendEq w) = extendEq (sumExtensionEquality η ζ w)
  sumEocEquality η ζ {E₀ = collapse c₀} (collapseEq w) = collapseEq (sumCollapseEquality η ζ w)

  weakenedSequentEquivalence :
      {k₀ k₁ l₀ l₁ : Level} {H₀ : Context 𝒥 k₀} {H₁ : Context 𝒥 k₁}
      {s₀ : Sequent 𝒥 l₀} {s₁ : Sequent 𝒥 l₁}
    → ContextEquivalence H₀ H₁ → SequentEquivalence s₀ s₁
    → SequentEquivalence (weakenSequent H₀ s₀) (weakenSequent H₁ s₁)
  weakenedSequentEquivalence he (mkStrictSequentEquivalence ce eoc) =
    mkStrictSequentEquivalence
      (sumContextEquivalence he ce)
      (sumEocEquality (ContextEquivalence.morphism he) (ContextEquivalence.morphism ce) eoc)

  assocEocEquality :
      {k₀ k₁ l : Level} (H₁ : Context 𝒥 k₀) (H₀ : Context 𝒥 k₁) {Γ : Context 𝒥 l}
      (E : ExtensionOrCollapse Γ)
    → mapExtensionOrCollapse (ContextEquivalence.morphism (assocSumContextEquivalence {Γ = H₁} {Δ = H₀} {Ψ = Γ}))
        (mapExtensionOrCollapse (inrContext {Γ = H₁ + H₀} {Δ = Γ}) E)
      ≈ mapExtensionOrCollapse (inrContext {Γ = H₁} {Δ = H₀ + Γ})
          (mapExtensionOrCollapse (inrContext {Γ = H₀} {Δ = Γ}) E)
  assocEocEquality H₁ H₀ (extend (mkExtension jf args)) =
    extendEq (mkExtensionEquality refl
      (record { component≈ = λ j → funExt (λ z → refl) }))
  assocEocEquality H₁ H₀ (collapse (mkCollapse jf args)) =
    collapseEq (mkCollapseEquality refl
      (record { component≈ = λ j → funExt (λ z → refl) }))

  assocWeakenSequentEquivalence :
      {k₀ k₁ l : Level} (H₁ : Context 𝒥 k₀) (H₀ : Context 𝒥 k₁) (s : Sequent 𝒥 l)
    → SequentEquivalence (weakenSequent (H₁ + H₀) s)
                         (weakenSequent H₁ (weakenSequent H₀ s))
  assocWeakenSequentEquivalence H₁ H₀ s =
    mkStrictSequentEquivalence assocSumContextEquivalence
      (assocEocEquality H₁ H₀ (Sequent.extensionOrCollapse s))


  map⋊-sum :
      {k₀ k₁ l₀ l₁ : Level} {H₀ : Context 𝒥 k₀} {H₁ : Context 𝒥 k₁}
      {Γ₀ : Context 𝒥 l₀} {Γ₁ : Context 𝒥 l₁}
      (η : H₀ ⇒ H₁) (ζ : Γ₀ ⇒ Γ₁)
      (E₀ : ExtensionOrCollapse Γ₀) (E₁ : ExtensionOrCollapse Γ₁)
      (w : mapExtensionOrCollapse ζ E₀ ≈ E₁)
    → map⋊ (sumContextMorphism η ζ)
           (mapExtensionOrCollapse (inrContext {Γ = H₀} {Δ = Γ₀}) E₀)
           (mapExtensionOrCollapse (inrContext {Γ = H₁} {Δ = Γ₁}) E₁)
           (sumEocEquality η ζ w)
      ＝ gatherExtended H₁ (mkSequent Γ₁ E₁)
        ∙ (sumContextMorphism η (map⋊ ζ E₀ E₁ w)
        ∙ distributeExtended H₀ (mkSequent Γ₀ E₀))
  map⋊-sum {H₀ = H₀} {H₁ = H₁} {Γ₀ = Γ₀} {Γ₁ = Γ₁} η ζ
    (extend (mkExtension jf a₀)) (extend (mkExtension jf₁ a₁))
    (extendEq (mkExtensionEquality refl q)) =
    eq (record { component≈ = λ j → funExt (pointwise j) })
    where
      E₀' = extend (mkExtension jf a₀)
      E₁' = extend (mkExtension jf a₁)

      pointwise : (j : type (Judgment 𝒥))
                  (w : ⌞ ((H₀ + Γ₀) ⋊ mapExtensionOrCollapse (inrContext {Γ = H₀} {Δ = Γ₀}) E₀') ⟨ j ⟩ ⌟)
                → (map⋊ (sumContextMorphism η ζ)
                        (mapExtensionOrCollapse (inrContext {Γ = H₀} {Δ = Γ₀}) E₀')
                        (mapExtensionOrCollapse (inrContext {Γ = H₁} {Δ = Γ₁}) E₁')
                        (sumEocEquality η ζ (extendEq (mkExtensionEquality refl q))) ⟨ j ⟩) w
                  ＝ ((gatherExtended H₁ (mkSequent Γ₁ E₁')
                      ∙ (sumContextMorphism η (map⋊ ζ E₀' E₁' (extendEq (mkExtensionEquality refl q)))
                      ∙ distributeExtended H₀ (mkSequent Γ₀ E₀'))) ⟨ j ⟩) w
      pointwise j (inl (inl h)) = refl
      pointwise j (inl (inr v)) = refl
      pointwise j (inr p) = refl
  map⋊-sum {k₀} {k₁} {l₀} {l₁} {H₀ = H₀} {H₁ = H₁} {Γ₀ = Γ₀} {Γ₁ = Γ₁} η ζ
    (collapse col₀@(mkCollapse jf a₀)) (collapse col₁@(mkCollapse jf₁ a₁))
    (collapseEq w@(mkCollapseEquality refl q)) =
    eq (record { component≈ = pointwise })
    where
      addedCol₀ = mapCollapse (inrContext {Γ = H₀} {Δ = Γ₀}) col₀
      addedCol₁ = mapCollapse (inrContext {Γ = H₁} {Δ = Γ₁}) col₁

      lhs = map⋊ₖ (sumContextMorphism η ζ) addedCol₀ addedCol₁ (sumCollapseEquality η ζ w)
      inner = map⋊ₖ ζ col₀ col₁ w

      module Q₀ (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ (H₀ + Γ₀) ⟨ j ⟩ ⌟) (CollapseRelation addedCol₀ j)
      module Q₁ (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ (H₁ + Γ₁) ⟨ j ⟩ ⌟) (CollapseRelation addedCol₁ j)
      module QΓ₀ (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ Γ₀ ⟨ j ⟩ ⌟) (CollapseRelation col₀ j)
      module QΓ₁ (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ Γ₁ ⟨ j ⟩ ⌟) (CollapseRelation col₁ j)

      tgt : Context 𝒥 (o ⊔ (k₁ ⊔ l₁))
      tgt = (H₁ + Γ₁) ⋊ₖ addedCol₁

      tgt-isSet : (j : type (Judgment 𝒥)) → isSet ⌞ tgt ⟨ j ⟩ ⌟
      tgt-isSet j = level-proof (tgt ⟨ j ⟩)

      mid₀-isSet : (j : type (Judgment 𝒥)) → isSet ⌞ (H₀ + (Γ₀ ⋊ₖ col₀)) ⟨ j ⟩ ⌟
      mid₀-isSet j = level-proof ((H₀ + (Γ₀ ⋊ₖ col₀)) ⟨ j ⟩)

      innerTgt-isSet : (j : type (Judgment 𝒥)) → isSet ⌞ (Γ₁ ⋊ₖ col₁) ⟨ j ⟩ ⌟
      innerTgt-isSet j = level-proof ((Γ₁ ⋊ₖ col₁) ⟨ j ⟩)

      class₁ : (j : type (Judgment 𝒥)) → ⌞ (H₁ + Γ₁) ⟨ j ⟩ ⌟ → ⌞ tgt ⟨ j ⟩ ⌟
      class₁ j = [_] ⦃ Q₁.setQuotient j ⦄

      classΓ₁ : (j : type (Judgment 𝒥)) → ⌞ Γ₁ ⟨ j ⟩ ⌟ → ⌞ (Γ₁ ⋊ₖ col₁) ⟨ j ⟩ ⌟
      classΓ₁ j = [_] ⦃ QΓ₁.setQuotient j ⦄

      G : (j : type (Judgment 𝒥)) → ⌞ (H₁ + (Γ₁ ⋊ₖ col₁)) ⟨ j ⟩ ⌟ → ⌞ tgt ⟨ j ⟩ ⌟
      G j = gatherExtended H₁ (mkSequent Γ₁ (collapse col₁)) ⟨ j ⟩

      S : (j : type (Judgment 𝒥)) → ⌞ (H₀ + (Γ₀ ⋊ₖ col₀)) ⟨ j ⟩ ⌟ → ⌞ (H₁ + (Γ₁ ⋊ₖ col₁)) ⟨ j ⟩ ⌟
      S j = sumContextMorphism η inner ⟨ j ⟩

      chase : (j : type (Judgment 𝒥)) (u : ⌞ (H₀ + Γ₀) ⟨ j ⟩ ⌟)
            → (lhs ⟨ j ⟩) ([_] ⦃ Q₀.setQuotient j ⦄ u)
              ＝ ((gatherExtended H₁ (mkSequent Γ₁ (collapse col₁))
                  ∙ (sumContextMorphism η inner
                  ∙ distributeExtended H₀ (mkSequent Γ₀ (collapse col₀)))) ⟨ j ⟩)
                  ([_] ⦃ Q₀.setQuotient j ⦄ u)
      chase j (inl h) =
           ⁄-rec-β ⦃ Q₀.setQuotient j ⦄ ⦃ bset = tgt-isSet j ⦄
                   (class₁ j ∘ (sumContextMorphism η ζ ⟨ j ⟩)) _ (inl h)
        ⨾  sym (ap (λ v → G j (S j v))
                   (⁄-rec-β ⦃ Q₀.setQuotient j ⦄ ⦃ bset = mid₀-isSet j ⦄ _ _ (inl h)))
      chase j (inr x) =
           ⁄-rec-β ⦃ Q₀.setQuotient j ⦄ ⦃ bset = tgt-isSet j ⦄
                   (class₁ j ∘ (sumContextMorphism η ζ ⟨ j ⟩)) _ (inr x)
        ⨾  sym (   ap (λ v → G j (S j v))
                      (⁄-rec-β ⦃ Q₀.setQuotient j ⦄ ⦃ bset = mid₀-isSet j ⦄ _ _ (inr x))
                ⨾  ap (λ v → G j (inr v))
                      (⁄-rec-β ⦃ QΓ₀.setQuotient j ⦄ ⦃ bset = innerTgt-isSet j ⦄
                               (classΓ₁ j ∘ (ζ ⟨ j ⟩)) _ x)
                ⨾  ⁄-rec-β ⦃ QΓ₁.setQuotient j ⦄ ⦃ bset = tgt-isSet j ⦄
                           (class₁ j ∘ inr) _ ((ζ ⟨ j ⟩) x))

      pointwise : (j : type (Judgment 𝒥))
                → (lhs ⟨ j ⟩)
                  ＝ ((gatherExtended H₁ (mkSequent Γ₁ (collapse col₁))
                      ∙ (sumContextMorphism η inner
                      ∙ distributeExtended H₀ (mkSequent Γ₀ (collapse col₀)))) ⟨ j ⟩)
      pointwise j =
        funExt
          (⁄-elim-proposition ⦃ Q₀.setQuotient j ⦄
            _
            (λ _ → ＝-isLevel ⦃ tgt-isSet j ⦄)
            (chase j))

  map⋊-sum-onAdded :
      {k₀ k₁ l₀ l₁ : Level} {H₀ : Context 𝒥 k₀} {H₁ : Context 𝒥 k₁}
      {Γ₀ : Context 𝒥 l₀} {Γ₁ : Context 𝒥 l₁}
      (η : H₀ ⇒ H₁) (ζ : Γ₀ ⇒ Γ₁)
      (E₀ : ExtensionOrCollapse Γ₀) (E₁ : ExtensionOrCollapse Γ₁)
      (w : mapExtensionOrCollapse ζ E₀ ≈ E₁)
      (j : type (Judgment 𝒥)) (u : ⌞ H₀ ⟨ j ⟩ ⌟)
    → (map⋊ (sumContextMorphism η ζ)
            (mapExtensionOrCollapse (inrContext {Γ = H₀} {Δ = Γ₀}) E₀)
            (mapExtensionOrCollapse (inrContext {Γ = H₁} {Δ = Γ₁}) E₁)
            (sumEocEquality η ζ w) ⟨ j ⟩)
        ((→⋊ (weakenSequent H₀ (mkSequent Γ₀ E₀)) ⟨ j ⟩) (inl u))
      ＝ (→⋊ (weakenSequent H₁ (mkSequent Γ₁ E₁)) ⟨ j ⟩) (inl ((η ⟨ j ⟩) u))
  map⋊-sum-onAdded η ζ
    (extend (mkExtension jf a₀)) (extend (mkExtension jf₁ a₁))
    (extendEq (mkExtensionEquality refl q)) j u = refl
  map⋊-sum-onAdded {H₀ = H₀} {H₁ = H₁} {Γ₀ = Γ₀} {Γ₁ = Γ₁} η ζ
    (collapse col₀@(mkCollapse jf a₀)) (collapse col₁@(mkCollapse jf₁ a₁))
    (collapseEq w@(mkCollapseEquality refl q)) j u =
    ⁄-rec-β ⦃ Q₀.setQuotient j ⦄ ⦃ bset = tgt-isSet j ⦄
            (class₁ j ∘ (sumContextMorphism η ζ ⟨ j ⟩)) _ (inl u)
    where
      addedCol₀ = mapCollapse (inrContext {Γ = H₀} {Δ = Γ₀}) col₀
      addedCol₁ = mapCollapse (inrContext {Γ = H₁} {Δ = Γ₁}) col₁

      module Q₀ (j' : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ (H₀ + Γ₀) ⟨ j' ⟩ ⌟) (CollapseRelation addedCol₀ j')
      module Q₁ (j' : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ (H₁ + Γ₁) ⟨ j' ⟩ ⌟) (CollapseRelation addedCol₁ j')

      tgt-isSet : (j' : type (Judgment 𝒥)) → isSet ⌞ ((H₁ + Γ₁) ⋊ₖ addedCol₁) ⟨ j' ⟩ ⌟
      tgt-isSet j' = level-proof (((H₁ + Γ₁) ⋊ₖ addedCol₁) ⟨ j' ⟩)

      class₁ : (j' : type (Judgment 𝒥)) → ⌞ (H₁ + Γ₁) ⟨ j' ⟩ ⌟ → ⌞ ((H₁ + Γ₁) ⋊ₖ addedCol₁) ⟨ j' ⟩ ⌟
      class₁ j' = [_] ⦃ Q₁.setQuotient j' ⦄

  toSequentMorphism-weakened :
      {k₀ k₁ l₀ l₁ : Level} {H₀ : Context 𝒥 k₀} {H₁ : Context 𝒥 k₁}
      {s₀ : Sequent 𝒥 l₀} {s₁ : Sequent 𝒥 l₁}
      (he : ContextEquivalence H₀ H₁) (se : SequentEquivalence s₀ s₁)
    → toSequentMorphism (weakenedSequentEquivalence he se)
      ＝ weakenedSequentMorphism (ContextEquivalence.morphism he) (toSequentMorphism se)
  toSequentMorphism-weakened {s₀ = s₀} {s₁ = s₁} he se =
    ap mkSequentMorphism
       (map⋊-sum (ContextEquivalence.morphism he)
                 (ContextEquivalence.morphism (SequentEquivalence.contextEquivalence se))
                 (Sequent.extensionOrCollapse s₀) (Sequent.extensionOrCollapse s₁)
                 (SequentEquivalence.extensionOrCollapseEquality se))


