module Weakening.Reassociation where

open import Prelude
open import Axioms
open import Homotopy.SetQuotient.Nominal
open import Structure.Associativity
open import Structure.Composable
open import Structure.Identity
open import Structure.PreservesComposition
open import Structure.Symmetric
open import Homotopy.StructuredType
open import Algebra.Wild.Semicategory
open import Algebra.Wild.Semifunctor
open Semicategory
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
open import Weakening.Sum


-- =============== Reassociation against sums of sequent morphisms ===============

module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄ {o a : Level} {𝒥 : DependentSortVocabulary o a} where

  map⋊-→⋊ :
      {l₀ l₁ : Level} {Γ₀ : Context 𝒥 l₀} {Γ₁ : Context 𝒥 l₁}
      (α : Γ₀ ⇒ Γ₁)
      (E₀ : ExtensionOrCollapse Γ₀) (E₁ : ExtensionOrCollapse Γ₁)
      (w : mapExtensionOrCollapse α E₀ ≈ E₁)
      (j : type (Judgment 𝒥)) (v : ⌞ Γ₀ ⟨ j ⟩ ⌟)
    → (map⋊ α E₀ E₁ w ⟨ j ⟩) ((→⋊ (mkSequent Γ₀ E₀) ⟨ j ⟩) v)
      ＝ (→⋊ (mkSequent Γ₁ E₁) ⟨ j ⟩) ((α ⟨ j ⟩) v)
  map⋊-→⋊ α (extend (mkExtension jf a₀)) (extend (mkExtension jf₁ a₁))
    (extendEq (mkExtensionEquality refl q)) j v = refl
  map⋊-→⋊ {Γ₀ = Γ₀} {Γ₁ = Γ₁} α
    (collapse col₀@(mkCollapse jf a₀)) (collapse col₁@(mkCollapse jf₁ a₁))
    (collapseEq w@(mkCollapseEquality refl q)) j v = refl


module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a : Level} {𝒥 : DependentSortVocabulary o a}
  {k₀ k₁ l₀ l₁ : Level} (H₁ : Context 𝒥 k₀) (H₀ : Context 𝒥 k₁)
  {Γ₀ : Context 𝒥 l₀} {Γ₁ : Context 𝒥 l₁} where

  private
    aTsm : {l : Level} (s : Sequent 𝒥 l)
         → extendedContext (weakenSequent (H₁ + H₀) s)
           ⇒ extendedContext (weakenSequent H₁ (weakenSequent H₀ s))
    aTsm s = SequentMorphism.sequentMorphism
               (toSequentMorphism (assocWeakenSequentEquivalence H₁ H₀ s))

  map⋊-assoc-square : (E₀ : ExtensionOrCollapse Γ₀) (E₁ : ExtensionOrCollapse Γ₁)
       (μ : SequentMorphism (mkSequent Γ₀ E₀) (mkSequent Γ₁ E₁))
     → aTsm (mkSequent Γ₁ E₁)
         ∙ SequentMorphism.sequentMorphism
             (weakenedSequentMorphism {H₀ = H₁ + H₀} {H₁ = H₁ + H₀} identity μ)
       ＝ SequentMorphism.sequentMorphism
           (weakenedSequentMorphism {H₀ = H₁} {H₁ = H₁} identity
             (weakenedSequentMorphism {H₀ = H₀} {H₁ = H₀} identity μ))
         ∙ aTsm (mkSequent Γ₀ E₀)
  map⋊-assoc-square E₀'@(extend (mkExtension jf₀ a₀)) E₁'@(extend (mkExtension jf₁ a₁)) μ =
    eq (record { component≈ = λ j → funExt (λ { (inl (inl (inl h₁))) → refl
                                              ; (inl (inl (inr h₀))) → refl
                                              ; (inl (inr γ)) → tail j ((μ' ⟨ j ⟩) (inl γ))
                                              ; (inr p) → tail j ((μ' ⟨ j ⟩) (inr p)) }) })
    where
      μ' = SequentMorphism.sequentMorphism μ
      s₀ = mkSequent Γ₀ E₀'
      s₁ = mkSequent Γ₁ E₁'

      tail : (j : type (Judgment 𝒥)) (y : ⌞ extendedContext s₁ ⟨ j ⟩ ⌟)
           → ((aTsm s₁) ⟨ j ⟩) ((gatherExtended (H₁ + H₀) s₁ ⟨ j ⟩) (inr y))
             ＝ (gatherExtended H₁ (weakenSequent H₀ s₁) ⟨ j ⟩)
                 (inr ((gatherExtended H₀ s₁ ⟨ j ⟩) (inr y)))
      tail j (inl γ₁) = refl
      tail j (inr p₁) = refl

  map⋊-assoc-square E₀'@(extend (mkExtension jf₀ a₀)) E₁'@(collapse col₁@(mkCollapse jf₁ a₁)) μ =
    eq (record { component≈ = λ j → funExt (λ { (inl (inl (inl h₁))) → refl
                                              ; (inl (inl (inr h₀))) → refl
                                              ; (inl (inr γ)) → tail j ((μ' ⟨ j ⟩) (inl γ))
                                              ; (inr p) → tail j ((μ' ⟨ j ⟩) (inr p)) }) })
    where
      μ' = SequentMorphism.sequentMorphism μ
      s₀ = mkSequent Γ₀ E₀'
      s₁ = mkSequent Γ₁ E₁'

      extDT-isSet : (j : type (Judgment 𝒥))
                  → isSet ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ s₁)) ⟨ j ⟩ ⌟
      extDT-isSet j = level-proof (extendedContext (weakenSequent H₁ (weakenSequent H₀ s₁)) ⟨ j ⟩)

      tail : (j : type (Judgment 𝒥)) (y : ⌞ extendedContext s₁ ⟨ j ⟩ ⌟)
           → ((aTsm s₁) ⟨ j ⟩) ((gatherExtended (H₁ + H₀) s₁ ⟨ j ⟩) (inr y))
             ＝ (gatherExtended H₁ (weakenSequent H₀ s₁) ⟨ j ⟩)
                 (inr ((gatherExtended H₀ s₁ ⟨ j ⟩) (inr y)))
      tail j =
        ⁄-elim-proposition
          (λ y → ((aTsm s₁) ⟨ j ⟩) ((gatherExtended (H₁ + H₀) s₁ ⟨ j ⟩) (inr y))
                 ＝ (gatherExtended H₁ (weakenSequent H₀ s₁) ⟨ j ⟩)
                     (inr ((gatherExtended H₀ s₁ ⟨ j ⟩) (inr y))))
          (λ _ → ＝-isLevel ⦃ extDT-isSet j ⦄)
          chase
        where
          chase : (v₁ : ⌞ (Γ₁ ⟨ j ⟩) ⌟)
                → ((aTsm s₁) ⟨ j ⟩) ((gatherExtended (H₁ + H₀) s₁ ⟨ j ⟩)
                    (inr ([_] v₁)))
                  ＝ (gatherExtended H₁ (weakenSequent H₀ s₁) ⟨ j ⟩)
                      (inr ((gatherExtended H₀ s₁ ⟨ j ⟩) (inr ([_] v₁))))
          chase v₁ = refl

  map⋊-assoc-square E₀'@(collapse col₀@(mkCollapse jf₀ a₀)) E₁'@(extend (mkExtension jf₁ a₁)) μ =
    eq (record { component≈ = λ j → funExt
         (⁄-elim-proposition
           (λ w → (lhsMor ⟨ j ⟩) w ＝ (rhsMor ⟨ j ⟩) w)
           (λ _ → ＝-isLevel ⦃ extDT-isSet j ⦄)
           (λ { (inl (inl h₁)) → refl
              ; (inl (inr h₀)) → refl
              ; (inr γ) → tail j ((μ' ⟨ j ⟩) ([_] γ)) })) })
    where
      μ' = SequentMorphism.sequentMorphism μ
      s₀ = mkSequent Γ₀ E₀'
      s₁ = mkSequent Γ₁ E₁'

      extDT-isSet : (j : type (Judgment 𝒥))
                  → isSet ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ s₁)) ⟨ j ⟩ ⌟
      extDT-isSet j = level-proof (extendedContext (weakenSequent H₁ (weakenSequent H₀ s₁)) ⟨ j ⟩)

      G1 : (j : type (Judgment 𝒥))
         → ⌞ ((H₁ + H₀) + extendedContext s₁) ⟨ j ⟩ ⌟
         → ⌞ extendedContext (weakenSequent (H₁ + H₀) s₁) ⟨ j ⟩ ⌟
      G1 j = gatherExtended (H₁ + H₀) s₁ ⟨ j ⟩

      GD : (j : type (Judgment 𝒥))
         → ⌞ (H₁ + extendedContext (weakenSequent H₀ s₁)) ⟨ j ⟩ ⌟
         → ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ s₁)) ⟨ j ⟩ ⌟
      GD j = gatherExtended H₁ (weakenSequent H₀ s₁) ⟨ j ⟩

      G0 : (j : type (Judgment 𝒥))
         → ⌞ (H₀ + extendedContext s₁) ⟨ j ⟩ ⌟
         → ⌞ extendedContext (weakenSequent H₀ s₁) ⟨ j ⟩ ⌟
      G0 j = gatherExtended H₀ s₁ ⟨ j ⟩

      lhsMor = aTsm s₁
               ∙ SequentMorphism.sequentMorphism
                   (weakenedSequentMorphism {H₀ = H₁ + H₀} {H₁ = H₁ + H₀} identity μ)
      rhsMor = SequentMorphism.sequentMorphism
                 (weakenedSequentMorphism {H₀ = H₁} {H₁ = H₁} identity
                   (weakenedSequentMorphism {H₀ = H₀} {H₁ = H₀} identity μ))
               ∙ aTsm s₀

      tail : (j : type (Judgment 𝒥)) (y : ⌞ extendedContext s₁ ⟨ j ⟩ ⌟)
           → ((aTsm s₁) ⟨ j ⟩) (G1 j (inr y))
             ＝ GD j (inr (G0 j (inr y)))
      tail j (inl γ₁) = refl
      tail j (inr p₁) = refl

  map⋊-assoc-square E₀'@(collapse col₀@(mkCollapse jf₀ a₀)) E₁'@(collapse col₁@(mkCollapse jf₁ a₁)) μ =
    eq (record { component≈ = λ j → funExt
         (⁄-elim-proposition
           (λ w → (lhsMor ⟨ j ⟩) w ＝ (rhsMor ⟨ j ⟩) w)
           (λ _ → ＝-isLevel ⦃ extDT-isSet j ⦄)
           (λ { (inl (inl h₁)) → refl
              ; (inl (inr h₀)) → refl
              ; (inr γ) → tail j ((μ' ⟨ j ⟩) ([_] γ)) })) })
    where
      μ' = SequentMorphism.sequentMorphism μ
      s₀ = mkSequent Γ₀ E₀'
      s₁ = mkSequent Γ₁ E₁'

      extDT-isSet : (j : type (Judgment 𝒥))
                  → isSet ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ s₁)) ⟨ j ⟩ ⌟
      extDT-isSet j = level-proof (extendedContext (weakenSequent H₁ (weakenSequent H₀ s₁)) ⟨ j ⟩)

      G1 : (j : type (Judgment 𝒥))
         → ⌞ ((H₁ + H₀) + extendedContext s₁) ⟨ j ⟩ ⌟
         → ⌞ extendedContext (weakenSequent (H₁ + H₀) s₁) ⟨ j ⟩ ⌟
      G1 j = gatherExtended (H₁ + H₀) s₁ ⟨ j ⟩

      GD : (j : type (Judgment 𝒥))
         → ⌞ (H₁ + extendedContext (weakenSequent H₀ s₁)) ⟨ j ⟩ ⌟
         → ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ s₁)) ⟨ j ⟩ ⌟
      GD j = gatherExtended H₁ (weakenSequent H₀ s₁) ⟨ j ⟩

      G0 : (j : type (Judgment 𝒥))
         → ⌞ (H₀ + extendedContext s₁) ⟨ j ⟩ ⌟
         → ⌞ extendedContext (weakenSequent H₀ s₁) ⟨ j ⟩ ⌟
      G0 j = gatherExtended H₀ s₁ ⟨ j ⟩

      lhsMor = aTsm s₁
               ∙ SequentMorphism.sequentMorphism
                   (weakenedSequentMorphism {H₀ = H₁ + H₀} {H₁ = H₁ + H₀} identity μ)
      rhsMor = SequentMorphism.sequentMorphism
                 (weakenedSequentMorphism {H₀ = H₁} {H₁ = H₁} identity
                   (weakenedSequentMorphism {H₀ = H₀} {H₁ = H₀} identity μ))
               ∙ aTsm s₀

      tail : (j : type (Judgment 𝒥)) (y : ⌞ extendedContext s₁ ⟨ j ⟩ ⌟)
           → ((aTsm s₁) ⟨ j ⟩) (G1 j (inr y))
             ＝ GD j (inr (G0 j (inr y)))
      tail j =
        ⁄-elim-proposition
          (λ y → ((aTsm s₁) ⟨ j ⟩) (G1 j (inr y)) ＝ GD j (inr (G0 j (inr y))))
          (λ _ → ＝-isLevel ⦃ extDT-isSet j ⦄)
          chaseT
        where
          chaseT : (v₁ : ⌞ (Γ₁ ⟨ j ⟩) ⌟)
                 → ((aTsm s₁) ⟨ j ⟩) (G1 j (inr ([_] v₁)))
                   ＝ GD j (inr (G0 j (inr ([_] v₁))))
          chaseT v₁ = refl


-- =============== Reassociation against cross morphisms ===============

module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a : Level} {𝒥 : DependentSortVocabulary o a}
  {k₁ k₀ : Level} (H₁ : Context 𝒥 k₁) (H₀ : Context 𝒥 k₀) where

  private
    aTsmC : {l : Level} (s : Sequent 𝒥 l)
          → extendedContext (weakenSequent (H₁ + H₀) s)
            ⇒ extendedContext (weakenSequent H₁ (weakenSequent H₀ s))
    aTsmC s = SequentMorphism.sequentMorphism
                (toSequentMorphism (assocWeakenSequentEquivalence H₁ H₀ s))

    bridge : {l : Level} (t : Sequent 𝒥 l) (j : type (Judgment 𝒥))
             (v : ⌞ ((H₁ + H₀) + Sequent.context t) ⟨ j ⟩ ⌟)
           → (aTsmC t ⟨ j ⟩) ((→⋊ (weakenSequent (H₁ + H₀) t) ⟨ j ⟩) v)
             ＝ (→⋊ (weakenSequent H₁ (weakenSequent H₀ t)) ⟨ j ⟩)
                 ((ContextEquivalence.morphism
                    (assocSumContextEquivalence {Γ = H₁} {Δ = H₀} {Ψ = Sequent.context t}) ⟨ j ⟩) v)
    bridge t j v =
      map⋊-→⋊ (ContextEquivalence.morphism
                 (assocSumContextEquivalence {Γ = H₁} {Δ = H₀} {Ψ = Sequent.context t}))
              (mapExtensionOrCollapse (inrContext {Γ = H₁ + H₀} {Δ = Sequent.context t})
                 (Sequent.extensionOrCollapse t))
              (mapExtensionOrCollapse (inrContext {Γ = H₁} {Δ = H₀ + Sequent.context t})
                 (mapExtensionOrCollapse (inrContext {Γ = H₀} {Δ = Sequent.context t})
                    (Sequent.extensionOrCollapse t)))
              (assocEocEquality H₁ H₀ (Sequent.extensionOrCollapse t))
              j v

  map⋊-assoc-cross :
      {l l' : Level} (t : Sequent 𝒥 l) {Δ : Context 𝒥 l'}
      (F : ExtensionOrCollapse Δ)
      (ρ : extendedContext (mkSequent Δ F) ⇒ H₀)
    → aTsmC t
        ∙ (→⋊ (weakenSequent (H₁ + H₀) t)
          ∙ (inlContext {Γ = H₁ + H₀} {Δ = Sequent.context t}
          ∙ (sumContextMorphism (identityH H₁) ρ
          ∙ distributeExtended H₁ (mkSequent Δ F))))
      ＝ SequentMorphism.sequentMorphism
          (weakenSequentMorphism H₁
            (mkSequentMorphism {s₁ = mkSequent Δ F} {s₂ = weakenSequent H₀ t}
             (→⋊ (weakenSequent H₀ t)
              ∙ (inlContext {Γ = H₀} {Δ = Sequent.context t} ∙ ρ))))
  map⋊-assoc-cross t {Δ = Δ} F'@(extend (mkExtension jfF aF)) ρ =
    eq (record { component≈ = λ j → funExt
         (λ { (inl (inl h)) → bridge t j (inl (inl h))
                              ⨾  sym (gatherExtended-onAdded H₁ (weakenSequent H₀ t) j h)
            ; (inl (inr d)) → tailC j (inl d)
            ; (inr p) → tailC j (inr p) }) })
    where
      s' = mkSequent Δ F'

      tailC : (j : type (Judgment 𝒥)) (y : ⌞ extendedContext s' ⟨ j ⟩ ⌟)
            → (aTsmC t ⟨ j ⟩)
                ((→⋊ (weakenSequent (H₁ + H₀) t) ⟨ j ⟩) (inl (inr ((ρ ⟨ j ⟩) y))))
              ＝ (gatherExtended H₁ (weakenSequent H₀ t) ⟨ j ⟩)
                  (inr ((→⋊ (weakenSequent H₀ t) ⟨ j ⟩) (inl ((ρ ⟨ j ⟩) y))))
      tailC j y =
           bridge t j (inl (inr ((ρ ⟨ j ⟩) y)))
        ⨾  sym (gatherExtended-onCtx H₁ (weakenSequent H₀ t) j (inl ((ρ ⟨ j ⟩) y)))

  map⋊-assoc-cross t {Δ = Δ} F'@(collapse colF@(mkCollapse jfF aF)) ρ =
    eq (record { component≈ = λ j → funExt
         (⁄-elim-proposition
           (λ z → (lhsMor ⟨ j ⟩) z ＝ (rhsMor ⟨ j ⟩) z)
           (λ _ → ＝-isLevel ⦃ extDT-isSet j ⦄)
           (λ { (inl h) → bridge t j (inl (inl h))
                          ⨾  sym (gatherExtended-onAdded H₁ (weakenSequent H₀ t) j h)
              ; (inr d) → tailC j ([_] d) })) })
    where
      s' = mkSequent Δ F'

      lhsMor = aTsmC t
               ∙ (→⋊ (weakenSequent (H₁ + H₀) t)
               ∙ (inlContext {Γ = H₁ + H₀} {Δ = Sequent.context t}
               ∙ (sumContextMorphism (identityH H₁) ρ
               ∙ distributeExtended H₁ s')))
      rhsMor = SequentMorphism.sequentMorphism
                 (weakenSequentMorphism H₁
                   (mkSequentMorphism {s₁ = s'} {s₂ = weakenSequent H₀ t}
                     (→⋊ (weakenSequent H₀ t)
                     ∙ (inlContext {Γ = H₀} {Δ = Sequent.context t} ∙ ρ))))

      extDT-isSet : (j : type (Judgment 𝒥))
                  → isSet ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ t)) ⟨ j ⟩ ⌟
      extDT-isSet j = level-proof (extendedContext (weakenSequent H₁ (weakenSequent H₀ t)) ⟨ j ⟩)

      tailC : (j : type (Judgment 𝒥)) (y : ⌞ extendedContext s' ⟨ j ⟩ ⌟)
            → (aTsmC t ⟨ j ⟩)
                ((→⋊ (weakenSequent (H₁ + H₀) t) ⟨ j ⟩) (inl (inr ((ρ ⟨ j ⟩) y))))
              ＝ (gatherExtended H₁ (weakenSequent H₀ t) ⟨ j ⟩)
                  (inr ((→⋊ (weakenSequent H₀ t) ⟨ j ⟩) (inl ((ρ ⟨ j ⟩) y))))
      tailC j y =
           bridge t j (inl (inr ((ρ ⟨ j ⟩) y)))
        ⨾  sym (gatherExtended-onCtx H₁ (weakenSequent H₀ t) j (inl ((ρ ⟨ j ⟩) y)))

  map⋊-assoc-realise :
      {l l' : Level} {Δ : Context 𝒥 l} (F : ExtensionOrCollapse Δ)
      {K : Context 𝒥 l'} (ρ : extendedContext (mkSequent Δ F) ⇒ K)
    → ContextEquivalence.morphism
        (assocSumContextEquivalence {Γ = H₁} {Δ = H₀} {Ψ = K})
        ∙ (sumContextMorphism (identityH (H₁ + H₀)) ρ
        ∙ distributeExtended (H₁ + H₀) (mkSequent Δ F))
      ＝ (sumContextMorphism (identityH H₁)
           (sumContextMorphism (identityH H₀) ρ ∙ distributeExtended H₀ (mkSequent Δ F))
         ∙ distributeExtended H₁ (weakenSequent H₀ (mkSequent Δ F)))
        ∙ SequentMorphism.sequentMorphism
            (toSequentMorphism (assocWeakenSequentEquivalence H₁ H₀ (mkSequent Δ F)))
  map⋊-assoc-realise {Δ = Δ} F'@(extend (mkExtension jfF aF)) {K = K} ρ =
    eq (record { component≈ = λ j → funExt (λ { (inl (inl (inl h₁))) → refl
                                              ; (inl (inl (inr h₀))) → refl
                                              ; (inl (inr d)) → refl
                                              ; (inr p) → refl }) })
    where
      s' = mkSequent Δ F'

  map⋊-assoc-realise {Δ = Δ} F'@(collapse colF@(mkCollapse jfF aF)) {K = K} ρ =
    eq (record { component≈ = λ j → funExt
         (⁄-elim-proposition
           (λ z → (lhsMor ⟨ j ⟩) z ＝ (rhsMor ⟨ j ⟩) z)
           (λ _ → ＝-isLevel ⦃ tgtK-isSet j ⦄)
           (λ { (inl (inl h₁)) → refl
              ; (inl (inr h₀)) → refl
              ; (inr d) → refl })) })
    where
      s' = mkSequent Δ F'

      lhsMor = ContextEquivalence.morphism (assocSumContextEquivalence {Γ = H₁} {Δ = H₀} {Ψ = K})
               ∙ (sumContextMorphism (identityH (H₁ + H₀)) ρ
               ∙ distributeExtended (H₁ + H₀) s')
      rhsMor = (sumContextMorphism (identityH H₁)
                  (sumContextMorphism (identityH H₀) ρ ∙ distributeExtended H₀ s')
                ∙ distributeExtended H₁ (weakenSequent H₀ s'))
               ∙ SequentMorphism.sequentMorphism
                   (toSequentMorphism (assocWeakenSequentEquivalence H₁ H₀ s'))

      aMΔ = ContextEquivalence.morphism (assocSumContextEquivalence {Γ = H₁} {Δ = H₀} {Ψ = Δ})

      tgtK-isSet : (j : type (Judgment 𝒥)) → isSet ⌞ (H₁ + (H₀ + K)) ⟨ j ⟩ ⌟
      tgtK-isSet j = level-proof ((H₁ + (H₀ + K)) ⟨ j ⟩)












-- =============== Reassociation squares of sequent morphisms ===============

module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a : Level} {𝒥 : DependentSortVocabulary o a}
  {k₁ k₀ : Level} (H₁ : Context 𝒥 k₁) (H₀ : Context 𝒥 k₀) where

  assocWeakenSequentMorphism-square :
      {l₀ l₁ : Level} {s₀ : Sequent 𝒥 l₀} {s₁ : Sequent 𝒥 l₁} (μ : SequentMorphism s₀ s₁)
    → toSequentMorphism (assocWeakenSequentEquivalence H₁ H₀ s₁)
        ∙ weakenSequentMorphism (H₁ + H₀) μ
      ＝ weakenSequentMorphism H₁ (weakenSequentMorphism H₀ μ)
        ∙ toSequentMorphism (assocWeakenSequentEquivalence H₁ H₀ s₀)
  assocWeakenSequentMorphism-square {s₀ = s₀} {s₁ = s₁} μ =
    ap mkSequentMorphism
       (map⋊-assoc-square H₁ H₀
         (Sequent.extensionOrCollapse s₀) (Sequent.extensionOrCollapse s₁) μ)

  assocWeakenSequentMorphism-left :
      {l l' : Level} (t : Sequent 𝒥 l) {s : Sequent 𝒥 l'} (ρ : extendedContext s ⇒ H₁)
    → toSequentMorphism (assocWeakenSequentEquivalence H₁ H₀ t)
        ∙ mkSequentMorphism {s₁ = s} {s₂ = weakenSequent (H₁ + H₀) t}
            (→⋊ (weakenSequent (H₁ + H₀) t)
              ∙ (inlContext ∙ (inlContext {Γ = H₁} {Δ = H₀} ∙ ρ)))
      ＝ mkSequentMorphism {s₁ = s} {s₂ = weakenSequent H₁ (weakenSequent H₀ t)}
          (→⋊ (weakenSequent H₁ (weakenSequent H₀ t)) ∙ (inlContext ∙ ρ))
  assocWeakenSequentMorphism-left t ρ =
    ap mkSequentMorphism
       (eq (record { component≈ = λ j → funExt (λ z →
          map⋊-→⋊ (ContextEquivalence.morphism
                     (assocSumContextEquivalence {Γ = H₁} {Δ = H₀} {Ψ = Sequent.context t}))
                  (mapExtensionOrCollapse (inrContext {Γ = H₁ + H₀} {Δ = Sequent.context t})
                     (Sequent.extensionOrCollapse t))
                  (mapExtensionOrCollapse (inrContext {Γ = H₁} {Δ = H₀ + Sequent.context t})
                     (mapExtensionOrCollapse (inrContext {Γ = H₀} {Δ = Sequent.context t})
                        (Sequent.extensionOrCollapse t)))
                  (assocEocEquality H₁ H₀ (Sequent.extensionOrCollapse t))
                  j (inl (inl ((ρ ⟨ j ⟩) z)))) }))

  assocWeakenSequentMorphism-cross :
      {l l' : Level} (t : Sequent 𝒥 l) {Δ : Context 𝒥 l'}
      (F : ExtensionOrCollapse Δ) (ρ : extendedContext (mkSequent Δ F) ⇒ H₀)
    → toSequentMorphism (assocWeakenSequentEquivalence H₁ H₀ t)
        ∙ mkSequentMorphism
            {s₁ = weakenSequent H₁ (mkSequent Δ F)} {s₂ = weakenSequent (H₁ + H₀) t}
            (→⋊ (weakenSequent (H₁ + H₀) t)
              ∙ (inlContext
              ∙ (sumContextMorphism (identityH H₁) ρ
              ∙ distributeExtended H₁ (mkSequent Δ F))))
      ＝ weakenSequentMorphism H₁
          (mkSequentMorphism {s₁ = mkSequent Δ F} {s₂ = weakenSequent H₀ t}
            (→⋊ (weakenSequent H₀ t) ∙ (inlContext ∙ ρ)))
  assocWeakenSequentMorphism-cross t F ρ =
    ap mkSequentMorphism (map⋊-assoc-cross H₁ H₀ t F ρ)
