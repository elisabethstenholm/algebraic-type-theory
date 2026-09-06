module Weakening.Reassociation where

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
    (collapseEq w@(mkCollapseEquality refl q)) j v =
    ⁄-rec-β ⦃ QΓ₀.setQuotient j ⦄ ⦃ bset = tgt-isSet j ⦄
            (class₁ j ∘ (α ⟨ j ⟩)) _ v
    where
      module QΓ₀ (j' : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ Γ₀ ⟨ j' ⟩ ⌟) (CollapseRelation col₀ j')
      module QΓ₁ (j' : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ Γ₁ ⟨ j' ⟩ ⌟) (CollapseRelation col₁ j')

      tgt-isSet : (j' : type (Judgment 𝒥)) → isSet ⌞ (Γ₁ ⋊ₖ col₁) ⟨ j' ⟩ ⌟
      tgt-isSet j' = level-proof ((Γ₁ ⋊ₖ col₁) ⟨ j' ⟩)

      class₁ : (j' : type (Judgment 𝒥)) → ⌞ Γ₁ ⟨ j' ⟩ ⌟ → ⌞ (Γ₁ ⋊ₖ col₁) ⟨ j' ⟩ ⌟
      class₁ j' = [_] ⦃ QΓ₁.setQuotient j' ⦄


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
    eq (record { component≈ = λ j → funExt (pw j) })
    where
      μ' = SequentMorphism.sequentMorphism μ
      s₀ = mkSequent Γ₀ E₀'
      s₁ = mkSequent Γ₁ E₁'

      pw : (j : type (Judgment 𝒥))
           (w : ⌞ extendedContext (weakenSequent (H₁ + H₀) s₀) ⟨ j ⟩ ⌟)
         → ((aTsm s₁
             ∙ SequentMorphism.sequentMorphism
                 (weakenedSequentMorphism {H₀ = H₁ + H₀} {H₁ = H₁ + H₀} identity μ)) ⟨ j ⟩) w
           ＝ ((SequentMorphism.sequentMorphism
                 (weakenedSequentMorphism {H₀ = H₁} {H₁ = H₁} identity
                   (weakenedSequentMorphism {H₀ = H₀} {H₁ = H₀} identity μ))
               ∙ aTsm s₀) ⟨ j ⟩) w
      tail : (j : type (Judgment 𝒥)) (y : ⌞ extendedContext s₁ ⟨ j ⟩ ⌟)
           → ((aTsm s₁) ⟨ j ⟩) ((gatherExtended (H₁ + H₀) s₁ ⟨ j ⟩) (inr y))
             ＝ (gatherExtended H₁ (weakenSequent H₀ s₁) ⟨ j ⟩)
                 (inr ((gatherExtended H₀ s₁ ⟨ j ⟩) (inr y)))
      tail j (inl γ₁) = refl
      tail j (inr p₁) = refl

      pw j (inl (inl (inl h₁))) = refl
      pw j (inl (inl (inr h₀))) = refl
      pw j (inl (inr γ)) = tail j ((μ' ⟨ j ⟩) (inl γ))
      pw j (inr p) = tail j ((μ' ⟨ j ⟩) (inr p))
  map⋊-assoc-square E₀'@(extend (mkExtension jf₀ a₀)) E₁'@(collapse col₁@(mkCollapse jf₁ a₁)) μ =
    eq (record { component≈ = λ j → funExt (pw j) })
    where
      μ' = SequentMorphism.sequentMorphism μ
      s₀ = mkSequent Γ₀ E₀'
      s₁ = mkSequent Γ₁ E₁'

      module QΓ₁ (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ (Γ₁ ⟨ j ⟩) ⌟) (CollapseRelation col₁ j)
      module Q1T (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ (((H₁ + H₀) + Γ₁) ⟨ j ⟩) ⌟)
          (CollapseRelation (mapCollapse (inrContext {Γ = H₁ + H₀} {Δ = Γ₁}) col₁) j)
      module Q0T (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ ((H₀ + Γ₁) ⟨ j ⟩) ⌟)
          (CollapseRelation (mapCollapse (inrContext {Γ = H₀} {Δ = Γ₁}) col₁) j)
      module QDT (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ ((H₁ + (H₀ + Γ₁)) ⟨ j ⟩) ⌟)
          (CollapseRelation (mapCollapse (inrContext {Γ = H₁} {Δ = H₀ + Γ₁})
                              (mapCollapse (inrContext {Γ = H₀} {Δ = Γ₁}) col₁)) j)

      ext1T-isSet : (j : type (Judgment 𝒥))
                  → isSet ⌞ extendedContext (weakenSequent (H₁ + H₀) s₁) ⟨ j ⟩ ⌟
      ext1T-isSet j = level-proof (extendedContext (weakenSequent (H₁ + H₀) s₁) ⟨ j ⟩)

      ext0T-isSet : (j : type (Judgment 𝒥))
                  → isSet ⌞ extendedContext (weakenSequent H₀ s₁) ⟨ j ⟩ ⌟
      ext0T-isSet j = level-proof (extendedContext (weakenSequent H₀ s₁) ⟨ j ⟩)

      extDT-isSet : (j : type (Judgment 𝒥))
                  → isSet ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ s₁)) ⟨ j ⟩ ⌟
      extDT-isSet j = level-proof (extendedContext (weakenSequent H₁ (weakenSequent H₀ s₁)) ⟨ j ⟩)

      classDT : (j : type (Judgment 𝒥)) → ⌞ ((H₁ + (H₀ + Γ₁)) ⟨ j ⟩) ⌟
              → ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ s₁)) ⟨ j ⟩ ⌟
      classDT j = [_] ⦃ QDT.setQuotient j ⦄

      class1T : (j : type (Judgment 𝒥)) → ⌞ (((H₁ + H₀) + Γ₁) ⟨ j ⟩) ⌟
              → ⌞ extendedContext (weakenSequent (H₁ + H₀) s₁) ⟨ j ⟩ ⌟
      class1T j = [_] ⦃ Q1T.setQuotient j ⦄

      class0T : (j : type (Judgment 𝒥)) → ⌞ ((H₀ + Γ₁) ⟨ j ⟩) ⌟
              → ⌞ extendedContext (weakenSequent H₀ s₁) ⟨ j ⟩ ⌟
      class0T j = [_] ⦃ Q0T.setQuotient j ⦄

      tail : (j : type (Judgment 𝒥)) (y : ⌞ extendedContext s₁ ⟨ j ⟩ ⌟)
           → ((aTsm s₁) ⟨ j ⟩) ((gatherExtended (H₁ + H₀) s₁ ⟨ j ⟩) (inr y))
             ＝ (gatherExtended H₁ (weakenSequent H₀ s₁) ⟨ j ⟩)
                 (inr ((gatherExtended H₀ s₁ ⟨ j ⟩) (inr y)))
      tail j =
        ⁄-elim-proposition ⦃ QΓ₁.setQuotient j ⦄
          (λ y → ((aTsm s₁) ⟨ j ⟩) ((gatherExtended (H₁ + H₀) s₁ ⟨ j ⟩) (inr y))
                 ＝ (gatherExtended H₁ (weakenSequent H₀ s₁) ⟨ j ⟩)
                     (inr ((gatherExtended H₀ s₁ ⟨ j ⟩) (inr y))))
          (λ _ → ＝-isLevel ⦃ extDT-isSet j ⦄)
          chase
        where
          chase : (v₁ : ⌞ (Γ₁ ⟨ j ⟩) ⌟)
                → ((aTsm s₁) ⟨ j ⟩) ((gatherExtended (H₁ + H₀) s₁ ⟨ j ⟩)
                    (inr ([_] ⦃ QΓ₁.setQuotient j ⦄ v₁)))
                  ＝ (gatherExtended H₁ (weakenSequent H₀ s₁) ⟨ j ⟩)
                      (inr ((gatherExtended H₀ s₁ ⟨ j ⟩) (inr ([_] ⦃ QΓ₁.setQuotient j ⦄ v₁))))
          chase v₁ =
               ap ((aTsm s₁) ⟨ j ⟩)
                  (⁄-rec-β ⦃ QΓ₁.setQuotient j ⦄ ⦃ bset = ext1T-isSet j ⦄
                           (class1T j ∘ inr) _ v₁)
            ⨾  ⁄-rec-β ⦃ Q1T.setQuotient j ⦄ ⦃ bset = extDT-isSet j ⦄
                       (classDT j ∘ (ContextEquivalence.morphism
                          (assocSumContextEquivalence {Γ = H₁} {Δ = H₀} {Ψ = Γ₁}) ⟨ j ⟩)) _ (inr v₁)
            ⨾  sym (   ap (λ q → (gatherExtended H₁ (weakenSequent H₀ s₁) ⟨ j ⟩) (inr q))
                          (⁄-rec-β ⦃ QΓ₁.setQuotient j ⦄ ⦃ bset = ext0T-isSet j ⦄
                                   (class0T j ∘ inr) _ v₁)
                    ⨾  ⁄-rec-β ⦃ Q0T.setQuotient j ⦄ ⦃ bset = extDT-isSet j ⦄
                               (classDT j ∘ inr) _ (inr v₁))

      pw : (j : type (Judgment 𝒥))
           (w : ⌞ extendedContext (weakenSequent (H₁ + H₀) s₀) ⟨ j ⟩ ⌟)
         → ((aTsm s₁
             ∙ SequentMorphism.sequentMorphism
                 (weakenedSequentMorphism {H₀ = H₁ + H₀} {H₁ = H₁ + H₀} identity μ)) ⟨ j ⟩) w
           ＝ ((SequentMorphism.sequentMorphism
                 (weakenedSequentMorphism {H₀ = H₁} {H₁ = H₁} identity
                   (weakenedSequentMorphism {H₀ = H₀} {H₁ = H₀} identity μ))
               ∙ aTsm s₀) ⟨ j ⟩) w
      pw j (inl (inl (inl h₁))) =
        ⁄-rec-β ⦃ Q1T.setQuotient j ⦄ ⦃ bset = extDT-isSet j ⦄
                (classDT j ∘ (ContextEquivalence.morphism
                   (assocSumContextEquivalence {Γ = H₁} {Δ = H₀} {Ψ = Γ₁}) ⟨ j ⟩)) _ (inl (inl h₁))
      pw j (inl (inl (inr h₀))) =
           ⁄-rec-β ⦃ Q1T.setQuotient j ⦄ ⦃ bset = extDT-isSet j ⦄
                   (classDT j ∘ (ContextEquivalence.morphism
                      (assocSumContextEquivalence {Γ = H₁} {Δ = H₀} {Ψ = Γ₁}) ⟨ j ⟩)) _ (inl (inr h₀))
        ⨾  sym (⁄-rec-β ⦃ Q0T.setQuotient j ⦄ ⦃ bset = extDT-isSet j ⦄
                        (classDT j ∘ inr) _ (inl h₀))
      pw j (inl (inr γ)) = tail j ((μ' ⟨ j ⟩) (inl γ))
      pw j (inr p) = tail j ((μ' ⟨ j ⟩) (inr p))
  map⋊-assoc-square E₀'@(collapse col₀@(mkCollapse jf₀ a₀)) E₁'@(extend (mkExtension jf₁ a₁)) μ =
    eq (record { component≈ = λ j → funExt (pw j) })
    where
      μ' = SequentMorphism.sequentMorphism μ
      s₀ = mkSequent Γ₀ E₀'
      s₁ = mkSequent Γ₁ E₁'

      aMor₀ = ContextEquivalence.morphism (assocSumContextEquivalence {Γ = H₁} {Δ = H₀} {Ψ = Γ₀})

      module QΓ₀ (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ (Γ₀ ⟨ j ⟩) ⌟) (CollapseRelation col₀ j)
      module Q1S (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ (((H₁ + H₀) + Γ₀) ⟨ j ⟩) ⌟)
          (CollapseRelation (mapCollapse (inrContext {Γ = H₁ + H₀} {Δ = Γ₀}) col₀) j)
      module Q0S (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ ((H₀ + Γ₀) ⟨ j ⟩) ⌟)
          (CollapseRelation (mapCollapse (inrContext {Γ = H₀} {Δ = Γ₀}) col₀) j)
      module QDS (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ ((H₁ + (H₀ + Γ₀)) ⟨ j ⟩) ⌟)
          (CollapseRelation (mapCollapse (inrContext {Γ = H₁} {Δ = H₀ + Γ₀})
                              (mapCollapse (inrContext {Γ = H₀} {Δ = Γ₀}) col₀)) j)

      extDS-isSet : (j : type (Judgment 𝒥))
                  → isSet ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ s₀)) ⟨ j ⟩ ⌟
      extDS-isSet j = level-proof (extendedContext (weakenSequent H₁ (weakenSequent H₀ s₀)) ⟨ j ⟩)

      extDT-isSet : (j : type (Judgment 𝒥))
                  → isSet ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ s₁)) ⟨ j ⟩ ⌟
      extDT-isSet j = level-proof (extendedContext (weakenSequent H₁ (weakenSequent H₀ s₁)) ⟨ j ⟩)

      mid1-isSet : (j : type (Judgment 𝒥))
                 → isSet ⌞ ((H₁ + H₀) + extendedContext s₀) ⟨ j ⟩ ⌟
      mid1-isSet j = level-proof (((H₁ + H₀) + extendedContext s₀) ⟨ j ⟩)

      mid2-isSet : (j : type (Judgment 𝒥))
                 → isSet ⌞ (H₁ + extendedContext (weakenSequent H₀ s₀)) ⟨ j ⟩ ⌟
      mid2-isSet j = level-proof ((H₁ + extendedContext (weakenSequent H₀ s₀)) ⟨ j ⟩)

      mid3-isSet : (j : type (Judgment 𝒥))
                 → isSet ⌞ (H₀ + extendedContext s₀) ⟨ j ⟩ ⌟
      mid3-isSet j = level-proof ((H₀ + extendedContext s₀) ⟨ j ⟩)

      classDS : (j : type (Judgment 𝒥)) → ⌞ ((H₁ + (H₀ + Γ₀)) ⟨ j ⟩) ⌟
              → ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ s₀)) ⟨ j ⟩ ⌟
      classDS j = [_] ⦃ QDS.setQuotient j ⦄

      SS : (j : type (Judgment 𝒥))
         → ⌞ ((H₁ + H₀) + extendedContext s₀) ⟨ j ⟩ ⌟
         → ⌞ ((H₁ + H₀) + extendedContext s₁) ⟨ j ⟩ ⌟
      SS j = sumContextMorphism (identityH (H₁ + H₀)) μ' ⟨ j ⟩

      G1 : (j : type (Judgment 𝒥))
         → ⌞ ((H₁ + H₀) + extendedContext s₁) ⟨ j ⟩ ⌟
         → ⌞ extendedContext (weakenSequent (H₁ + H₀) s₁) ⟨ j ⟩ ⌟
      G1 j = gatherExtended (H₁ + H₀) s₁ ⟨ j ⟩

      S0 : (j : type (Judgment 𝒥))
         → ⌞ (H₀ + extendedContext s₀) ⟨ j ⟩ ⌟
         → ⌞ (H₀ + extendedContext s₁) ⟨ j ⟩ ⌟
      S0 j = sumContextMorphism (identityH H₀) μ' ⟨ j ⟩

      SD : (j : type (Judgment 𝒥))
         → ⌞ (H₁ + extendedContext (weakenSequent H₀ s₀)) ⟨ j ⟩ ⌟
         → ⌞ (H₁ + extendedContext (weakenSequent H₀ s₁)) ⟨ j ⟩ ⌟
      SD j = sumContextMorphism (identityH H₁)
               (SequentMorphism.sequentMorphism (weakenedSequentMorphism {H₀ = H₀} {H₁ = H₀} identity μ)) ⟨ j ⟩

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

      chase : (j : type (Judgment 𝒥)) (u : ⌞ (((H₁ + H₀) + Γ₀) ⟨ j ⟩) ⌟)
            → (lhsMor ⟨ j ⟩) ([_] ⦃ Q1S.setQuotient j ⦄ u)
              ＝ (rhsMor ⟨ j ⟩) ([_] ⦃ Q1S.setQuotient j ⦄ u)
      chase j (inl (inl h₁)) =
           ap (λ v → ((aTsm s₁) ⟨ j ⟩) (G1 j (SS j v)))
              (⁄-rec-β ⦃ Q1S.setQuotient j ⦄ ⦃ bset = mid1-isSet j ⦄ _ _ (inl (inl h₁)))
        ⨾  sym (   ap (λ v → GD j (SD j v))
                      (⁄-rec-β ⦃ QDS.setQuotient j ⦄ ⦃ bset = mid2-isSet j ⦄ _ _ (inl h₁))
                ⨾  refl)
        ⨾  sym (ap (λ v → GD j (SD j ((distributeExtended H₁ (weakenSequent H₀ s₀) ⟨ j ⟩) v)))
                   (⁄-rec-β ⦃ Q1S.setQuotient j ⦄ ⦃ bset = extDS-isSet j ⦄
                            (classDS j ∘ (aMor₀ ⟨ j ⟩)) _ (inl (inl h₁))))
      chase j (inl (inr h₀)) =
           ap (λ v → ((aTsm s₁) ⟨ j ⟩) (G1 j (SS j v)))
              (⁄-rec-β ⦃ Q1S.setQuotient j ⦄ ⦃ bset = mid1-isSet j ⦄ _ _ (inl (inr h₀)))
        ⨾  sym (   ap (λ v → GD j (SD j v))
                      (⁄-rec-β ⦃ QDS.setQuotient j ⦄ ⦃ bset = mid2-isSet j ⦄ _ _ (inr (inl h₀)))
                ⨾  ap (λ v → GD j (inr (G0 j (S0 j v))))
                      (⁄-rec-β ⦃ Q0S.setQuotient j ⦄ ⦃ bset = mid3-isSet j ⦄ _ _ (inl h₀)))
        ⨾  sym (ap (λ v → GD j (SD j ((distributeExtended H₁ (weakenSequent H₀ s₀) ⟨ j ⟩) v)))
                   (⁄-rec-β ⦃ Q1S.setQuotient j ⦄ ⦃ bset = extDS-isSet j ⦄
                            (classDS j ∘ (aMor₀ ⟨ j ⟩)) _ (inl (inr h₀))))
      chase j (inr γ) =
           ap (λ v → ((aTsm s₁) ⟨ j ⟩) (G1 j (SS j v)))
              (⁄-rec-β ⦃ Q1S.setQuotient j ⦄ ⦃ bset = mid1-isSet j ⦄ _ _ (inr γ))
        ⨾  tail j ((μ' ⟨ j ⟩) ([_] ⦃ QΓ₀.setQuotient j ⦄ γ))
        ⨾  sym (   ap (λ v → GD j (SD j v))
                      (⁄-rec-β ⦃ QDS.setQuotient j ⦄ ⦃ bset = mid2-isSet j ⦄ _ _ (inr (inr γ)))
                ⨾  ap (λ v → GD j (inr (G0 j (S0 j v))))
                      (⁄-rec-β ⦃ Q0S.setQuotient j ⦄ ⦃ bset = mid3-isSet j ⦄ _ _ (inr γ)))
        ⨾  sym (ap (λ v → GD j (SD j ((distributeExtended H₁ (weakenSequent H₀ s₀) ⟨ j ⟩) v)))
                   (⁄-rec-β ⦃ Q1S.setQuotient j ⦄ ⦃ bset = extDS-isSet j ⦄
                            (classDS j ∘ (aMor₀ ⟨ j ⟩)) _ (inr γ)))

      pw : (j : type (Judgment 𝒥))
           (w : ⌞ extendedContext (weakenSequent (H₁ + H₀) s₀) ⟨ j ⟩ ⌟)
         → (lhsMor ⟨ j ⟩) w ＝ (rhsMor ⟨ j ⟩) w
      pw j =
        ⁄-elim-proposition ⦃ Q1S.setQuotient j ⦄
          (λ w → (lhsMor ⟨ j ⟩) w ＝ (rhsMor ⟨ j ⟩) w)
          (λ _ → ＝-isLevel ⦃ extDT-isSet j ⦄)
          (chase j)
  map⋊-assoc-square E₀'@(collapse col₀@(mkCollapse jf₀ a₀)) E₁'@(collapse col₁@(mkCollapse jf₁ a₁)) μ =
    eq (record { component≈ = λ j → funExt (pw j) })
    where
      μ' = SequentMorphism.sequentMorphism μ
      s₀ = mkSequent Γ₀ E₀'
      s₁ = mkSequent Γ₁ E₁'

      aMor₀ = ContextEquivalence.morphism (assocSumContextEquivalence {Γ = H₁} {Δ = H₀} {Ψ = Γ₀})
      aMor₁ = ContextEquivalence.morphism (assocSumContextEquivalence {Γ = H₁} {Δ = H₀} {Ψ = Γ₁})

      module QΓ₀ (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ (Γ₀ ⟨ j ⟩) ⌟) (CollapseRelation col₀ j)
      module Q1S (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ (((H₁ + H₀) + Γ₀) ⟨ j ⟩) ⌟)
          (CollapseRelation (mapCollapse (inrContext {Γ = H₁ + H₀} {Δ = Γ₀}) col₀) j)
      module Q0S (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ ((H₀ + Γ₀) ⟨ j ⟩) ⌟)
          (CollapseRelation (mapCollapse (inrContext {Γ = H₀} {Δ = Γ₀}) col₀) j)
      module QDS (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ ((H₁ + (H₀ + Γ₀)) ⟨ j ⟩) ⌟)
          (CollapseRelation (mapCollapse (inrContext {Γ = H₁} {Δ = H₀ + Γ₀})
                              (mapCollapse (inrContext {Γ = H₀} {Δ = Γ₀}) col₀)) j)
      module QΓ₁ (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ (Γ₁ ⟨ j ⟩) ⌟) (CollapseRelation col₁ j)
      module Q1T (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ (((H₁ + H₀) + Γ₁) ⟨ j ⟩) ⌟)
          (CollapseRelation (mapCollapse (inrContext {Γ = H₁ + H₀} {Δ = Γ₁}) col₁) j)
      module Q0T (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ ((H₀ + Γ₁) ⟨ j ⟩) ⌟)
          (CollapseRelation (mapCollapse (inrContext {Γ = H₀} {Δ = Γ₁}) col₁) j)
      module QDT (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ ((H₁ + (H₀ + Γ₁)) ⟨ j ⟩) ⌟)
          (CollapseRelation (mapCollapse (inrContext {Γ = H₁} {Δ = H₀ + Γ₁})
                              (mapCollapse (inrContext {Γ = H₀} {Δ = Γ₁}) col₁)) j)

      extDS-isSet : (j : type (Judgment 𝒥))
                  → isSet ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ s₀)) ⟨ j ⟩ ⌟
      extDS-isSet j = level-proof (extendedContext (weakenSequent H₁ (weakenSequent H₀ s₀)) ⟨ j ⟩)

      ext1T-isSet : (j : type (Judgment 𝒥))
                  → isSet ⌞ extendedContext (weakenSequent (H₁ + H₀) s₁) ⟨ j ⟩ ⌟
      ext1T-isSet j = level-proof (extendedContext (weakenSequent (H₁ + H₀) s₁) ⟨ j ⟩)

      ext0T-isSet : (j : type (Judgment 𝒥))
                  → isSet ⌞ extendedContext (weakenSequent H₀ s₁) ⟨ j ⟩ ⌟
      ext0T-isSet j = level-proof (extendedContext (weakenSequent H₀ s₁) ⟨ j ⟩)

      extDT-isSet : (j : type (Judgment 𝒥))
                  → isSet ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ s₁)) ⟨ j ⟩ ⌟
      extDT-isSet j = level-proof (extendedContext (weakenSequent H₁ (weakenSequent H₀ s₁)) ⟨ j ⟩)

      mid1-isSet : (j : type (Judgment 𝒥))
                 → isSet ⌞ ((H₁ + H₀) + extendedContext s₀) ⟨ j ⟩ ⌟
      mid1-isSet j = level-proof (((H₁ + H₀) + extendedContext s₀) ⟨ j ⟩)

      mid2-isSet : (j : type (Judgment 𝒥))
                 → isSet ⌞ (H₁ + extendedContext (weakenSequent H₀ s₀)) ⟨ j ⟩ ⌟
      mid2-isSet j = level-proof ((H₁ + extendedContext (weakenSequent H₀ s₀)) ⟨ j ⟩)

      mid3-isSet : (j : type (Judgment 𝒥))
                 → isSet ⌞ (H₀ + extendedContext s₀) ⟨ j ⟩ ⌟
      mid3-isSet j = level-proof ((H₀ + extendedContext s₀) ⟨ j ⟩)

      classDS : (j : type (Judgment 𝒥)) → ⌞ ((H₁ + (H₀ + Γ₀)) ⟨ j ⟩) ⌟
              → ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ s₀)) ⟨ j ⟩ ⌟
      classDS j = [_] ⦃ QDS.setQuotient j ⦄

      classDT : (j : type (Judgment 𝒥)) → ⌞ ((H₁ + (H₀ + Γ₁)) ⟨ j ⟩) ⌟
              → ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ s₁)) ⟨ j ⟩ ⌟
      classDT j = [_] ⦃ QDT.setQuotient j ⦄

      class1T : (j : type (Judgment 𝒥)) → ⌞ (((H₁ + H₀) + Γ₁) ⟨ j ⟩) ⌟
              → ⌞ extendedContext (weakenSequent (H₁ + H₀) s₁) ⟨ j ⟩ ⌟
      class1T j = [_] ⦃ Q1T.setQuotient j ⦄

      class0T : (j : type (Judgment 𝒥)) → ⌞ ((H₀ + Γ₁) ⟨ j ⟩) ⌟
              → ⌞ extendedContext (weakenSequent H₀ s₁) ⟨ j ⟩ ⌟
      class0T j = [_] ⦃ Q0T.setQuotient j ⦄

      SS : (j : type (Judgment 𝒥))
         → ⌞ ((H₁ + H₀) + extendedContext s₀) ⟨ j ⟩ ⌟
         → ⌞ ((H₁ + H₀) + extendedContext s₁) ⟨ j ⟩ ⌟
      SS j = sumContextMorphism (identityH (H₁ + H₀)) μ' ⟨ j ⟩

      S0 : (j : type (Judgment 𝒥))
         → ⌞ (H₀ + extendedContext s₀) ⟨ j ⟩ ⌟
         → ⌞ (H₀ + extendedContext s₁) ⟨ j ⟩ ⌟
      S0 j = sumContextMorphism (identityH H₀) μ' ⟨ j ⟩

      G1 : (j : type (Judgment 𝒥))
         → ⌞ ((H₁ + H₀) + extendedContext s₁) ⟨ j ⟩ ⌟
         → ⌞ extendedContext (weakenSequent (H₁ + H₀) s₁) ⟨ j ⟩ ⌟
      G1 j = gatherExtended (H₁ + H₀) s₁ ⟨ j ⟩

      SD : (j : type (Judgment 𝒥))
         → ⌞ (H₁ + extendedContext (weakenSequent H₀ s₀)) ⟨ j ⟩ ⌟
         → ⌞ (H₁ + extendedContext (weakenSequent H₀ s₁)) ⟨ j ⟩ ⌟
      SD j = sumContextMorphism (identityH H₁)
               (SequentMorphism.sequentMorphism (weakenedSequentMorphism {H₀ = H₀} {H₁ = H₀} identity μ)) ⟨ j ⟩

      GD : (j : type (Judgment 𝒥))
         → ⌞ (H₁ + extendedContext (weakenSequent H₀ s₁)) ⟨ j ⟩ ⌟
         → ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ s₁)) ⟨ j ⟩ ⌟
      GD j = gatherExtended H₁ (weakenSequent H₀ s₁) ⟨ j ⟩

      G0 : (j : type (Judgment 𝒥))
         → ⌞ (H₀ + extendedContext s₁) ⟨ j ⟩ ⌟
         → ⌞ extendedContext (weakenSequent H₀ s₁) ⟨ j ⟩ ⌟
      G0 j = gatherExtended H₀ s₁ ⟨ j ⟩

      DBL : (j : type (Judgment 𝒥))
          → ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ s₀)) ⟨ j ⟩ ⌟
          → ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ s₁)) ⟨ j ⟩ ⌟
      DBL j = SequentMorphism.sequentMorphism
                (weakenedSequentMorphism {H₀ = H₁} {H₁ = H₁} identity
                  (weakenedSequentMorphism {H₀ = H₀} {H₁ = H₀} identity μ)) ⟨ j ⟩

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
        ⁄-elim-proposition ⦃ QΓ₁.setQuotient j ⦄
          (λ y → ((aTsm s₁) ⟨ j ⟩) (G1 j (inr y)) ＝ GD j (inr (G0 j (inr y))))
          (λ _ → ＝-isLevel ⦃ extDT-isSet j ⦄)
          chaseT
        where
          chaseT : (v₁ : ⌞ (Γ₁ ⟨ j ⟩) ⌟)
                 → ((aTsm s₁) ⟨ j ⟩) (G1 j (inr ([_] ⦃ QΓ₁.setQuotient j ⦄ v₁)))
                   ＝ GD j (inr (G0 j (inr ([_] ⦃ QΓ₁.setQuotient j ⦄ v₁))))
          chaseT v₁ =
               ap ((aTsm s₁) ⟨ j ⟩)
                  (⁄-rec-β ⦃ QΓ₁.setQuotient j ⦄ ⦃ bset = ext1T-isSet j ⦄
                           (class1T j ∘ inr) _ v₁)
            ⨾  ⁄-rec-β ⦃ Q1T.setQuotient j ⦄ ⦃ bset = extDT-isSet j ⦄
                       (classDT j ∘ (aMor₁ ⟨ j ⟩)) _ (inr v₁)
            ⨾  sym (   ap (λ q → GD j (inr q))
                          (⁄-rec-β ⦃ QΓ₁.setQuotient j ⦄ ⦃ bset = ext0T-isSet j ⦄
                                   (class0T j ∘ inr) _ v₁)
                    ⨾  ⁄-rec-β ⦃ Q0T.setQuotient j ⦄ ⦃ bset = extDT-isSet j ⦄
                               (classDT j ∘ inr) _ (inr v₁))

      chase : (j : type (Judgment 𝒥)) (u : ⌞ (((H₁ + H₀) + Γ₀) ⟨ j ⟩) ⌟)
            → (lhsMor ⟨ j ⟩) ([_] ⦃ Q1S.setQuotient j ⦄ u)
              ＝ (rhsMor ⟨ j ⟩) ([_] ⦃ Q1S.setQuotient j ⦄ u)
      chase j (inl (inl h₁)) =
           ap (λ v → ((aTsm s₁) ⟨ j ⟩) (G1 j (SS j v)))
              (⁄-rec-β ⦃ Q1S.setQuotient j ⦄ ⦃ bset = mid1-isSet j ⦄ _ _ (inl (inl h₁)))
        ⨾  ⁄-rec-β ⦃ Q1T.setQuotient j ⦄ ⦃ bset = extDT-isSet j ⦄
                   (classDT j ∘ (aMor₁ ⟨ j ⟩)) _ (inl (inl h₁))
        ⨾  sym (   ap (DBL j)
                      (⁄-rec-β ⦃ Q1S.setQuotient j ⦄ ⦃ bset = extDS-isSet j ⦄
                               (classDS j ∘ (aMor₀ ⟨ j ⟩)) _ (inl (inl h₁)))
                ⨾  ap (λ v → GD j (SD j v))
                      (⁄-rec-β ⦃ QDS.setQuotient j ⦄ ⦃ bset = mid2-isSet j ⦄ _ _ (inl h₁)))
      chase j (inl (inr h₀)) =
           ap (λ v → ((aTsm s₁) ⟨ j ⟩) (G1 j (SS j v)))
              (⁄-rec-β ⦃ Q1S.setQuotient j ⦄ ⦃ bset = mid1-isSet j ⦄ _ _ (inl (inr h₀)))
        ⨾  ⁄-rec-β ⦃ Q1T.setQuotient j ⦄ ⦃ bset = extDT-isSet j ⦄
                   (classDT j ∘ (aMor₁ ⟨ j ⟩)) _ (inl (inr h₀))
        ⨾  sym (   ap (DBL j)
                      (⁄-rec-β ⦃ Q1S.setQuotient j ⦄ ⦃ bset = extDS-isSet j ⦄
                               (classDS j ∘ (aMor₀ ⟨ j ⟩)) _ (inl (inr h₀)))
                ⨾  ap (λ v → GD j (SD j v))
                      (⁄-rec-β ⦃ QDS.setQuotient j ⦄ ⦃ bset = mid2-isSet j ⦄ _ _ (inr (inl h₀)))
                ⨾  ap (λ v → GD j (inr (G0 j (S0 j v))))
                      (⁄-rec-β ⦃ Q0S.setQuotient j ⦄ ⦃ bset = mid3-isSet j ⦄ _ _ (inl h₀))
                ⨾  ⁄-rec-β ⦃ Q0T.setQuotient j ⦄ ⦃ bset = extDT-isSet j ⦄
                           (classDT j ∘ inr) _ (inl h₀))
      chase j (inr γ) =
           ap (λ v → ((aTsm s₁) ⟨ j ⟩) (G1 j (SS j v)))
              (⁄-rec-β ⦃ Q1S.setQuotient j ⦄ ⦃ bset = mid1-isSet j ⦄ _ _ (inr γ))
        ⨾  tail j ((μ' ⟨ j ⟩) ([_] ⦃ QΓ₀.setQuotient j ⦄ γ))
        ⨾  sym (   ap (DBL j)
                      (⁄-rec-β ⦃ Q1S.setQuotient j ⦄ ⦃ bset = extDS-isSet j ⦄
                               (classDS j ∘ (aMor₀ ⟨ j ⟩)) _ (inr γ))
                ⨾  ap (λ v → GD j (SD j v))
                      (⁄-rec-β ⦃ QDS.setQuotient j ⦄ ⦃ bset = mid2-isSet j ⦄ _ _ (inr (inr γ)))
                ⨾  ap (λ v → GD j (inr (G0 j (S0 j v))))
                      (⁄-rec-β ⦃ Q0S.setQuotient j ⦄ ⦃ bset = mid3-isSet j ⦄ _ _ (inr γ)))

      pw : (j : type (Judgment 𝒥))
           (w : ⌞ extendedContext (weakenSequent (H₁ + H₀) s₀) ⟨ j ⟩ ⌟)
         → (lhsMor ⟨ j ⟩) w ＝ (rhsMor ⟨ j ⟩) w
      pw j =
        ⁄-elim-proposition ⦃ Q1S.setQuotient j ⦄
          (λ w → (lhsMor ⟨ j ⟩) w ＝ (rhsMor ⟨ j ⟩) w)
          (λ _ → ＝-isLevel ⦃ extDT-isSet j ⦄)
          (chase j)



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
    eq (record { component≈ = λ j → funExt (pw j) })
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

      pw : (j : type (Judgment 𝒥))
           (z : ⌞ extendedContext (weakenSequent H₁ s') ⟨ j ⟩ ⌟)
         → ((aTsmC t
             ∙ (→⋊ (weakenSequent (H₁ + H₀) t)
               ∙ (inlContext {Γ = H₁ + H₀} {Δ = Sequent.context t}
               ∙ (sumContextMorphism (identityH H₁) ρ
               ∙ distributeExtended H₁ s')))) ⟨ j ⟩) z
           ＝ ((SequentMorphism.sequentMorphism
                 (weakenSequentMorphism H₁
                   (mkSequentMorphism {s₁ = s'} {s₂ = weakenSequent H₀ t}
                     (→⋊ (weakenSequent H₀ t)
                     ∙ (inlContext {Γ = H₀} {Δ = Sequent.context t} ∙ ρ))))) ⟨ j ⟩) z
      pw j (inl (inl h)) =
           bridge t j (inl (inl h))
        ⨾  sym (gatherExtended-onAdded H₁ (weakenSequent H₀ t) j h)
      pw j (inl (inr d)) = tailC j (inl d)
      pw j (inr p) = tailC j (inr p)
  map⋊-assoc-cross t {Δ = Δ} F'@(collapse colF@(mkCollapse jfF aF)) ρ =
    eq (record { component≈ = λ j → funExt (pw j) })
    where
      s' = mkSequent Δ F'

      module QΔ (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ Δ ⟨ j ⟩ ⌟) (CollapseRelation colF j)
      module QM (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ (H₁ + Δ) ⟨ j ⟩ ⌟)
          (CollapseRelation (mapCollapse (inrContext {Γ = H₁} {Δ = Δ}) colF) j)

      extDT-isSet : (j : type (Judgment 𝒥))
                  → isSet ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ t)) ⟨ j ⟩ ⌟
      extDT-isSet j = level-proof (extendedContext (weakenSequent H₁ (weakenSequent H₀ t)) ⟨ j ⟩)

      midF-isSet : (j : type (Judgment 𝒥))
                 → isSet ⌞ (H₁ + extendedContext s') ⟨ j ⟩ ⌟
      midF-isSet j = level-proof ((H₁ + extendedContext s') ⟨ j ⟩)

      tailC : (j : type (Judgment 𝒥)) (y : ⌞ extendedContext s' ⟨ j ⟩ ⌟)
            → (aTsmC t ⟨ j ⟩)
                ((→⋊ (weakenSequent (H₁ + H₀) t) ⟨ j ⟩) (inl (inr ((ρ ⟨ j ⟩) y))))
              ＝ (gatherExtended H₁ (weakenSequent H₀ t) ⟨ j ⟩)
                  (inr ((→⋊ (weakenSequent H₀ t) ⟨ j ⟩) (inl ((ρ ⟨ j ⟩) y))))
      tailC j y =
           bridge t j (inl (inr ((ρ ⟨ j ⟩) y)))
        ⨾  sym (gatherExtended-onCtx H₁ (weakenSequent H₀ t) j (inl ((ρ ⟨ j ⟩) y)))

      lhsF : (j : type (Judgment 𝒥))
           → ⌞ (H₁ + extendedContext s') ⟨ j ⟩ ⌟
           → ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ t)) ⟨ j ⟩ ⌟
      lhsF j v =
        (aTsmC t ⟨ j ⟩)
          ((→⋊ (weakenSequent (H₁ + H₀) t) ⟨ j ⟩)
            (inl ((sumContextMorphism (identityH H₁) ρ ⟨ j ⟩) v)))

      rhsF : (j : type (Judgment 𝒥))
           → ⌞ (H₁ + extendedContext s') ⟨ j ⟩ ⌟
           → ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ t)) ⟨ j ⟩ ⌟
      rhsF j v =
        (gatherExtended H₁ (weakenSequent H₀ t) ⟨ j ⟩)
          ((sumContextMorphism (identityH H₁)
             (→⋊ (weakenSequent H₀ t)
               ∙ (inlContext {Γ = H₀} {Δ = Sequent.context t} ∙ ρ)) ⟨ j ⟩) v)

      chase : (j : type (Judgment 𝒥)) (u : ⌞ (H₁ + Δ) ⟨ j ⟩ ⌟)
            → ((aTsmC t
                ∙ (→⋊ (weakenSequent (H₁ + H₀) t)
                  ∙ (inlContext {Γ = H₁ + H₀} {Δ = Sequent.context t}
                  ∙ (sumContextMorphism (identityH H₁) ρ
                  ∙ distributeExtended H₁ s')))) ⟨ j ⟩) ([_] ⦃ QM.setQuotient j ⦄ u)
              ＝ ((SequentMorphism.sequentMorphism
                    (weakenSequentMorphism H₁
                      (mkSequentMorphism {s₁ = s'} {s₂ = weakenSequent H₀ t}
                      (→⋊ (weakenSequent H₀ t)
                        ∙ (inlContext {Γ = H₀} {Δ = Sequent.context t} ∙ ρ))))) ⟨ j ⟩)
                  ([_] ⦃ QM.setQuotient j ⦄ u)
      chase j (inl h) =
           ap (lhsF j) (⁄-rec-β ⦃ QM.setQuotient j ⦄ ⦃ bset = midF-isSet j ⦄ _ _ (inl h))
        ⨾  bridge t j (inl (inl h))
        ⨾  sym (gatherExtended-onAdded H₁ (weakenSequent H₀ t) j h)
        ⨾  sym (ap (rhsF j) (⁄-rec-β ⦃ QM.setQuotient j ⦄ ⦃ bset = midF-isSet j ⦄ _ _ (inl h)))
      chase j (inr d) =
           ap (lhsF j) (⁄-rec-β ⦃ QM.setQuotient j ⦄ ⦃ bset = midF-isSet j ⦄ _ _ (inr d))
        ⨾  tailC j ([_] ⦃ QΔ.setQuotient j ⦄ d)
        ⨾  sym (ap (rhsF j) (⁄-rec-β ⦃ QM.setQuotient j ⦄ ⦃ bset = midF-isSet j ⦄ _ _ (inr d)))

      pw : (j : type (Judgment 𝒥))
           (z : ⌞ extendedContext (weakenSequent H₁ s') ⟨ j ⟩ ⌟)
         → ((aTsmC t
             ∙ (→⋊ (weakenSequent (H₁ + H₀) t)
               ∙ (inlContext {Γ = H₁ + H₀} {Δ = Sequent.context t}
               ∙ (sumContextMorphism (identityH H₁) ρ
               ∙ distributeExtended H₁ s')))) ⟨ j ⟩) z
           ＝ ((SequentMorphism.sequentMorphism
                 (weakenSequentMorphism H₁
                   (mkSequentMorphism {s₁ = s'} {s₂ = weakenSequent H₀ t}
                     (→⋊ (weakenSequent H₀ t)
                     ∙ (inlContext {Γ = H₀} {Δ = Sequent.context t} ∙ ρ))))) ⟨ j ⟩) z
      pw j =
        ⁄-elim-proposition ⦃ QM.setQuotient j ⦄
          (λ z → ((aTsmC t
                   ∙ (→⋊ (weakenSequent (H₁ + H₀) t)
                     ∙ (inlContext {Γ = H₁ + H₀} {Δ = Sequent.context t}
                     ∙ (sumContextMorphism (identityH H₁) ρ
                     ∙ distributeExtended H₁ s')))) ⟨ j ⟩) z
                 ＝ ((SequentMorphism.sequentMorphism
                       (weakenSequentMorphism H₁
                         (mkSequentMorphism {s₁ = s'} {s₂ = weakenSequent H₀ t}
                           (→⋊ (weakenSequent H₀ t)
                           ∙ (inlContext {Γ = H₀} {Δ = Sequent.context t} ∙ ρ))))) ⟨ j ⟩) z)
          (λ _ → ＝-isLevel ⦃ extDT-isSet j ⦄)
          (chase j)

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
    eq (record { component≈ = λ j → funExt (pw j) })
    where
      s' = mkSequent Δ F'

      pw : (j : type (Judgment 𝒥))
           (z : ⌞ extendedContext (weakenSequent (H₁ + H₀) s') ⟨ j ⟩ ⌟)
         → ((ContextEquivalence.morphism (assocSumContextEquivalence {Γ = H₁} {Δ = H₀} {Ψ = K})
             ∙ (sumContextMorphism (identityH (H₁ + H₀)) ρ
             ∙ distributeExtended (H₁ + H₀) s')) ⟨ j ⟩) z
           ＝ (((sumContextMorphism (identityH H₁)
                  (sumContextMorphism (identityH H₀) ρ ∙ distributeExtended H₀ s')
                ∙ distributeExtended H₁ (weakenSequent H₀ s'))
               ∙ SequentMorphism.sequentMorphism
                   (toSequentMorphism (assocWeakenSequentEquivalence H₁ H₀ s'))) ⟨ j ⟩) z
      pw j (inl (inl (inl h₁))) = refl
      pw j (inl (inl (inr h₀))) = refl
      pw j (inl (inr d)) = refl
      pw j (inr p) = refl
  map⋊-assoc-realise {Δ = Δ} F'@(collapse colF@(mkCollapse jfF aF)) {K = K} ρ =
    eq (record { component≈ = λ j → funExt (pw j) })
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

      aMK : (j : type (Judgment 𝒥))
          → ⌞ ((H₁ + H₀) + K) ⟨ j ⟩ ⌟ → ⌞ (H₁ + (H₀ + K)) ⟨ j ⟩ ⌟
      aMK j = ContextEquivalence.morphism (assocSumContextEquivalence {Γ = H₁} {Δ = H₀} {Ψ = K}) ⟨ j ⟩

      module QΔ (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ Δ ⟨ j ⟩ ⌟) (CollapseRelation colF j)
      module QW (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ ((H₁ + H₀) + Δ) ⟨ j ⟩ ⌟)
          (CollapseRelation (mapCollapse (inrContext {Γ = H₁ + H₀} {Δ = Δ}) colF) j)
      module QI (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ (H₀ + Δ) ⟨ j ⟩ ⌟)
          (CollapseRelation (mapCollapse (inrContext {Γ = H₀} {Δ = Δ}) colF) j)
      module QD (j : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ (H₁ + (H₀ + Δ)) ⟨ j ⟩ ⌟)
          (CollapseRelation (mapCollapse (inrContext {Γ = H₁} {Δ = H₀ + Δ})
                              (mapCollapse (inrContext {Γ = H₀} {Δ = Δ}) colF)) j)

      tgtK-isSet : (j : type (Judgment 𝒥)) → isSet ⌞ (H₁ + (H₀ + K)) ⟨ j ⟩ ⌟
      tgtK-isSet j = level-proof ((H₁ + (H₀ + K)) ⟨ j ⟩)

      mid1-isSet : (j : type (Judgment 𝒥))
                 → isSet ⌞ ((H₁ + H₀) + extendedContext s') ⟨ j ⟩ ⌟
      mid1-isSet j = level-proof (((H₁ + H₀) + extendedContext s') ⟨ j ⟩)

      mid2-isSet : (j : type (Judgment 𝒥))
                 → isSet ⌞ (H₁ + extendedContext (weakenSequent H₀ s')) ⟨ j ⟩ ⌟
      mid2-isSet j = level-proof ((H₁ + extendedContext (weakenSequent H₀ s')) ⟨ j ⟩)

      mid3-isSet : (j : type (Judgment 𝒥))
                 → isSet ⌞ (H₀ + extendedContext s') ⟨ j ⟩ ⌟
      mid3-isSet j = level-proof ((H₀ + extendedContext s') ⟨ j ⟩)

      extD-isSet : (j : type (Judgment 𝒥))
                 → isSet ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ s')) ⟨ j ⟩ ⌟
      extD-isSet j = level-proof (extendedContext (weakenSequent H₁ (weakenSequent H₀ s')) ⟨ j ⟩)

      classD : (j : type (Judgment 𝒥)) → ⌞ (H₁ + (H₀ + Δ)) ⟨ j ⟩ ⌟
             → ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ s')) ⟨ j ⟩ ⌟
      classD j = [_] ⦃ QD.setQuotient j ⦄

      SR : (j : type (Judgment 𝒥))
         → ⌞ ((H₁ + H₀) + extendedContext s') ⟨ j ⟩ ⌟ → ⌞ ((H₁ + H₀) + K) ⟨ j ⟩ ⌟
      SR j = sumContextMorphism (identityH (H₁ + H₀)) ρ ⟨ j ⟩

      SD : (j : type (Judgment 𝒥))
         → ⌞ (H₁ + extendedContext (weakenSequent H₀ s')) ⟨ j ⟩ ⌟
         → ⌞ (H₁ + (H₀ + K)) ⟨ j ⟩ ⌟
      SD j = sumContextMorphism (identityH H₁)
               (sumContextMorphism (identityH H₀) ρ ∙ distributeExtended H₀ s') ⟨ j ⟩

      D2 : (j : type (Judgment 𝒥))
         → ⌞ extendedContext (weakenSequent H₁ (weakenSequent H₀ s')) ⟨ j ⟩ ⌟
         → ⌞ (H₁ + extendedContext (weakenSequent H₀ s')) ⟨ j ⟩ ⌟
      D2 j = distributeExtended H₁ (weakenSequent H₀ s') ⟨ j ⟩

      chase : (j : type (Judgment 𝒥)) (u : ⌞ ((H₁ + H₀) + Δ) ⟨ j ⟩ ⌟)
            → (lhsMor ⟨ j ⟩) ([_] ⦃ QW.setQuotient j ⦄ u)
              ＝ (rhsMor ⟨ j ⟩) ([_] ⦃ QW.setQuotient j ⦄ u)
      chase j (inl (inl h₁)) =
           ap (λ v → aMK j (SR j v))
              (⁄-rec-β ⦃ QW.setQuotient j ⦄ ⦃ bset = mid1-isSet j ⦄ _ _ (inl (inl h₁)))
        ⨾  sym (   ap (λ v → SD j (D2 j v))
                      (⁄-rec-β ⦃ QW.setQuotient j ⦄ ⦃ bset = extD-isSet j ⦄
                               (classD j ∘ (aMΔ ⟨ j ⟩)) _ (inl (inl h₁)))
                ⨾  ap (SD j)
                      (⁄-rec-β ⦃ QD.setQuotient j ⦄ ⦃ bset = mid2-isSet j ⦄ _ _ (inl h₁)))
      chase j (inl (inr h₀)) =
           ap (λ v → aMK j (SR j v))
              (⁄-rec-β ⦃ QW.setQuotient j ⦄ ⦃ bset = mid1-isSet j ⦄ _ _ (inl (inr h₀)))
        ⨾  sym (   ap (λ v → SD j (D2 j v))
                      (⁄-rec-β ⦃ QW.setQuotient j ⦄ ⦃ bset = extD-isSet j ⦄
                               (classD j ∘ (aMΔ ⟨ j ⟩)) _ (inl (inr h₀)))
                ⨾  ap (SD j)
                      (⁄-rec-β ⦃ QD.setQuotient j ⦄ ⦃ bset = mid2-isSet j ⦄ _ _ (inr (inl h₀)))
                ⨾  ap (λ v → inr ((sumContextMorphism (identityH H₀) ρ ⟨ j ⟩) v))
                      (⁄-rec-β ⦃ QI.setQuotient j ⦄ ⦃ bset = mid3-isSet j ⦄ _ _ (inl h₀)))
      chase j (inr d) =
           ap (λ v → aMK j (SR j v))
              (⁄-rec-β ⦃ QW.setQuotient j ⦄ ⦃ bset = mid1-isSet j ⦄ _ _ (inr d))
        ⨾  sym (   ap (λ v → SD j (D2 j v))
                      (⁄-rec-β ⦃ QW.setQuotient j ⦄ ⦃ bset = extD-isSet j ⦄
                               (classD j ∘ (aMΔ ⟨ j ⟩)) _ (inr d))
                ⨾  ap (SD j)
                      (⁄-rec-β ⦃ QD.setQuotient j ⦄ ⦃ bset = mid2-isSet j ⦄ _ _ (inr (inr d)))
                ⨾  ap (λ v → inr ((sumContextMorphism (identityH H₀) ρ ⟨ j ⟩) v))
                      (⁄-rec-β ⦃ QI.setQuotient j ⦄ ⦃ bset = mid3-isSet j ⦄ _ _ (inr d)))

      pw : (j : type (Judgment 𝒥))
           (z : ⌞ extendedContext (weakenSequent (H₁ + H₀) s') ⟨ j ⟩ ⌟)
         → (lhsMor ⟨ j ⟩) z ＝ (rhsMor ⟨ j ⟩) z
      pw j =
        ⁄-elim-proposition ⦃ QW.setQuotient j ⦄
          (λ z → (lhsMor ⟨ j ⟩) z ＝ (rhsMor ⟨ j ⟩) z)
          (λ _ → ＝-isLevel ⦃ tgtK-isSet j ⦄)
          (chase j)
