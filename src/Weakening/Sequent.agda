module Weakening.Sequent where

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


-- =============== Weakening a sequent with a context ===============

module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄ {o a : Level} {𝒥 : DependentSortVocabulary o a} where

  weakenSequent : {k l : Level} → Context 𝒥 k → Sequent 𝒥 l → Sequent 𝒥 (k ⊔ l)
  weakenSequent c s =
    record
      { context = c + Sequent.context s
      ; extensionOrCollapse = mapExtensionOrCollapse inrContext (Sequent.extensionOrCollapse s) }


  weakenWithEmptyContextEquivalence : {k l : Level} (Γ : Context 𝒥 l)
                  → ContextEquivalence (emptyContext 𝒥 k + Γ) Γ
  weakenWithEmptyContextEquivalence {k} Γ =
    record
      { morphism = record
          { component = component
          ; natural = funExt ∘ natural~ }
      ; component-isEquivalence = λ j →
          record
            { section = record { sectionBack = inr ; isSection = λ x → refl }
            ; retraction = record { retractionBack = inr ; isRetraction = isRetraction~ j } } }
    where
      component : (j : type (Judgment 𝒥)) → ⌞ (emptyContext 𝒥 k + Γ) ⟨ j ⟩ ⌟ → ⌞ Γ ⟨ j ⟩ ⌟
      component j (inr x) = x

      natural~ : {j₀ j₁ : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀ j₁))
               → Γ ⟨ f ⟩ ∘ component j₀ ~ component j₁ ∘ (emptyContext 𝒥 k + Γ) ⟨ f ⟩
      natural~ f (inr x) = refl

      isRetraction~ : (j : type (Judgment 𝒥)) → inr ∘ component j ~ id
      isRetraction~ j (inr x) = refl


  module _ {k : Level} (H : Context 𝒥 k) where

    identityH : H ⇒ H
    identityH = identity

    distributeExtended : {l : Level} (s : Sequent 𝒥 l)
                       → extendedContext (weakenSequent H s) ⇒ H + extendedContext s
    distributeExtended (mkSequent Γ (extend ext)) =
      record
        { component = λ j → λ { (inl (inl h)) → inl h
                              ; (inl (inr x)) → inr (inl x)
                              ; (inr p)       → inr (inr p) }
        ; natural = λ f → funExt λ { (inl (inl h)) → refl
                                   ; (inl (inr x)) → refl
                                   ; (inr refl)    → refl } }
    distributeExtended {l} (mkSequent Γ (collapse col)) =
      record
        { component = component
        ; natural = λ f → funExt (natural~ f) }
      where
        addedCollapse : Collapse (H + Γ)
        addedCollapse = mapCollapse inrContext col

        target : Context 𝒥 (k ⊔ (o ⊔ l))
        target = H + (Γ ⋊ₖ col)

        target-isSet : (j : type (Judgment 𝒥)) → isSet ⌞ target ⟨ j ⟩ ⌟
        target-isSet j = level-proof (target ⟨ j ⟩)

        onEntries : (j : type (Judgment 𝒥)) → ⌞ (H + Γ) ⟨ j ⟩ ⌟ → ⌞ target ⟨ j ⟩ ⌟
        onEntries j (inl h) = inl h
        onEntries j (inr x) = inr [ x ]
          where open FromAllSetQuotients ( ⌞ Γ ⟨ j ⟩ ⌟) (CollapseRelation col j)

        respectsCollapse : (j : type (Judgment 𝒥)) {x y : ⌞ (H + Γ) ⟨ j ⟩ ⌟}
                         → CollapseRelation addedCollapse j x y
                         → onEntries j x ＝ onEntries j y
        respectsCollapse j collapseRelation = ap inr (respects collapseRelation)
          where open FromAllSetQuotients ( ⌞ Γ ⟨ j ⟩ ⌟) (CollapseRelation col j)

        component : (j : type (Judgment 𝒥)) → ⌞ ((H + Γ) ⋊ₖ addedCollapse) ⟨ j ⟩ ⌟ → ⌞ target ⟨ j ⟩ ⌟
        component j = ⁄-rec ⦃ bset = target-isSet j ⦄ (onEntries j) (respectsCollapse j)
          where open FromAllSetQuotients (⌞ (H + Γ) ⟨ j ⟩ ⌟) (CollapseRelation addedCollapse j)

        natural~ : {j₀ j₁ : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀ j₁))
                 → target ⟨ f ⟩ ∘ component j₀ ~ component j₁ ∘ ((H + Γ) ⋊ₖ addedCollapse) ⟨ f ⟩
        natural~ {j₀} {j₁} f =
          ⁄-elim-proposition _ (λ q → ＝-isLevel ⦃ target-isSet j₁ ⦄) pointwise
          where
            open FromAllSetQuotients (⌞ (H + Γ) ⟨ j₀ ⟩ ⌟) (CollapseRelation addedCollapse j₀)
            open FromAllSetQuotients (⌞ (H + Γ) ⟨ j₁ ⟩ ⌟) (CollapseRelation addedCollapse j₁)
            open FromAllSetQuotients ( ⌞ Γ ⟨ j₀ ⟩ ⌟) (CollapseRelation col j₀)
            open FromAllSetQuotients ( ⌞ Γ ⟨ j₁ ⟩ ⌟) (CollapseRelation col j₁)

            step : (x : ⌞ (H + Γ) ⟨ j₀ ⟩ ⌟) → (target ⟨ f ⟩) (onEntries j₀ x) ＝ onEntries j₁ (((H + Γ) ⟨ f ⟩) x)
            step (inl h) = refl
            step (inr x) = ap inr (⁄-rec-β ([_] ∘ (Γ ⟨ f ⟩)) _ x)

            pointwise : (x : ⌞ (H + Γ) ⟨ j₀ ⟩ ⌟)
                      → (target ⟨ f ⟩) (component j₀ [ x ]) ＝ component j₁ ((((H + Γ) ⋊ₖ addedCollapse) ⟨ f ⟩) [ x ])
            pointwise x =
                 ap (target ⟨ f ⟩) (⁄-rec-β ⦃ bset = target-isSet j₀ ⦄ (onEntries j₀) (respectsCollapse j₀) x)
              ⨾  step x
              ⨾  sym (⁄-rec-β ⦃ bset = target-isSet j₁ ⦄ (onEntries j₁) (respectsCollapse j₁) (((H + Γ) ⟨ f ⟩) x))
              ⨾  ap (component j₁) (sym (⁄-rec-β ([_] ∘ ((H + Γ) ⟨ f ⟩)) _ x))

    gatherExtended : {l : Level} (s : Sequent 𝒥 l)
                   → H + extendedContext s ⇒ extendedContext (weakenSequent H s)
    gatherExtended (mkSequent Γ (extend ext)) =
      record
        { component = λ j → λ { (inl h)       → inl (inl h)
                              ; (inr (inl x)) → inl (inr x)
                              ; (inr (inr p)) → inr p }
        ; natural = λ f → funExt λ { (inl h)          → refl
                                   ; (inr (inl x))    → refl
                                   ; (inr (inr refl)) → refl } }
    gatherExtended {l} (mkSequent Γ (collapse col)) =
      record
        { component = component
        ; natural = λ f → funExt (natural~ f) }
      where
        addedCollapse : Collapse (H + Γ)
        addedCollapse = mapCollapse inrContext col

        source : Context 𝒥 (k ⊔ (o ⊔ l))
        source = H + (Γ ⋊ₖ col)

        target : Context 𝒥 (o ⊔ (k ⊔ l))
        target = (H + Γ) ⋊ₖ addedCollapse

        instance
          entriesH-isSet : {j : type (Judgment 𝒥)} → isSet ⌞ H ⟨ j ⟩ ⌟
          entriesH-isSet {j} = level-proof (H ⟨ j ⟩)

        classOf : (j : type (Judgment 𝒥)) → ⌞ (H + Γ) ⟨ j ⟩ ⌟ → ⌞ target ⟨ j ⟩ ⌟
        classOf j = [_]
          where open FromAllSetQuotients (⌞ (H + Γ) ⟨ j ⟩ ⌟) (CollapseRelation addedCollapse j)

        respectsCollapse : (j : type (Judgment 𝒥)) {x y : ⌞ Γ ⟨ j ⟩ ⌟}
                         → CollapseRelation col j x y
                         → classOf j (inr x) ＝ classOf j (inr y)
        respectsCollapse j collapseRelation = respects collapseRelation
          where open FromAllSetQuotients (⌞ (H + Γ) ⟨ j ⟩ ⌟) (CollapseRelation addedCollapse j)

        component : (j : type (Judgment 𝒥)) → ⌞ source ⟨ j ⟩ ⌟ → ⌞ target ⟨ j ⟩ ⌟
        component j (inl h) = classOf j (inl h)
        component j (inr q) = ⁄-rec (classOf j ∘ inr) (respectsCollapse j) q
          where
            open FromAllSetQuotients (⌞ Γ ⟨ j ⟩ ⌟) (CollapseRelation col j)
            open FromAllSetQuotients (⌞ (H + Γ) ⟨ j ⟩ ⌟) (CollapseRelation addedCollapse j)

        natural~ : {j₀ j₁ : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀ j₁))
                 → target ⟨ f ⟩ ∘ component j₀ ~ component j₁ ∘ source ⟨ f ⟩
        natural~ {j₀} {j₁} f (inl h) = ⁄-rec-β ([_] ∘ ((H + Γ) ⟨ f ⟩)) _ (inl h)
          where
            open FromAllSetQuotients (⌞ (H + Γ) ⟨ j₀ ⟩ ⌟) (CollapseRelation addedCollapse j₀)
            open FromAllSetQuotients (⌞ (H + Γ) ⟨ j₁ ⟩ ⌟) (CollapseRelation addedCollapse j₁)
        natural~ {j₀} {j₁} f (inr q) = ⁄-elim-proposition _ (λ _ → fromInstance) pointwise q
          where
            open FromAllSetQuotients (⌞ Γ ⟨ j₀ ⟩ ⌟) (CollapseRelation col j₀)
            open FromAllSetQuotients (⌞ Γ ⟨ j₁ ⟩ ⌟) (CollapseRelation col j₁)
            open FromAllSetQuotients (⌞ (H + Γ) ⟨ j₀ ⟩ ⌟) (CollapseRelation addedCollapse j₀)
            open FromAllSetQuotients (⌞ (H + Γ) ⟨ j₁ ⟩ ⌟) (CollapseRelation addedCollapse j₁)

            pointwise : (x : ⌞ Γ ⟨ j₀ ⟩ ⌟)
                      → (target ⟨ f ⟩) (component j₀ (inr [ x ])) ＝ component j₁ ((source ⟨ f ⟩) (inr [ x ]))
            pointwise x =
                 ap (target ⟨ f ⟩) (⁄-rec-β (classOf j₀ ∘ inr) (respectsCollapse j₀) x)
              ⨾  ⁄-rec-β ([_] ∘ ((H + Γ) ⟨ f ⟩)) _ (inr x)
              ⨾  sym (⁄-rec-β (classOf j₁ ∘ inr) (respectsCollapse j₁) ((Γ ⟨ f ⟩) x))
              ⨾  ap (λ q → component j₁ (inr q)) (sym (⁄-rec-β ([_] ∘ (Γ ⟨ f ⟩)) _ x))

    distribute-gather : {l : Level} (s : Sequent 𝒥 l) (j : type (Judgment 𝒥)) (w : ⌞ (H + extendedContext s) ⟨ j ⟩ ⌟)
                      → (distributeExtended s ⟨ j ⟩) ((gatherExtended s ⟨ j ⟩) w) ＝ w
    distribute-gather (mkSequent Γ (extend ext)) j (inl h) = refl
    distribute-gather (mkSequent Γ (extend ext)) j (inr (inl x)) = refl
    distribute-gather (mkSequent Γ (extend ext)) j (inr (inr p)) = refl
    distribute-gather {l} (mkSequent Γ (collapse col)) j (inl h) =
      ⁄-rec-β ⦃ bset = level-proof (target ⟨ j ⟩) ⦄ _ _ (inl h)
      where
        target : Context 𝒥 (k ⊔ (o ⊔ l))
        target = H + (Γ ⋊ₖ col)

        entriesΓ : (j : type (Judgment 𝒥)) → Type l
        entriesΓ j = ⌞ Γ ⟨ j ⟩ ⌟

        entriesHΓ : (j : type (Judgment 𝒥)) → Type (k ⊔ l)
        entriesHΓ j = ⌞ (H + Γ) ⟨ j ⟩ ⌟

        addedCollapse : Collapse (H + Γ)
        addedCollapse = mapCollapse inrContext col

        open FromAllSetQuotients (entriesΓ j) (CollapseRelation col j)
        open FromAllSetQuotients (entriesHΓ j) (CollapseRelation addedCollapse j)

        instance
          entriesH-isSet : isSet ⌞ H ⟨ j ⟩ ⌟
          entriesH-isSet = level-proof (H ⟨ j ⟩)
    distribute-gather {l} (mkSequent Γ (collapse col)) j (inr q) =
      ⁄-elim-proposition
        (λ q' → (distributeExtended (mkSequent Γ (collapse col)) ⟨ j ⟩)
                  ((gatherExtended (mkSequent Γ (collapse col)) ⟨ j ⟩) (inr q'))
                ＝ inr q')
        (λ _ → ＝-isLevel ⦃ level-proof (target ⟨ j ⟩) ⦄)
        pointwise q
      where
        target : Context 𝒥 (k ⊔ (o ⊔ l))
        target = H + (Γ ⋊ₖ col)

        entriesΓ : (j : type (Judgment 𝒥)) → Type l
        entriesΓ j = ⌞ Γ ⟨ j ⟩ ⌟

        entriesHΓ : (j : type (Judgment 𝒥)) → Type (k ⊔ l)
        entriesHΓ j = ⌞ (H + Γ) ⟨ j ⟩ ⌟

        addedCollapse : Collapse (H + Γ)
        addedCollapse = mapCollapse inrContext col

        open FromAllSetQuotients (entriesΓ j) (CollapseRelation col j)
        open FromAllSetQuotients (entriesHΓ j) (CollapseRelation addedCollapse j)

        instance
          entriesH-isSet : isSet ⌞ H ⟨ j ⟩ ⌟
          entriesH-isSet = level-proof (H ⟨ j ⟩)

        pointwise : (x : ⌞ Γ ⟨ j ⟩ ⌟)
                  → (distributeExtended (mkSequent Γ (collapse col)) ⟨ j ⟩)
                      ((gatherExtended (mkSequent Γ (collapse col)) ⟨ j ⟩) (inr [ x ]))
                  ＝ inr [ x ]
        pointwise x =
             ap (distributeExtended (mkSequent Γ (collapse col)) ⟨ j ⟩) (⁄-rec-β _ _ x)
          ⨾  ⁄-rec-β ⦃ bset = level-proof (target ⟨ j ⟩) ⦄ _ _ (inr x)

    gather-distribute : {l : Level} (s : Sequent 𝒥 l) (j : type (Judgment 𝒥)) (w : ⌞ extendedContext (weakenSequent H s) ⟨ j ⟩ ⌟)
                      → (gatherExtended s ⟨ j ⟩) ((distributeExtended s ⟨ j ⟩) w) ＝ w
    gather-distribute (mkSequent Γ (extend ext)) j (inl (inl h)) = refl
    gather-distribute (mkSequent Γ (extend ext)) j (inl (inr x)) = refl
    gather-distribute (mkSequent Γ (extend ext)) j (inr p) = refl
    gather-distribute {l} (mkSequent Γ (collapse col)) j w =
      ⁄-elim-proposition
        (λ w' → (gatherExtended (mkSequent Γ (collapse col)) ⟨ j ⟩)
                  ((distributeExtended (mkSequent Γ (collapse col)) ⟨ j ⟩) w')
                ＝ w')
        (λ _ → ＝-isLevel ⦃ level-proof (source ⟨ j ⟩) ⦄)
        pointwise
        w
      where
        addedCollapse : Collapse (H + Γ)
        addedCollapse = mapCollapse inrContext col

        source : Context 𝒥 (o ⊔ (k ⊔ l))
        source = (H + Γ) ⋊ₖ addedCollapse

        target : Context 𝒥 (k ⊔ (o ⊔ l))
        target = H + (Γ ⋊ₖ col)

        open FromAllSetQuotients (⌞ Γ ⟨ j ⟩ ⌟) (CollapseRelation col j)
        open FromAllSetQuotients (⌞ (H + Γ) ⟨ j ⟩ ⌟) (CollapseRelation addedCollapse j)

        instance
          entriesH-isSet : isSet ⌞ H ⟨ j ⟩ ⌟
          entriesH-isSet = level-proof (H ⟨ j ⟩)

        pointwise : (x : ⌞ (H + Γ) ⟨ j ⟩ ⌟)
                  → (gatherExtended (mkSequent Γ (collapse col)) ⟨ j ⟩)
                      ((distributeExtended (mkSequent Γ (collapse col)) ⟨ j ⟩) [ x ])
                    ＝ [ x ]
        pointwise (inl h) =
          ap (gatherExtended (mkSequent Γ (collapse col)) ⟨ j ⟩)
             (⁄-rec-β ⦃ bset = level-proof (target ⟨ j ⟩) ⦄ _ _ (inl h))
        pointwise (inr x) =
          begin
            (gatherExtended (mkSequent Γ (collapse col)) ⟨ j ⟩)
              ((distributeExtended (mkSequent Γ (collapse col)) ⟨ j ⟩) [ inr x ])  ⟪ ap (gatherExtended (mkSequent Γ (collapse col)) ⟨ j ⟩)
                                                                                        (⁄-rec-β ⦃ bset = level-proof (target ⟨ j ⟩) ⦄ _ _ (inr x)) ⟫
            (gatherExtended (mkSequent Γ (collapse col)) ⟨ j ⟩) (inr [ x ])        ⟪ ⁄-rec-β _ _ x ⟫
            [ inr x ]                                                             ∎

    distributeExtendedEquivalence : {l : Level} (s : Sequent 𝒥 l)
                                  → ContextEquivalence (extendedContext (weakenSequent H s))
                                                       (H + extendedContext s)
    distributeExtendedEquivalence s =
      record
        { morphism = distributeExtended s
        ; component-isEquivalence = λ j →
            record
              { section = record
                  { sectionBack = gatherExtended s ⟨ j ⟩
                  ; isSection = distribute-gather s j }
              ; retraction = record
                  { retractionBack = gatherExtended s ⟨ j ⟩
                  ; isRetraction = gather-distribute s j } } }

    weakenSequentMorphism : {l₀ l₁ : Level} {s₀ : Sequent 𝒥 l₀} {s₁ : Sequent 𝒥 l₁}
                                → SequentMorphism s₀ s₁
                                → SequentMorphism (weakenSequent H s₀) (weakenSequent H s₁)
    weakenSequentMorphism {s₀ = s₀} {s₁ = s₁} α =
      mkSequentMorphism
        (gatherExtended s₁ ∙ (sumContextMorphism identityH (SequentMorphism.sequentMorphism α) ∙ distributeExtended s₀))

    distributeExtended-onAdded : {l : Level} (s : Sequent 𝒥 l) (j : type (Judgment 𝒥)) (u : ⌞ H ⟨ j ⟩ ⌟)
                               → (distributeExtended s ⟨ j ⟩) ((→⋊ (weakenSequent H s) ⟨ j ⟩) (inl u))
                               ＝ inl u
    distributeExtended-onAdded (mkSequent Γ (extend ext)) j u = refl
    distributeExtended-onAdded {l} (mkSequent Γ (collapse col)) j u =
      ⁄-rec-β ⦃ bset = level-proof (target ⟨ j ⟩) ⦄ _ _ (inl u)
      where
        target : Context 𝒥 (k ⊔ (o ⊔ l))
        target = H + (Γ ⋊ₖ col)

        entriesΓ : (j : type (Judgment 𝒥)) → Type l
        entriesΓ j = ⌞ Γ ⟨ j ⟩ ⌟

        entriesHΓ : (j : type (Judgment 𝒥)) → Type (k ⊔ l)
        entriesHΓ j = ⌞ (H + Γ) ⟨ j ⟩ ⌟

        addedCollapse : Collapse (H + Γ)
        addedCollapse = mapCollapse inrContext col

        open FromAllSetQuotients (entriesΓ j) (CollapseRelation col j)
        open FromAllSetQuotients (entriesHΓ j) (CollapseRelation addedCollapse j)

        instance
          entriesH-isSet : isSet ⌞ H ⟨ j ⟩ ⌟
          entriesH-isSet = level-proof (H ⟨ j ⟩)

    gatherExtended-onAdded : {l : Level} (s : Sequent 𝒥 l) (j : type (Judgment 𝒥)) (u : ⌞ H ⟨ j ⟩ ⌟)
                           → (gatherExtended s ⟨ j ⟩) (inl u)
                           ＝ (→⋊ (weakenSequent H s) ⟨ j ⟩) (inl u)
    gatherExtended-onAdded (mkSequent Γ (extend ext)) j u = refl
    gatherExtended-onAdded (mkSequent Γ (collapse col)) j u = refl

    weakenSequentMorphism-onAdded :
        {l₀ l₁ : Level} {s₀ : Sequent 𝒥 l₀} {s₁ : Sequent 𝒥 l₁}
        (α : SequentMorphism s₀ s₁) (j : type (Judgment 𝒥)) (u : ⌞ H ⟨ j ⟩ ⌟)
      → (weakenSequentMorphism α ⟨ j ⟩) ((→⋊ (weakenSequent H s₀) ⟨ j ⟩) (inl u))
        ＝ (→⋊ (weakenSequent H s₁) ⟨ j ⟩) (inl u)
    weakenSequentMorphism-onAdded {s₀ = s₀} {s₁ = s₁} α j u =
         ap (λ w → (gatherExtended s₁ ⟨ j ⟩) ((sumContextMorphism identityH (SequentMorphism.sequentMorphism α) ⟨ j ⟩) w))
            (distributeExtended-onAdded s₀ j u)
      ⨾  gatherExtended-onAdded s₁ j u

    weakenSequentMorphism-composition :
        {l₀ l₁ l₂ : Level} {s₀ : Sequent 𝒥 l₀} {s₁ : Sequent 𝒥 l₁} {s₂ : Sequent 𝒥 l₂}
        (α : SequentMorphism s₀ s₁) (β : SequentMorphism s₁ s₂)
      → weakenSequentMorphism (α ⨾ β)
        ＝ weakenSequentMorphism α ⨾ weakenSequentMorphism β
    weakenSequentMorphism-composition {s₀ = s₀} {s₁ = s₁} {s₂ = s₂} α β =
      ap mkSequentMorphism (eq (record { component≈ = λ j → funExt (pointwise j) }))
      where
        α' = SequentMorphism.sequentMorphism α
        β' = SequentMorphism.sequentMorphism β

        onSum : (j : type (Judgment 𝒥)) (u : ⌞ (H + extendedContext s₀) ⟨ j ⟩ ⌟)
              → (sumContextMorphism identityH (β' ∙ α') ⟨ j ⟩) u
              ＝ (sumContextMorphism identityH β' ⟨ j ⟩) ((sumContextMorphism identityH α' ⟨ j ⟩) u)
        onSum j (inl h) = refl
        onSum j (inr v) = refl

        pointwise : (j : type (Judgment 𝒥)) (w : ⌞ extendedContext (weakenSequent H s₀) ⟨ j ⟩ ⌟)
                  → (weakenSequentMorphism (α ⨾ β) ⟨ j ⟩) w
                  ＝ ((weakenSequentMorphism α ⨾ weakenSequentMorphism β) ⟨ j ⟩) w
        pointwise j w =
             ap (gatherExtended s₂ ⟨ j ⟩) (onSum j ((distributeExtended s₀ ⟨ j ⟩) w))
          ⨾  ap (λ v → (gatherExtended s₂ ⟨ j ⟩) ((sumContextMorphism identityH β' ⟨ j ⟩) v))
                (sym (distribute-gather s₁ j ((sumContextMorphism identityH α' ⟨ j ⟩) ((distributeExtended s₀ ⟨ j ⟩) w))))

  weakenWithEmptySequentEquivalence : {k l : Level} (s : Sequent 𝒥 l)
                                      → SequentEquivalence (weakenSequent (emptyContext 𝒥 k) s) s
  weakenWithEmptySequentEquivalence {k} s =
    record
      { contextEquivalence = weakenWithEmptyContextEquivalence {k} (Sequent.context s)
      ; extensionOrCollapseEquality = onExtensionOrCollapse (Sequent.extensionOrCollapse s) }
    where
      ε : emptyContext 𝒥 k + Sequent.context s ⇒ Sequent.context s
      ε = ContextEquivalence.morphism (weakenWithEmptyContextEquivalence {k} (Sequent.context s))

      onExtensionOrCollapse : (e : ExtensionOrCollapse (Sequent.context s))
                            → mapExtensionOrCollapse ε (mapExtensionOrCollapse inrContext e) ≈ e
      onExtensionOrCollapse (extend e) =
        extendEq (mkExtensionEquality refl (record { component≈ = λ j → refl }))
      onExtensionOrCollapse (collapse c) =
        collapseEq (mkCollapseEquality refl (record { component≈ = λ j → refl }))

  fromEmptyContext : {k l : Level} (s : Sequent 𝒥 l) → SequentMorphism (weakenSequent (emptyContext 𝒥 k) s) s
  fromEmptyContext {k} s = toSequentMorphism (weakenWithEmptySequentEquivalence {k} s)

  distributeExtended-empty : {k l : Level} (s : Sequent 𝒥 l) (j : type (Judgment 𝒥))
                             (w : ⌞ extendedContext (weakenSequent (emptyContext 𝒥 k) s) ⟨ j ⟩ ⌟)
                           → (distributeExtended (emptyContext 𝒥 k) s ⟨ j ⟩) w
                             ＝ inr ((fromEmptyContext {k} s ⟨ j ⟩) w)
  distributeExtended-empty (mkSequent Γ (extend e)) j (inl (inr x)) = refl
  distributeExtended-empty (mkSequent Γ (extend e)) j (inr p) = refl
  distributeExtended-empty {k} s@(mkSequent Γ (collapse c)) j =
    ⁄-elim-proposition _
      (λ _ → ＝-isLevel ⦃ level-proof ((emptyContext 𝒥 k + extendedContext s) ⟨ j ⟩) ⦄)
      onClass
    where
      ∅ = emptyContext 𝒥 k

      ε : ∅ + Γ ⇒ Γ
      ε = ContextEquivalence.morphism (weakenWithEmptyContextEquivalence {k} Γ)

      collapseEquality : mapCollapse ε (mapCollapse inrContext c) ≈ c
      collapseEquality = mkCollapseEquality refl (record { component≈ = λ _ → refl })

      open FromAllSetQuotients (⌞ (∅ + Γ) ⟨ j ⟩ ⌟) (CollapseRelation (mapCollapse inrContext c) j)

      onClass : (z : ⌞ (∅ + Γ) ⟨ j ⟩ ⌟)
              → (distributeExtended ∅ s ⟨ j ⟩) ((σ ⟨ j ⟩) z)
                ＝ inr ((fromEmptyContext {k} s ⟨ j ⟩) ((σ ⟨ j ⟩) z))
      onClass (inr x) =
        begin
          (distributeExtended ∅ s ⟨ j ⟩) ((σ ⟨ j ⟩) (inr x))       ⟪ ⁄-rec-β ⦃ bset = level-proof ((∅ + extendedContext s) ⟨ j ⟩) ⦄ _ _ (inr x) ⟫
          inr ((σ ⟨ j ⟩) x)                                        ⟪ ap inr (sym (map⋊ₖ-class ε (mapCollapse inrContext c) c collapseEquality j (inr x))) ⟫
          inr ((fromEmptyContext {k} s ⟨ j ⟩) ((σ ⟨ j ⟩) (inr x))) ∎

  gatherExtended-empty : {k l : Level} (s : Sequent 𝒥 l) (j : type (Judgment 𝒥))
                         (v : ⌞ extendedContext s ⟨ j ⟩ ⌟)
                       → (fromEmptyContext {k} s ⟨ j ⟩) ((gatherExtended (emptyContext 𝒥 k) s ⟨ j ⟩) (inr v))
                         ＝ v
  gatherExtended-empty {k} s j v =
    begin
      (fromEmptyContext {k} s ⟨ j ⟩) (gathered)              ⟪ sym (ap (ε ⟨ j ⟩) (distributeExtended-empty {k} s j gathered)) ⟫
      (ε ⟨ j ⟩) ((distributeExtended ∅ s ⟨ j ⟩) gathered)    ⟪ ap (ε ⟨ j ⟩) (distribute-gather ∅ s j (inr v)) ⟫
      v                                                      ∎
    where
      ∅ = emptyContext 𝒥 k

      ε : ∅ + extendedContext s ⇒ extendedContext s
      ε = ContextEquivalence.morphism (weakenWithEmptyContextEquivalence {k} (extendedContext s))

      gathered = (gatherExtended ∅ s ⟨ j ⟩) (inr v)

  weakenWithEmptySequentEquivalence-natural :
      {k l₀ l₁ : Level} {s₀ : Sequent 𝒥 l₀} {s₁ : Sequent 𝒥 l₁} (α : SequentMorphism s₀ s₁)
    → toSequentMorphism (weakenWithEmptySequentEquivalence {k} s₁)
      ∙ weakenSequentMorphism (emptyContext 𝒥 k) α
      ＝ α ∙ toSequentMorphism (weakenWithEmptySequentEquivalence {k} s₀)
  weakenWithEmptySequentEquivalence-natural {k} {s₀ = s₀} {s₁ = s₁} α =
    ap mkSequentMorphism (eq (record { component≈ = λ j → funExt (pointwise j) }))
    where
      ∅ = emptyContext 𝒥 k
      α' = SequentMorphism.sequentMorphism α

      pointwise : (j : type (Judgment 𝒥)) (w : ⌞ extendedContext (weakenSequent ∅ s₀) ⟨ j ⟩ ⌟)
                → ((fromEmptyContext {k} s₁ ∙ weakenSequentMorphism ∅ α) ⟨ j ⟩) w
                  ＝ ((α ∙ fromEmptyContext {k} s₀) ⟨ j ⟩) w
      pointwise j w =
        begin
          ((fromEmptyContext {k} s₁ ∙ weakenSequentMorphism ∅ α) ⟨ j ⟩) w  ⟪ ap (λ v → (fromEmptyContext {k} s₁ ⟨ j ⟩)
                                                                                              ((gatherExtended ∅ s₁ ⟨ j ⟩)
                                                                                                ((sumContextMorphism (identityH ∅) α' ⟨ j ⟩) v)))
                                                                                       (distributeExtended-empty {k} s₀ j w) ⟫
          (fromEmptyContext {k} s₁ ⟨ j ⟩)
            ((gatherExtended ∅ s₁ ⟨ j ⟩) (inr ((α' ⟨ j ⟩) ((fromEmptyContext {k} s₀ ⟨ j ⟩) w))))
                                                                                 ⟪ gatherExtended-empty {k} s₁ j ((α' ⟨ j ⟩) ((fromEmptyContext {k} s₀ ⟨ j ⟩) w)) ⟫
          ((α ∙ fromEmptyContext {k} s₀) ⟨ j ⟩) w                                ∎



-- =============== Gathering context elements ===============

module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a : Level} {𝒥 : DependentSortVocabulary o a} where

  gatherExtended-onCtx :
      {k l : Level} (H : Context 𝒥 k) (s : Sequent 𝒥 l)
      (j : type (Judgment 𝒥)) (v : ⌞ Sequent.context s ⟨ j ⟩ ⌟)
    → (gatherExtended H s ⟨ j ⟩) (inr ((→⋊ s ⟨ j ⟩) v))
      ＝ (→⋊ (weakenSequent H s) ⟨ j ⟩) (inr v)
  gatherExtended-onCtx H (mkSequent Γ (extend (mkExtension jf args))) j v = refl
  gatherExtended-onCtx {k} {l} H (mkSequent Γ (collapse col@(mkCollapse jf args))) j v =
    ⁄-rec-β ⦃ QΓ.setQuotient j ⦄ ⦃ bset = tgt-isSet j ⦄
            (classT j ∘ inr) _ v
    where
      module QΓ (j' : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ Γ ⟨ j' ⟩ ⌟) (CollapseRelation col j')
      module QT (j' : type (Judgment 𝒥)) =
        FromAllSetQuotients (⌞ (H + Γ) ⟨ j' ⟩ ⌟)
          (CollapseRelation (mapCollapse (inrContext {Γ = H} {Δ = Γ}) col) j')

      tgt-isSet : (j' : type (Judgment 𝒥))
                → isSet ⌞ ((H + Γ) ⋊ₖ mapCollapse (inrContext {Γ = H} {Δ = Γ}) col) ⟨ j' ⟩ ⌟
      tgt-isSet j' = level-proof (((H + Γ) ⋊ₖ mapCollapse (inrContext {Γ = H} {Δ = Γ}) col) ⟨ j' ⟩)

      classT : (j' : type (Judgment 𝒥)) → ⌞ (H + Γ) ⟨ j' ⟩ ⌟
             → ⌞ ((H + Γ) ⋊ₖ mapCollapse (inrContext {Γ = H} {Δ = Γ}) col) ⟨ j' ⟩ ⌟
      classT j' = [_] ⦃ QT.setQuotient j' ⦄


