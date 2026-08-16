module SequentStructure where

open import Prelude
open import Axioms
open import Homotopy.SetQuotient
open import Syntax.Addable
open import Structure.Associativity
open import Structure.Composable
open import Structure.Identity
open import Structure.PreservesComposition
open import Structure.Reasoning
open import Structure.Symmetric
open import Homotopy.StructuredType
open import Algebra.Wild.Semi
open Semicategory.Semicategory
open import Algebra.Wild.TypeSemicategory

open import DependentSortVocabulary
open import Context
open import Sequent

-- ============= Sequent structures ============

record SequentStructure
  ⦃ _ : FunExt ⦄
  ⦃ _ : AllSetQuotients ⦄
  {o a : Level}
  (𝒥 : DependentSortVocabulary {o} {a})
  (so sa i : Level)
  : Type (o ⊔ a ⊔ lsuc so ⊔ lsuc sa ⊔ lsuc i) where
  constructor mkSequentStructure
  field
    dependency : Semicategory so sa
    sequent : Semifunctor (dependency ᵒᵖ) (SequentSemicategory 𝒥 i)

data EmptyOb (so : Level) : Type so where

EmptyHom' : {so : Level} (sa : Level) → EmptyOb so → EmptyOb so → Type sa
EmptyHom' sa () ()

data EmptyHom {so : Level} (sa : Level) (x y : EmptyOb so) : Type sa where
  emptyHom : EmptyHom' sa x y → EmptyHom sa x y

emptySemicategory : (so sa : Level) → Semicategory so sa
emptySemicategory so sa =
  record
    { Ob = EmptyOb so
    ; Hom = EmptyHom sa
    ; semicategorical = record
      { composable = record { composition = λ { {A = ()} _ _ } }
      ; associativeComposition = record { ⨾-associative = λ { {A = ()} } } } }

module _ {co ca : Level} (𝒞 : Semicategory co ca) where

  open Semicategory.Reasoning 𝒞

  emptySemifunctorOnObjects : {so : Level} → EmptyOb so → Ob 𝒞
  emptySemifunctorOnObjects ()

  emptySemifunctor : (so sa : Level) → Semifunctor (emptySemicategory so sa) 𝒞
  emptySemifunctor so sa =
    record
      { onObjects = emptySemifunctorOnObjects
      ; semifunctorial = record
        { mappable = record { map = λ { {A = ()} } }
        ; preservesComposition = record { preserves-composition = λ { {A = ()} } } } }

  emptySemifunctorᵒᵖ : (so sa : Level) → Semifunctor (emptySemicategory so sa ᵒᵖ) 𝒞
  emptySemifunctorᵒᵖ so sa =
    record
      { onObjects = emptySemifunctorOnObjects
      ; semifunctorial = record
        { mappable = record { map = λ { {A = ()} } }
        ; preservesComposition = record { preserves-composition = λ { {A = ()} } } } }

emptySequentStructure : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄ {o a : Level}
                      → (𝒥 : DependentSortVocabulary {o} {a}) (so sa i : Level)
                      → SequentStructure 𝒥 so sa i
emptySequentStructure 𝒥 so sa i =
  record
    { dependency = emptySemicategory so sa
    ; sequent = emptySemifunctorᵒᵖ (SequentSemicategory 𝒥 i) so sa }

record SequentDependencyStructure
  ⦃ _ : FunExt ⦄
  ⦃ _ : AllSetQuotients ⦄
  {o a t : Level}
  (𝒥 : DependentSortVocabulary {o} {a})
  (so sa i : Level)
  (A : Type t)
  (f : A → Context 𝒥 i)
  : Type (o ⊔ a ⊔ lsuc so ⊔ lsuc sa ⊔ lsuc i ⊔ t) where
  constructor mkSequentDependencyStructure
  field
    head : A
    sequentStructure : SequentStructure 𝒥 so sa i
    dependency : Semifunctor (SequentStructure.dependency sequentStructure) (TypeSemicategory sa)
    realiseDependency : (d : Ob (SequentStructure.dependency sequentStructure))
                      → dependency ⟨ d ⟩
                      → ContextMorphism
                          (extendedContext (SequentStructure.sequent sequentStructure ⟨ d ⟩))
                          (f head)
    coherenceRealisation : {d₀ d₁ : Ob (SequentStructure.dependency sequentStructure)}
                         → (f : dependency ⟨ d₀ ⟩) 
                         → (g : Hom (SequentStructure.dependency sequentStructure) d₀ d₁)
                         → realiseDependency d₁ ((dependency ⟨ g ⟩) f)
                         ＝ realiseDependency d₀ f ∙ SequentMorphism.sequentMorphism (SequentStructure.sequent sequentStructure ⟨ g ⟩)
open SequentDependencyStructure

-- =============== Contexts with terms =================

ContextWithTerms : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
                 → {o a : Level} (𝒥 : DependentSortVocabulary {o} {a})
                 → (so sa i : Level)
                 → Type (o ⊔ a ⊔ lsuc so ⊔ lsuc sa ⊔ lsuc i)
ContextWithTerms 𝒥 so sa i = SequentDependencyStructure 𝒥 so sa i (Context 𝒥 i) id


module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄ {o a : Level} {𝒥 : DependentSortVocabulary {o} {a}} where

  toContextWithTerms : {so sa i : Level} → Context 𝒥 i → ContextWithTerms 𝒥 so sa i
  toContextWithTerms {so} {sa} {i} Γ =
    record
      { head = Γ
      ; sequentStructure = emptySequentStructure 𝒥 so sa i
      ; dependency = emptySemifunctor (TypeSemicategory sa) so sa
      ; realiseDependency = λ ()
      ; coherenceRealisation = λ { {()} } }

  addContextToSequent : {k l : Level} → Context 𝒥 k → Sequent 𝒥 l → Sequent 𝒥 (k ⊔ l)
  addContextToSequent c s =
    record
      { context = c + Sequent.context s
      ; extensionOrCollapse = mapExtensionOrCollapse inrContext (Sequent.extensionOrCollapse s) }

  addContextWithTermsToSequent : {to ta i j : Level}
                               → ContextWithTerms 𝒥 to ta i → Sequent 𝒥 j
                               → Sequent 𝒥 (i ⊔ j)
  addContextWithTermsToSequent c s = addContextToSequent (head c) s


  module _ {k : Level} (H : Context 𝒥 k) where

    identityH : H ⇒ H
    identityH = identity

    distributeExtended : {l : Level} (s : Sequent 𝒥 l)
                       → extendedContext (addContextToSequent H s) ⇒ H + extendedContext s
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
                   → H + extendedContext s ⇒ extendedContext (addContextToSequent H s)
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

    addContextToSequentMorphism : {l₀ l₁ : Level} {s₀ : Sequent 𝒥 l₀} {s₁ : Sequent 𝒥 l₁}
                                → SequentMorphism s₀ s₁
                                → SequentMorphism (addContextToSequent H s₀) (addContextToSequent H s₁)
    addContextToSequentMorphism {s₀ = s₀} {s₁ = s₁} α =
      mkSequentMorphism
        (gatherExtended s₁ ∙ (sumContextMorphism identityH (SequentMorphism.sequentMorphism α) ∙ distributeExtended s₀))

    distributeExtended-onAdded : {l : Level} (s : Sequent 𝒥 l) (j : type (Judgment 𝒥)) (u : ⌞ H ⟨ j ⟩ ⌟)
                               → (distributeExtended s ⟨ j ⟩) ((→⋊ (addContextToSequent H s) ⟨ j ⟩) (inl u))
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
                           ＝ (→⋊ (addContextToSequent H s) ⟨ j ⟩) (inl u)
    gatherExtended-onAdded (mkSequent Γ (extend ext)) j u = refl
    gatherExtended-onAdded (mkSequent Γ (collapse col)) j u = refl

    addContextToSequentMorphism-onAdded :
        {l₀ l₁ : Level} {s₀ : Sequent 𝒥 l₀} {s₁ : Sequent 𝒥 l₁}
        (α : SequentMorphism s₀ s₁) (j : type (Judgment 𝒥)) (u : ⌞ H ⟨ j ⟩ ⌟)
      → (addContextToSequentMorphism α ⟨ j ⟩) ((→⋊ (addContextToSequent H s₀) ⟨ j ⟩) (inl u))
        ＝ (→⋊ (addContextToSequent H s₁) ⟨ j ⟩) (inl u)
    addContextToSequentMorphism-onAdded {s₀ = s₀} {s₁ = s₁} α j u =
         ap (λ w → (gatherExtended s₁ ⟨ j ⟩) ((sumContextMorphism identityH (SequentMorphism.sequentMorphism α) ⟨ j ⟩) w))
            (distributeExtended-onAdded s₀ j u)
      ⨾  gatherExtended-onAdded s₁ j u

    addContextToSequentMorphism-composition :
        {l₀ l₁ l₂ : Level} {s₀ : Sequent 𝒥 l₀} {s₁ : Sequent 𝒥 l₁} {s₂ : Sequent 𝒥 l₂}
        (α : SequentMorphism s₀ s₁) (β : SequentMorphism s₁ s₂)
      → addContextToSequentMorphism (α ⨾ β)
        ＝ addContextToSequentMorphism α ⨾ addContextToSequentMorphism β
    addContextToSequentMorphism-composition {s₀ = s₀} {s₁ = s₁} {s₂ = s₂} α β =
      ap mkSequentMorphism (eq (record { component≈ = λ j → funExt (pointwise j) }))
      where
        α' = SequentMorphism.sequentMorphism α
        β' = SequentMorphism.sequentMorphism β

        onSum : (j : type (Judgment 𝒥)) (u : ⌞ (H + extendedContext s₀) ⟨ j ⟩ ⌟)
              → (sumContextMorphism identityH (β' ∙ α') ⟨ j ⟩) u
              ＝ (sumContextMorphism identityH β' ⟨ j ⟩) ((sumContextMorphism identityH α' ⟨ j ⟩) u)
        onSum j (inl h) = refl
        onSum j (inr v) = refl

        pointwise : (j : type (Judgment 𝒥)) (w : ⌞ extendedContext (addContextToSequent H s₀) ⟨ j ⟩ ⌟)
                  → (addContextToSequentMorphism (α ⨾ β) ⟨ j ⟩) w
                  ＝ ((addContextToSequentMorphism α ⨾ addContextToSequentMorphism β) ⟨ j ⟩) w
        pointwise j w =
             ap (gatherExtended s₂ ⟨ j ⟩) (onSum j ((distributeExtended s₀ ⟨ j ⟩) w))
          ⨾  ap (λ v → (gatherExtended s₂ ⟨ j ⟩) ((sumContextMorphism identityH β' ⟨ j ⟩) v))
                (sym (distribute-gather s₁ j ((sumContextMorphism identityH α' ⟨ j ⟩) ((distributeExtended s₀ ⟨ j ⟩) w))))

  addContextWithTermsToSequentStructure : {so sa i : Level}
                                        → ContextWithTerms 𝒥 so sa i → SequentStructure 𝒥 so sa i
                                        → SequentStructure 𝒥 so sa i
  addContextWithTermsToSequentStructure {so} {sa} {i} c ss =
    record
      { dependency =
          record
            { Ob = depOb
            ; Hom = depHom
            ; semicategorical =
                record
                  { composable =
                      record { composition = λ {A} {B} {C} → depComposition {A} {B} {C} }
                  ; associativeComposition =
                      record { ⨾-associative = λ {A} {B} {C} {D} {f} {g} {h} → depAssociative {A} {B} {C} {D} {f} {g} {h} } } }
      ; sequent =
          record
            { onObjects = onObjects
            ; semifunctorial =
                record
                  { mappable =
                      record
                        { map = λ {x} {y} → map {x} {y} }
                  ; preservesComposition =
                      record { preserves-composition = λ {A} {B} {C} g h → preserves {C} {B} {A} h g } } } }
    where
      𝒞 = SequentStructure.dependency (SequentDependencyStructure.sequentStructure c)
      ℱ = SequentStructure.sequent (SequentDependencyStructure.sequentStructure c)
      𝒟 = SequentStructure.dependency ss
      𝒢 = SequentStructure.sequent ss

      open Semicategory.Reasoning 𝒞
      open Semicategory.Reasoning (𝒞 ᵒᵖ)
      open Semicategory.Reasoning 𝒟
      open Semicategory.Reasoning (𝒟 ᵒᵖ)
      open Semicategory.Reasoning (TypeSemicategory sa)
      open Semifunctor.Reasoning (SequentDependencyStructure.dependency c)

      depOb : Type so
      depOb = Ob 𝒞 + Ob 𝒟

      depHom : depOb → depOb → Type sa
      depHom (inl x) (inl y) = Hom 𝒞 x y
      depHom (inl x) (inr y) = Empty
      depHom (inr x) (inl y) = SequentDependencyStructure.dependency c ⟨ y ⟩
      depHom (inr x) (inr y) = Hom 𝒟 x y

      depComposition : {A B C : depOb} → depHom A B → depHom B C → depHom A C
      depComposition {inl x} {inl y} {inl z} f g = g ∙ f
      depComposition {inl x} {inl y} {inr z} f ()
      depComposition {inl x} {inr y} {C} () g
      depComposition {inr x} {inl y} {inl z} f g = (SequentDependencyStructure.dependency c ⟨ g ⟩) f
      depComposition {inr x} {inl y} {inr z} f ()
      depComposition {inr x} {inr y} {inl z} f g = g
      depComposition {inr x} {inr y} {inr z} f g = g ∙ f

      depAssociative : {A B C D : depOb} {f : depHom A B} {g : depHom B C} {h : depHom C D}
                     → depComposition {A} {C} {D} (depComposition {A} {B} {C} f g) h
                     ＝ depComposition {A} {B} {D} f (depComposition {B} {C} {D} g h)
      depAssociative {inl w} {inl x} {inl y} {inl z} = ⨾-associative
      depAssociative {inr w} {inl x} {inl y} {inl z} {f} {g} {h} = sym (ap (λ σ → σ f) (preserves-composition g h))
      depAssociative {inr w} {inr x} {inl y} {inl z} = refl
      depAssociative {inr w} {inr x} {inr y} {inl z} = refl
      depAssociative {inr w} {inr x} {inr y} {inr z} = ⨾-associative
      depAssociative {A} {B} {inl y} {inr z} {g = g} {h = ()}
      depAssociative {A} {inl x} {inr y} {D} {g = ()}
      depAssociative {inl w} {inr x} {C} {D} {f = ()}

      onObjects : depOb → Sequent 𝒥 i
      onObjects (inl x) = ℱ ⟨ x ⟩
      onObjects (inr x) = addContextWithTermsToSequent c (𝒢 ⟨ x ⟩)

      map : {x y : depOb}
          → depHom y x
          → SequentMorphism (onObjects x) (onObjects y)
      map {inl x} {inl y} f = ℱ ⟨ f ⟩
      map {inl x} {inr y} f =
        mkSequentMorphism (→⋊ (onObjects (inr y)) ∙ (inlContext ∙ realiseDependency c x f))
      map {inr x} {inr y} f = addContextToSequentMorphism (head c) (𝒢 ⟨ f ⟩)

      preserves : {A B C : depOb} (f : depHom A B) (g : depHom B C)
                → map {C} {A} (depComposition {A} {B} {C} f g) ＝ map {B} {A} f ∙ map {C} {B} g
      preserves {inl x} {inl y} {inl z} f g = PreservesComposition.preserves-composition pres _ _
        where
          open Semifunctor.Reasoning ℱ renaming (preservesCompositionₛ to pres)
          open Semicategory.Reasoning (SequentSemicategory 𝒥 i)
      preserves {inl x} {inl y} {inr z} f ()
      preserves {inl x} {inr y} {C} () g
      preserves {inr x} {inl y} {inl z} f g = ap mkSequentMorphism
        (   ap (λ σ → →⋊ s ∙ (inlContext ∙ σ)) (coherenceRealisation c f g)
         ⨾  ap (→⋊ s ∙_) (∙-associative {f = ℱg} {g = realiseDependency c y f} {h = inlContext})
         ⨾  ∙-associative {f = ℱg} {g = inlContext ∙ realiseDependency c y f} {h = →⋊ s})
        where
          s = onObjects (inr x)
          ℱg = SequentMorphism.sequentMorphism (ℱ ⟨ g ⟩)
      preserves {inr x} {inl y} {inr z} f ()
      preserves {inr x} {inr y} {inl z} f g =
        ap mkSequentMorphism
          (eq (record
                 { component≈ = λ j → funExt λ w →
                     sym (addContextToSequentMorphism-onAdded (head c) (𝒢 ⟨ f ⟩) j
                            ((realiseDependency c z g ⟨ j ⟩) w)) }))
      preserves {inr x} {inr y} {inr z} f g =
           ap (addContextToSequentMorphism (head c)) (PreservesComposition.preserves-composition pres g f)
        ⨾  addContextToSequentMorphism-composition (head c) (𝒢 ⟨ g ⟩) (𝒢 ⟨ f ⟩)
        where
          open Semifunctor.Reasoning 𝒢 renaming (preservesCompositionₛ to pres)
          open Semicategory.Reasoning (SequentSemicategory 𝒥 i)

-- =============== Morphisms of sequent structures ===============

dependenciesOf : {so sa : Level} (𝒟 : Semicategory so sa) → Ob 𝒟 → Type (so ⊔ sa)
dependenciesOf 𝒟 x = ∑[ y ∶ Ob 𝒟 ] Hom 𝒟 x y

mapDependencies : {so₀ sa₀ so₁ sa₁ : Level}
                  {𝒞 : Semicategory so₀ sa₀} {𝒟 : Semicategory so₁ sa₁}
                → (F : Semifunctor 𝒞 𝒟) (x : Ob 𝒞)
                → dependenciesOf 𝒞 x → dependenciesOf 𝒟 (F ⟨ x ⟩)
mapDependencies F x (y , f) = F ⟨ y ⟩ , F ⟨ f ⟩

record SequentStructureMorphism
  ⦃ _ : FunExt ⦄
  ⦃ _ : AllSetQuotients ⦄
  {o a so₀ sa₀ i₀ so₁ sa₁ i₁ : Level}
  {𝒥 : DependentSortVocabulary {o} {a}}
  (sd : SequentStructure 𝒥 so₀ sa₀ i₀)
  (sc : SequentStructure 𝒥 so₁ sa₁ i₁)
  -- (to ta i j : Level)
  : Type (o ⊔ a ⊔ so₀ ⊔ sa₀ ⊔ i₀ ⊔ so₁ ⊔ sa₁ ⊔ i₁ ) where
  constructor mkSequentStructureMorphism
  field
    onDependencies : Semifunctor (SequentStructure.dependency sd) (SequentStructure.dependency sc)
    dependenciesEquivalence : (x : Ob (SequentStructure.dependency sd))
                            → isEquivalence (mapDependencies onDependencies x)
    -- baseContext : ContextWithTerms 𝒥 to ta i j
    -- contextEquivalence : (x : Ob (SequentStructure.dependency sd))
    --                    → baseContext + Sequent.context (SequentStructure.sequent sd ⟨ x ⟩)
    --                    ≈ Sequent.context (SequentStructure.sequent sc ⟨ onDependencies ⟨ x ⟩ ⟩)
    -- TODO: add naturality condition wrt onDependencies and SequentStructure.sequent
