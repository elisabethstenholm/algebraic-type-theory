module Context.ExtensionMorphism where

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
open import Algebra.Wild.Semi
open Semicategory using (tr-hom)
open import Algebra.Wild.TruncatedTypeSemicategory
open import Homotopy.SetQuotient
open import Syntax.Arrowable
open import Foundation.Sum.Equivalence
open import Structure.Bimappable

open import DependentSortVocabulary
open DependentSortVocabulary.DependentSortVocabulary


open import Context
open import Context.Morphism
open import Context.Extension

open ContextMorphismEquality

-- ============== Extending a context morphism ==============

module _ ⦃ _ : FunExt ⦄
  {o a i j : Level} {𝒥 : DependentSortVocabulary o a}
  {Γ : Context 𝒥 i} {Δ : Context 𝒥 j}
  (α : Γ ⇒ Δ) where

  map⋊ₑ : (e₀ : Extension Γ) (e₁ : Extension Δ)
        → mapExtension α e₀ ≈ e₁ → Γ ⋊ₑ e₀ ⇒ Δ ⋊ₑ e₁
  map⋊ₑ e₀@(mkExtension j₀ a₀) e₁@(mkExtension .j₀ a₁) (mkExtensionEquality refl a≈) =
    record
      { component = component
      ; natural = funExt ∘ natural~ }
    where
      component : (j' : type (Judgment 𝒥)) → ⌞ (Γ ⋊ₑ e₀) ⟨ j' ⟩ ⌟ → ⌞ (Δ ⋊ₑ e₁) ⟨ j' ⟩ ⌟
      component j' (inl x) = inl ((α ⟨ j' ⟩) x)
      component j' (inr p) = inr p

      natural~ : {j₀' j₁' : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀' j₁'))
               → (Δ ⋊ₑ e₁) ⟨ f ⟩ ∘ component j₀' ~ component j₁' ∘ (Γ ⋊ₑ e₀) ⟨ f ⟩
      natural~ f (inl x) = ap (λ h → inl (h x)) (ContextMorphism.natural α f)
      natural~ {j₁' = j₁'} f (inr refl) = ap (λ h → inl (h f)) (sym (component≈ a≈ j₁'))

module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a i j : Level} {𝒥 : DependentSortVocabulary o a}
  {Γ : Context 𝒥 i} {Δ : Context 𝒥 j}
  (α : Γ ⇒ Δ) where

  map⋊ₖ : (c₀ : Collapse Γ) (c₁ : Collapse Δ)
        → mapCollapse α c₀ ≈ c₁ → Γ ⋊ₖ c₀ ⇒ Δ ⋊ₖ c₁
  map⋊ₖ c₀@(mkCollapse j₀ a₀) c₁@(mkCollapse .j₀ a₁) (mkCollapseEquality refl a≈) =
    record
      { component = component
      ; natural = funExt ∘ natural~ }
    where
      module QΓ (j' : type (Judgment 𝒥)) = FromAllSetQuotients (⌞ Γ ⟨ j' ⟩ ⌟) (CollapseRelation c₀ j')
      module QΔ (j' : type (Judgment 𝒥)) = FromAllSetQuotients (⌞ Δ ⟨ j' ⟩ ⌟) (CollapseRelation c₁ j')

      classΓ : (j' : type (Judgment 𝒥)) → ⌞ Γ ⟨ j' ⟩ ⌟ → ⌞ (Γ ⋊ₖ c₀) ⟨ j' ⟩ ⌟
      classΓ j' = [_] ⦃ QΓ.setQuotient j' ⦄

      classΔ : (j' : type (Judgment 𝒥)) → ⌞ Δ ⟨ j' ⟩ ⌟ → ⌞ (Δ ⋊ₖ c₁) ⟨ j' ⟩ ⌟
      classΔ j' = [_] ⦃ QΔ.setQuotient j' ⦄

      resp : (j' : type (Judgment 𝒥)) {x y : ⌞ Γ ⟨ j' ⟩ ⌟}
           → CollapseRelation c₀ j' x y
           → classΔ j' ((α ⟨ j' ⟩) x) ＝ classΔ j' ((α ⟨ j' ⟩) y)
      resp j' collapseRelation =
        begin
          classΔ j₀ ((α ⟨ j₀ ⟩) ((a₀ ⟨ j₀ ⟩) (inr (inl refl))))  ⟪ ap (λ h → classΔ j₀ (h (inr (inl refl)))) (component≈ a≈ j₀) ⟫
          classΔ j₀ ((a₁ ⟨ j₀ ⟩) (inr (inl refl)))               ⟪ respects ⦃ QΔ.setQuotient j₀ ⦄ collapseRelation ⟫
          classΔ j₀ ((a₁ ⟨ j₀ ⟩) (inr (inr refl)))               ⟪ sym (ap (λ h → classΔ j₀ (h (inr (inr refl)))) (component≈ a≈ j₀)) ⟫
          classΔ j₀ ((α ⟨ j₀ ⟩) ((a₀ ⟨ j₀ ⟩) (inr (inr refl))))  ∎

      component : (j' : type (Judgment 𝒥)) → ⌞ (Γ ⋊ₖ c₀) ⟨ j' ⟩ ⌟ → ⌞ (Δ ⋊ₖ c₁) ⟨ j' ⟩ ⌟
      component j' = ⁄-rec ⦃ QΓ.setQuotient j' ⦄ ⦃ bset = level-proof ((Δ ⋊ₖ c₁) ⟨ j' ⟩) ⦄
                           (classΔ j' ∘ (α ⟨ j' ⟩)) (resp j')

      natural~ : {j₀' j₁' : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀' j₁'))
               → (Δ ⋊ₖ c₁) ⟨ f ⟩ ∘ component j₀' ~ component j₁' ∘ (Γ ⋊ₖ c₀) ⟨ f ⟩
      natural~ {j₀'} {j₁'} f =
        ⁄-elim-proposition ⦃ QΓ.setQuotient j₀' ⦄
          (λ q → ((Δ ⋊ₖ c₁) ⟨ f ⟩) (component j₀' q) ＝ component j₁' (((Γ ⋊ₖ c₀) ⟨ f ⟩) q))
          (λ _ → ＝-isLevel ⦃ level-proof ((Δ ⋊ₖ c₁) ⟨ j₁' ⟩) ⦄)
          pointwise
        where
          pointwise : (x : ⌞ Γ ⟨ j₀' ⟩ ⌟)
                    → ((Δ ⋊ₖ c₁) ⟨ f ⟩) (component j₀' (classΓ j₀' x))
                      ＝ component j₁' (((Γ ⋊ₖ c₀) ⟨ f ⟩) (classΓ j₀' x))
          pointwise x =
            begin
              ((Δ ⋊ₖ c₁) ⟨ f ⟩) (component j₀' (classΓ j₀' x))  ⟪ ap ((Δ ⋊ₖ c₁) ⟨ f ⟩)
                                                                     (⁄-rec-β ⦃ QΓ.setQuotient j₀' ⦄ ⦃ bset = level-proof ((Δ ⋊ₖ c₁) ⟨ j₀' ⟩) ⦄
                                                                              (classΔ j₀' ∘ (α ⟨ j₀' ⟩)) (resp j₀') x) ⟫
              ((Δ ⋊ₖ c₁) ⟨ f ⟩) (classΔ j₀' ((α ⟨ j₀' ⟩) x))    ⟪ ⁄-rec-β ⦃ QΔ.setQuotient j₀' ⦄ ⦃ bset = level-proof ((Δ ⋊ₖ c₁) ⟨ j₁' ⟩) ⦄
                                                                          (classΔ j₁' ∘ (Δ ⟨ f ⟩)) _ ((α ⟨ j₀' ⟩) x) ⟫
              classΔ j₁' ((Δ ⟨ f ⟩) ((α ⟨ j₀' ⟩) x))            ⟪ ap (classΔ j₁') (ap (λ h → h x) (ContextMorphism.natural α f)) ⟫
              classΔ j₁' ((α ⟨ j₁' ⟩) ((Γ ⟨ f ⟩) x))            ⟪ sym (⁄-rec-β ⦃ QΓ.setQuotient j₁' ⦄ ⦃ bset = level-proof ((Δ ⋊ₖ c₁) ⟨ j₁' ⟩) ⦄
                                                                               (classΔ j₁' ∘ (α ⟨ j₁' ⟩)) (resp j₁') ((Γ ⟨ f ⟩) x)) ⟫
              component j₁' (classΓ j₁' ((Γ ⟨ f ⟩) x))          ⟪ ap (component j₁')
                                                                     (sym (⁄-rec-β ⦃ QΓ.setQuotient j₀' ⦄ ⦃ bset = level-proof ((Γ ⋊ₖ c₀) ⟨ j₁' ⟩) ⦄
                                                                                   (classΓ j₁' ∘ (Γ ⟨ f ⟩)) _ x)) ⟫
              component j₁' (((Γ ⋊ₖ c₀) ⟨ f ⟩) (classΓ j₀' x))  ∎

  map⋊ : (e₀ : ExtensionOrCollapse Γ) (e₁ : ExtensionOrCollapse Δ)
       → mapExtensionOrCollapse α e₀ ≈ e₁ → Γ ⋊ e₀ ⇒ Δ ⋊ e₁
  map⋊ (extend e₀) (extend e₁) (extendEq q) = map⋊ₑ α e₀ e₁ q
  map⋊ (collapse c₀) (collapse c₁) (collapseEq q) = map⋊ₖ c₀ c₁ q

  map⋊ₖ-class : (c₀ : Collapse Γ) (c₁ : Collapse Δ)
                (p : mapCollapse α c₀ ≈ c₁) (j' : type (Judgment 𝒥)) (x : ⌞ Γ ⟨ j' ⟩ ⌟)
              → (map⋊ₖ c₀ c₁ p ⟨ j' ⟩) ((σ {Γ = Γ} {c = c₀} ⟨ j' ⟩) x)
                ＝ (σ {Γ = Δ} {c = c₁} ⟨ j' ⟩) ((α ⟨ j' ⟩) x)
  map⋊ₖ-class c₀@(mkCollapse j₀ a₀) c₁@(mkCollapse .j₀ a₁) (mkCollapseEquality refl a≈) j' x =
    ⁄-rec-β ⦃ bset = level-proof ((Δ ⋊ₖ c₁) ⟨ j' ⟩) ⦄ _ _ x
    where
      open FromAllSetQuotients (⌞ Γ ⟨ j' ⟩ ⌟) (CollapseRelation c₀ j')


-- ============== Composing extended context morphisms ==============

module _ ⦃ _ : FunExt ⦄
  {o a i j k : Level} {𝒥 : DependentSortVocabulary o a}
  {Γ : Context 𝒥 i} {Δ : Context 𝒥 j} {Θ : Context 𝒥 k}
  (α : Γ ⇒ Δ) (β : Δ ⇒ Θ) where

  mapExtension-⨾ : (e₀ : Extension Γ) (e₁ : Extension Δ) (e₂ : Extension Θ)
                 → mapExtension α e₀ ≈ e₁ → mapExtension β e₁ ≈ e₂
                 → mapExtension (α ⨾ β) e₀ ≈ e₂
  mapExtension-⨾ (mkExtension j₀ a₀) (mkExtension .j₀ a₁) (mkExtension .j₀ a₂)
                 (mkExtensionEquality refl p) (mkExtensionEquality refl q) =
    mkExtensionEquality refl (record { component≈ = component≈~ })
    where
      component≈~ : (j' : type (Judgment 𝒥)) → ((α ⨾ β) ∙ a₀) ⟨ j' ⟩ ＝ a₂ ⟨ j' ⟩
      component≈~ j' =
        begin
          ((α ⨾ β) ∙ a₀) ⟨ j' ⟩     ⟪ ap ((β ⟨ j' ⟩) ∘_) (component≈ p j') ⟫
          (β ⟨ j' ⟩) ∘ (a₁ ⟨ j' ⟩)  ⟪ component≈ q j' ⟫
          a₂ ⟨ j' ⟩                 ∎

  mapCollapse-⨾ : (c₀ : Collapse Γ) (c₁ : Collapse Δ) (c₂ : Collapse Θ)
                → mapCollapse α c₀ ≈ c₁ → mapCollapse β c₁ ≈ c₂
                → mapCollapse (α ⨾ β) c₀ ≈ c₂
  mapCollapse-⨾ (mkCollapse j₀ a₀) (mkCollapse .j₀ a₁) (mkCollapse .j₀ a₂)
                (mkCollapseEquality refl p) (mkCollapseEquality refl q) =
    mkCollapseEquality refl (record { component≈ = component≈~ })
    where
      component≈~ : (j' : type (Judgment 𝒥)) → ((α ⨾ β) ∙ a₀) ⟨ j' ⟩ ＝ a₂ ⟨ j' ⟩
      component≈~ j' =
        begin
          ((α ⨾ β) ∙ a₀) ⟨ j' ⟩     ⟪ ap ((β ⟨ j' ⟩) ∘_) (component≈ p j') ⟫
          (β ⟨ j' ⟩) ∘ (a₁ ⟨ j' ⟩)  ⟪ component≈ q j' ⟫
          a₂ ⟨ j' ⟩                 ∎

  mapExtensionOrCollapse-⨾ : (e₀ : ExtensionOrCollapse Γ) (e₁ : ExtensionOrCollapse Δ) (e₂ : ExtensionOrCollapse Θ)
                           → mapExtensionOrCollapse α e₀ ≈ e₁ → mapExtensionOrCollapse β e₁ ≈ e₂
                           → mapExtensionOrCollapse (α ⨾ β) e₀ ≈ e₂
  mapExtensionOrCollapse-⨾ (extend e₀) (extend e₁) (extend e₂) (extendEq p) (extendEq q) =
    extendEq (mapExtension-⨾ e₀ e₁ e₂ p q)
  mapExtensionOrCollapse-⨾ (collapse c₀) (collapse c₁) (collapse c₂) (collapseEq p) (collapseEq q) =
    collapseEq (mapCollapse-⨾ c₀ c₁ c₂ p q)

module _ ⦃ _ : FunExt ⦄
  {o a i : Level} {𝒥 : DependentSortVocabulary o a} {Γ : Context 𝒥 i} where

  mapExtension-identity : (e : Extension Γ) → mapExtension identity e ≈ e
  mapExtension-identity (mkExtension j₀ a₀) =
    mkExtensionEquality refl (record { component≈ = λ j' → refl })

  mapCollapse-identity : (c : Collapse Γ) → mapCollapse identity c ≈ c
  mapCollapse-identity (mkCollapse j₀ a₀) =
    mkCollapseEquality refl (record { component≈ = λ j' → refl })

  mapExtensionOrCollapse-identity : (e : ExtensionOrCollapse Γ) → mapExtensionOrCollapse identity e ≈ e
  mapExtensionOrCollapse-identity (extend e) = extendEq (mapExtension-identity e)
  mapExtensionOrCollapse-identity (collapse c) = collapseEq (mapCollapse-identity c)

module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a i j k : Level} {𝒥 : DependentSortVocabulary o a}
  {Γ : Context 𝒥 i} {Δ : Context 𝒥 j} {Θ : Context 𝒥 k}
  (α : Γ ⇒ Δ) (β : Δ ⇒ Θ) where

  map⋊-⨾ : (e₀ : ExtensionOrCollapse Γ) (e₁ : ExtensionOrCollapse Δ) (e₂ : ExtensionOrCollapse Θ)
           (p : mapExtensionOrCollapse α e₀ ≈ e₁) (q : mapExtensionOrCollapse β e₁ ≈ e₂)
         → map⋊ (α ⨾ β) e₀ e₂ (mapExtensionOrCollapse-⨾ α β e₀ e₁ e₂ p q)
           ＝ map⋊ α e₀ e₁ p ⨾ map⋊ β e₁ e₂ q
  map⋊-⨾ (extend (mkExtension j₀ a₀)) (extend (mkExtension .j₀ a₁)) (extend (mkExtension .j₀ a₂))
         (extendEq (mkExtensionEquality refl p)) (extendEq (mkExtensionEquality refl q)) =
    eq (record { component≈ = λ j' → funExt (λ { (inl x) → refl ; (inr r) → refl }) })
  map⋊-⨾ (collapse c₀@(mkCollapse j₀ a₀)) (collapse c₁@(mkCollapse .j₀ a₁)) (collapse c₂@(mkCollapse .j₀ a₂))
         P@(collapseEq p'@(mkCollapseEquality refl p)) Q@(collapseEq q'@(mkCollapseEquality refl q)) =
    eq (record { component≈ = λ j' → funExt (pointwise j') })
    where
      mapα  = map⋊ α (collapse c₀) (collapse c₁) P
      mapβ  = map⋊ β (collapse c₁) (collapse c₂) Q
      mapαβ = map⋊ (α ⨾ β) (collapse c₀) (collapse c₂)
                   (mapExtensionOrCollapse-⨾ α β (collapse c₀) (collapse c₁) (collapse c₂) P Q)

      pointwise : (j' : type (Judgment 𝒥)) (z : ⌞ (Γ ⋊ₖ c₀) ⟨ j' ⟩ ⌟)
                → (mapαβ ⟨ j' ⟩) z ＝ ((mapα ⨾ mapβ) ⟨ j' ⟩) z
      pointwise j' =
        ⁄-elim-proposition _ (λ _ → ＝-isLevel ⦃ level-proof ((Θ ⋊ₖ c₂) ⟨ j' ⟩) ⦄) onClass
        where
          open FromAllSetQuotients (⌞ Γ ⟨ j' ⟩ ⌟) (CollapseRelation c₀ j')

          onClass : (x : ⌞ Γ ⟨ j' ⟩ ⌟)
                  → (mapαβ ⟨ j' ⟩) ((σ {c = c₀} ⟨ j' ⟩) x)
                    ＝ ((mapα ⨾ mapβ) ⟨ j' ⟩) ((σ {c = c₀} ⟨ j' ⟩) x)
          onClass x =
            begin
              (mapαβ ⟨ j' ⟩) ((σ {c = c₀} ⟨ j' ⟩) x)                 ⟪ map⋊ₖ-class (α ⨾ β) c₀ c₂ (mapCollapse-⨾ α β c₀ c₁ c₂ p' q') j' x ⟫
              (σ {c = c₂} ⟨ j' ⟩) ((β ⟨ j' ⟩) ((α ⟨ j' ⟩) x))        ⟪ sym (map⋊ₖ-class β c₁ c₂ q' j' ((α ⟨ j' ⟩) x)) ⟫
              (mapβ ⟨ j' ⟩) ((σ {c = c₁} ⟨ j' ⟩) ((α ⟨ j' ⟩) x))     ⟪ ap (mapβ ⟨ j' ⟩) (sym (map⋊ₖ-class α c₀ c₁ p' j' x)) ⟫
              (mapβ ⟨ j' ⟩) ((mapα ⟨ j' ⟩) ((σ {c = c₀} ⟨ j' ⟩) x))  ∎


module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a i : Level} {𝒥 : DependentSortVocabulary o a} {Γ : Context 𝒥 i} where

  map⋊-identity : (E : ExtensionOrCollapse Γ)
                → map⋊ identity E E (mapExtensionOrCollapse-identity E) ≈ identity
  map⋊-identity (extend (mkExtension j a)) =
    record { component≈ = λ j' → funExt (λ { (inl x) → refl ; (inr p) → refl }) }
  map⋊-identity (collapse c@(mkCollapse j a)) =
    record { component≈ = λ j' → funExt (onClass j') }
    where
      onClass : (j' : type (Judgment 𝒥)) (q : ⌞ (Γ ⋊ₖ c) ⟨ j' ⟩ ⌟)
              → (map⋊ₖ identity c c (mapCollapse-identity c) ⟨ j' ⟩) q ＝ q
      onClass j' =
        ⁄-elim-proposition
          (λ q → (map⋊ₖ identity c c (mapCollapse-identity c) ⟨ j' ⟩) q ＝ q)
          (λ _ → ＝-isLevel ⦃ level-proof ((Γ ⋊ₖ c) ⟨ j' ⟩) ⦄)
          (λ x → map⋊ₖ-class identity c c (mapCollapse-identity c) j' x)
        where open FromAllSetQuotients (⌞ Γ ⟨ j' ⟩ ⌟) (CollapseRelation c j')


module _ ⦃ _ : FunExt ⦄
  {o a i j : Level} {𝒥 : DependentSortVocabulary o a}
  {Γ : Context 𝒥 i} {Δ : Context 𝒥 j}
  (w : ContextEquivalence Γ Δ) where

  private
    α : Γ ⇒ Δ
    α = ContextEquivalence.morphism w

    αEquiv : (j' : type (Judgment 𝒥)) → isEquivalence (α ⟨ j' ⟩)
    αEquiv = ContextEquivalence.component-isEquivalence w

  map⋊ₑ-isEquivalence : (e₀ : Extension Γ) (e₁ : Extension Δ)
                        (q : mapExtension α e₀ ≈ e₁)
                        (j' : type (Judgment 𝒥))
                      → isEquivalence (map⋊ₑ α e₀ e₁ q ⟨ j' ⟩)
  map⋊ₑ-isEquivalence e₀@(mkExtension j₀ a₀) e₁@(mkExtension _ a₁)
                      (mkExtensionEquality refl a≈) j' =
    makeIsEquivalence
      (record { sectionBack = backS ; isSection = isSection~ })
      (record { retractionBack = backR ; isRetraction = isRetraction~ })
    where
      backS : ⌞ (Δ ⋊ₑ e₁) ⟨ j' ⟩ ⌟ → ⌞ (Γ ⋊ₑ e₀) ⟨ j' ⟩ ⌟
      backS (inl y) = inl (sectionBack (section (αEquiv j')) y)
      backS (inr p) = inr p

      backR : ⌞ (Δ ⋊ₑ e₁) ⟨ j' ⟩ ⌟ → ⌞ (Γ ⋊ₑ e₀) ⟨ j' ⟩ ⌟
      backR (inl y) = inl (retractionBack (retraction (αEquiv j')) y)
      backR (inr p) = inr p

      isSection~ : (y : ⌞ (Δ ⋊ₑ e₁) ⟨ j' ⟩ ⌟)
                 → (map⋊ₑ α e₀ e₁ (mkExtensionEquality refl a≈) ⟨ j' ⟩) (backS y) ＝ y
      isSection~ (inl y) = ap inl (isSection (section (αEquiv j')) y)
      isSection~ (inr p) = refl

      isRetraction~ : (x : ⌞ (Γ ⋊ₑ e₀) ⟨ j' ⟩ ⌟)
                    → backR ((map⋊ₑ α e₀ e₁ (mkExtensionEquality refl a≈) ⟨ j' ⟩) x) ＝ x
      isRetraction~ (inl x) = ap inl (isRetraction (retraction (αEquiv j')) x)
      isRetraction~ (inr p) = refl


module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a i j : Level} {𝒥 : DependentSortVocabulary o a}
  {Γ : Context 𝒥 i} {Δ : Context 𝒥 j}
  (w : ContextEquivalence Γ Δ) where

  private
    α : Γ ⇒ Δ
    α = ContextEquivalence.morphism w

    αEquiv : (j' : type (Judgment 𝒥)) → isEquivalence (α ⟨ j' ⟩)
    αEquiv = ContextEquivalence.component-isEquivalence w

  backwards : (j' : type (Judgment 𝒥)) → ⌞ Δ ⟨ j' ⟩ ⌟ → ⌞ Γ ⟨ j' ⟩ ⌟
  backwards j' = sectionBack (section (αEquiv j'))

  backwardsSection : (j' : type (Judgment 𝒥)) (y : ⌞ Δ ⟨ j' ⟩ ⌟)
                   → (α ⟨ j' ⟩) (backwards j' y) ＝ y
  backwardsSection j' = isSection (section (αEquiv j'))

  backwardsRetraction : (j' : type (Judgment 𝒥)) (x : ⌞ Γ ⟨ j' ⟩ ⌟)
                   → backwards j' ((α ⟨ j' ⟩) x) ＝ x
  backwardsRetraction j' x =
       sym (isRetraction (retraction (αEquiv j')) (backwards j' ((α ⟨ j' ⟩) x)))
    ⨾  ap (retractionBack (retraction (αEquiv j'))) (backwardsSection j' ((α ⟨ j' ⟩) x))
    ⨾  isRetraction (retraction (αEquiv j')) x

  inverseContextMorphism : Δ ⇒ Γ
  inverseContextMorphism =
    record { component = backwards ; natural = λ f → funExt (natural~ f) }
    where
      natural~ : {j₀ j₁ : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀ j₁))
               → Γ ⟨ f ⟩ ∘ backwards j₀ ~ backwards j₁ ∘ Δ ⟨ f ⟩
      natural~ {j₀} {j₁} f y =
           sym (backwardsRetraction j₁ ((Γ ⟨ f ⟩) (backwards j₀ y)))
        ⨾  ap (backwards j₁)
              (sym (ap (λ h → h (backwards j₀ y)) (ContextMorphism.natural α f)))
        ⨾  ap (λ z → backwards j₁ ((Δ ⟨ f ⟩) z)) (backwardsSection j₀ y)

  map⋊ₖ-isEquivalence : (c₀ : Collapse Γ) (c₁ : Collapse Δ)
                        (q : mapCollapse α c₀ ≈ c₁)
                        (j' : type (Judgment 𝒥))
                      → isEquivalence (map⋊ₖ α c₀ c₁ q ⟨ j' ⟩)
  map⋊ₖ-isEquivalence c₀@(mkCollapse j₀ a₀) c₁@(mkCollapse _ a₁)
                      q@(mkCollapseEquality refl a≈) j' =
    makeIsEquivalence
      (record { sectionBack = back j' ; isSection = isSection~ })
      (record { retractionBack = back j' ; isRetraction = isRetraction~ })
    where
      classΓ : (k : type (Judgment 𝒥)) → ⌞ Γ ⟨ k ⟩ ⌟ → ⌞ (Γ ⋊ₖ c₀) ⟨ k ⟩ ⌟
      classΓ k = [_]
        where open FromAllSetQuotients (⌞ Γ ⟨ k ⟩ ⌟) (CollapseRelation c₀ k)

      classΔ : (k : type (Judgment 𝒥)) → ⌞ Δ ⟨ k ⟩ ⌟ → ⌞ (Δ ⋊ₖ c₁) ⟨ k ⟩ ⌟
      classΔ k = [_]
        where open FromAllSetQuotients (⌞ Δ ⟨ k ⟩ ⌟) (CollapseRelation c₁ k)

      resp : (k : type (Judgment 𝒥)) {u v : ⌞ Δ ⟨ k ⟩ ⌟}
           → CollapseRelation c₁ k u v
           → classΓ k (backwards k u) ＝ classΓ k (backwards k v)
      resp _ collapseRelation =
           ap (λ z → classΓ j₀ (backwards j₀ z))
              (sym (ap (λ h → h (inr (inl refl))) (component≈ a≈ j₀)))
        ⨾  ap (classΓ j₀) (backwardsRetraction j₀ ((a₀ ⟨ j₀ ⟩) (inr (inl refl))))
        ⨾  respects ⦃ setQuotient ⦄ collapseRelation
        ⨾  sym (ap (classΓ j₀) (backwardsRetraction j₀ ((a₀ ⟨ j₀ ⟩) (inr (inr refl)))))
        ⨾  ap (λ z → classΓ j₀ (backwards j₀ z))
              (ap (λ h → h (inr (inr refl))) (component≈ a≈ j₀))
        where open FromAllSetQuotients (⌞ Γ ⟨ j₀ ⟩ ⌟) (CollapseRelation c₀ j₀)

      back : (k : type (Judgment 𝒥)) → ⌞ (Δ ⋊ₖ c₁) ⟨ k ⟩ ⌟ → ⌞ (Γ ⋊ₖ c₀) ⟨ k ⟩ ⌟
      back k = ⁄-rec ⦃ bset = level-proof ((Γ ⋊ₖ c₀) ⟨ k ⟩) ⦄
                     (λ y → classΓ k (backwards k y)) (resp k)
        where open FromAllSetQuotients (⌞ Δ ⟨ k ⟩ ⌟) (CollapseRelation c₁ k)

      isSection~ : (y : ⌞ (Δ ⋊ₖ c₁) ⟨ j' ⟩ ⌟)
                 → (map⋊ₖ α c₀ c₁ q ⟨ j' ⟩) (back j' y) ＝ y
      isSection~ =
        ⁄-elim-proposition
          (λ y → (map⋊ₖ α c₀ c₁ q ⟨ j' ⟩) (back j' y) ＝ y)
          (λ _ → ＝-isLevel ⦃ level-proof ((Δ ⋊ₖ c₁) ⟨ j' ⟩) ⦄)
          (λ y →
               ap (map⋊ₖ α c₀ c₁ q ⟨ j' ⟩)
                  (⁄-rec-β ⦃ bset = level-proof ((Γ ⋊ₖ c₀) ⟨ j' ⟩) ⦄
                           (λ z → classΓ j' (backwards j' z)) (resp j') y)
            ⨾  map⋊ₖ-class α c₀ c₁ q j' (backwards j' y)
            ⨾  ap (classΔ j') (backwardsSection j' y))
        where
          open FromAllSetQuotients (⌞ Δ ⟨ j' ⟩ ⌟) (CollapseRelation c₁ j')
          open FromAllSetQuotients (⌞ Γ ⟨ j' ⟩ ⌟) (CollapseRelation c₀ j')

      isRetraction~ : (x : ⌞ (Γ ⋊ₖ c₀) ⟨ j' ⟩ ⌟)
                    → back j' ((map⋊ₖ α c₀ c₁ q ⟨ j' ⟩) x) ＝ x
      isRetraction~ =
        ⁄-elim-proposition
          (λ x → back j' ((map⋊ₖ α c₀ c₁ q ⟨ j' ⟩) x) ＝ x)
          (λ _ → ＝-isLevel ⦃ level-proof ((Γ ⋊ₖ c₀) ⟨ j' ⟩) ⦄)
          (λ x →
               ap (back j') (map⋊ₖ-class α c₀ c₁ q j' x)
            ⨾  ⁄-rec-β ⦃ bset = level-proof ((Γ ⋊ₖ c₀) ⟨ j' ⟩) ⦄
                       (λ z → classΓ j' (backwards j' z)) (resp j') ((α ⟨ j' ⟩) x)
            ⨾  ap (classΓ j') (backwardsRetraction j' x))
        where
          open FromAllSetQuotients (⌞ Γ ⟨ j' ⟩ ⌟) (CollapseRelation c₀ j')
          open FromAllSetQuotients (⌞ Δ ⟨ j' ⟩ ⌟) (CollapseRelation c₁ j')


module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a i j : Level} {𝒥 : DependentSortVocabulary o a}
  {Γ : Context 𝒥 i} {Δ : Context 𝒥 j}
  (w : ContextEquivalence Γ Δ) where

  private
    α : Γ ⇒ Δ
    α = ContextEquivalence.morphism w

  map⋊-isEquivalence : (E₀ : ExtensionOrCollapse Γ) (E₁ : ExtensionOrCollapse Δ)
                       (q : mapExtensionOrCollapse α E₀ ≈ E₁)
                       (j' : type (Judgment 𝒥))
                     → isEquivalence (map⋊ α E₀ E₁ q ⟨ j' ⟩)
  map⋊-isEquivalence (extend e₀) (extend e₁) (extendEq p) j' =
    map⋊ₑ-isEquivalence w e₀ e₁ p j'
  map⋊-isEquivalence (collapse c₀) (collapse c₁) (collapseEq p) j' =
    map⋊ₖ-isEquivalence w c₀ c₁ p j'


module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a i j k : Level} {𝒥 : DependentSortVocabulary o a}
  {Γ : Context 𝒥 i} {Δ : Context 𝒥 j} {Θ : Context 𝒥 k}
  (w : ContextEquivalence Γ Δ) where

  private
    T : Γ ⇒ Δ
    T = ContextEquivalence.morphism w

  precomposeContext-isEquivalence : isEquivalence (λ (g : Δ ⇒ Θ) → g ∙ T)
  precomposeContext-isEquivalence =
    makeIsEquivalence
      (record { sectionBack = λ h → h ∙ inverseContextMorphism w
              ; isSection = isSection~ })
      (record { retractionBack = λ h → h ∙ inverseContextMorphism w
              ; isRetraction = isRetraction~ })
    where
      isSection~ : (h : Γ ⇒ Θ) → (h ∙ inverseContextMorphism w) ∙ T ＝ h
      isSection~ h =
        eq (record { component≈ = λ j' → funExt (λ z →
             ap (h ⟨ j' ⟩) (backwardsRetraction w j' z)) })

      isRetraction~ : (g : Δ ⇒ Θ) → (g ∙ T) ∙ inverseContextMorphism w ＝ g
      isRetraction~ g =
        eq (record { component≈ = λ j' → funExt (λ z →
             ap (g ⟨ j' ⟩) (backwardsSection w j' z)) })


