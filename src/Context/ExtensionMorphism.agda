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
open import Algebra.Wild.Semicategory
open import Algebra.Wild.Semifunctor
open import Algebra.Wild.TruncatedTypeSemicategory
open import Homotopy.SetQuotient.Nominal
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
      ; natural = naturalPath }
    where
      component : (j' : type (Judgment 𝒥)) → ⌞ (Γ ⋊ₑ e₀) ⟨ j' ⟩ ⌟ → ⌞ (Δ ⋊ₑ e₁) ⟨ j' ⟩ ⌟
      component j' (inl x) = inl ((α ⟨ j' ⟩) x)
      component j' (inr p) = inr p

      natural~ : {j₀' j₁' : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀' j₁'))
               → (Δ ⋊ₑ e₁) ⟨ f ⟩ ∘ component j₀' ~ component j₁' ∘ (Γ ⋊ₑ e₀) ⟨ f ⟩
      natural~ f (inl x) = ap (λ h → inl (h x)) (ContextMorphism.natural α f)
      natural~ {j₁' = j₁'} f (inr refl) = ap (λ h → inl (h f)) (sym (component≈ a≈ j₁'))

      opaque
        naturalPath : {j₀' j₁' : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀' j₁'))
                    → (Δ ⋊ₑ e₁) ⟨ f ⟩ ∘ component j₀' ＝ component j₁' ∘ (Γ ⋊ₑ e₀) ⟨ f ⟩
        naturalPath f = funExt (natural~ f)

module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a i j : Level} {𝒥 : DependentSortVocabulary o a}
  {Γ : Context 𝒥 i} {Δ : Context 𝒥 j}
  (α : Γ ⇒ Δ) where

  map⋊ₖ : (c₀ : Collapse Γ) (c₁ : Collapse Δ)
        → mapCollapse α c₀ ≈ c₁ → Γ ⋊ₖ c₀ ⇒ Δ ⋊ₖ c₁
  map⋊ₖ c₀@(mkCollapse j₀ a₀) c₁@(mkCollapse .j₀ a₁) (mkCollapseEquality refl a≈) =
    record
      { component = component
      ; natural = naturalPath }
    where

      classΓ : (j' : type (Judgment 𝒥)) → ⌞ Γ ⟨ j' ⟩ ⌟ → ⌞ (Γ ⋊ₖ c₀) ⟨ j' ⟩ ⌟
      classΓ j' = [_]

      classΔ : (j' : type (Judgment 𝒥)) → ⌞ Δ ⟨ j' ⟩ ⌟ → ⌞ (Δ ⋊ₖ c₁) ⟨ j' ⟩ ⌟
      classΔ j' = [_]

      opaque
        resp : (j' : type (Judgment 𝒥)) {x y : ⌞ Γ ⟨ j' ⟩ ⌟}
             → CollapseRelation c₀ j' x y
             → classΔ j' ((α ⟨ j' ⟩) x) ＝ classΔ j' ((α ⟨ j' ⟩) y)
        resp j' collapseRelation =
             ap (λ h → classΔ j₀ (h (inr (inl refl)))) (component≈ a≈ j₀)
          ⨾  respects collapseRelation
          ⨾  sym (ap (λ h → classΔ j₀ (h (inr (inr refl)))) (component≈ a≈ j₀))

      component : (j' : type (Judgment 𝒥)) → ⌞ (Γ ⋊ₖ c₀) ⟨ j' ⟩ ⌟ → ⌞ (Δ ⋊ₖ c₁) ⟨ j' ⟩ ⌟
      component j' = ⁄-rec ⦃ bset = level-proof ((Δ ⋊ₖ c₁) ⟨ j' ⟩) ⦄
                           (classΔ j' ∘ (α ⟨ j' ⟩)) (resp j')

      natural~ : {j₀' j₁' : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀' j₁'))
               → (Δ ⋊ₖ c₁) ⟨ f ⟩ ∘ component j₀' ~ component j₁' ∘ (Γ ⋊ₖ c₀) ⟨ f ⟩
      natural~ {j₀'} {j₁'} f =
        ⁄-elim-proposition
          (λ q → ((Δ ⋊ₖ c₁) ⟨ f ⟩) (component j₀' q) ＝ component j₁' (((Γ ⋊ₖ c₀) ⟨ f ⟩) q))
          (λ _ → ＝-isLevel ⦃ level-proof ((Δ ⋊ₖ c₁) ⟨ j₁' ⟩) ⦄)
          pointwise
        where
          pointwise : (x : ⌞ Γ ⟨ j₀' ⟩ ⌟)
                    → ((Δ ⋊ₖ c₁) ⟨ f ⟩) (component j₀' (classΓ j₀' x))
                      ＝ component j₁' (((Γ ⋊ₖ c₀) ⟨ f ⟩) (classΓ j₀' x))
          pointwise x = ap (classΔ j₁') (ap (λ h → h x) (ContextMorphism.natural α f))

      opaque
        naturalPath : {j₀' j₁' : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀' j₁'))
                    → (Δ ⋊ₖ c₁) ⟨ f ⟩ ∘ component j₀' ＝ component j₁' ∘ (Γ ⋊ₖ c₀) ⟨ f ⟩
        naturalPath f = funExt (natural~ f)

  map⋊ : (e₀ : ExtensionOrCollapse Γ) (e₁ : ExtensionOrCollapse Δ)
       → mapExtensionOrCollapse α e₀ ≈ e₁ → Γ ⋊ e₀ ⇒ Δ ⋊ e₁
  map⋊ (extend e₀) (extend e₁) (extendEq q) = map⋊ₑ α e₀ e₁ q
  map⋊ (collapse c₀) (collapse c₁) (collapseEq q) = map⋊ₖ c₀ c₁ q


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
           ap ((β ⟨ j' ⟩) ∘_) (component≈ p j')
        ⨾  component≈ q j'

  mapCollapse-⨾ : (c₀ : Collapse Γ) (c₁ : Collapse Δ) (c₂ : Collapse Θ)
                → mapCollapse α c₀ ≈ c₁ → mapCollapse β c₁ ≈ c₂
                → mapCollapse (α ⨾ β) c₀ ≈ c₂
  mapCollapse-⨾ (mkCollapse j₀ a₀) (mkCollapse .j₀ a₁) (mkCollapse .j₀ a₂)
                (mkCollapseEquality refl p) (mkCollapseEquality refl q) =
    mkCollapseEquality refl (record { component≈ = component≈~ })
    where
      component≈~ : (j' : type (Judgment 𝒥)) → ((α ⨾ β) ∙ a₀) ⟨ j' ⟩ ＝ a₂ ⟨ j' ⟩
      component≈~ j' =
           ap ((β ⟨ j' ⟩) ∘_) (component≈ p j')
        ⨾  component≈ q j'

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
        ⁄-elim-proposition _ (λ _ → ＝-isLevel ⦃ level-proof ((Θ ⋊ₖ c₂) ⟨ j' ⟩) ⦄) (λ x → refl)


module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a i : Level} {𝒥 : DependentSortVocabulary o a} {Γ : Context 𝒥 i} where

  map⋊-identity-at : (E : ExtensionOrCollapse Γ) (j' : type (Judgment 𝒥))
                     (z : ⌞ (Γ ⋊ E) ⟨ j' ⟩ ⌟)
                   → (map⋊ identity E E (mapExtensionOrCollapse-identity E) ⟨ j' ⟩) z ＝ z
  map⋊-identity-at (extend (mkExtension j a)) j' (inl x) = refl
  map⋊-identity-at (extend (mkExtension j a)) j' (inr p) = refl
  map⋊-identity-at (collapse c@(mkCollapse j a)) j' =
    ⁄-elim-proposition
      (λ q → (map⋊ₖ identity c c (mapCollapse-identity c) ⟨ j' ⟩) q ＝ q)
      (λ _ → ＝-isLevel ⦃ level-proof ((Γ ⋊ₖ c) ⟨ j' ⟩) ⦄)
      (λ x → refl)

  map⋊-identity : (E : ExtensionOrCollapse Γ)
                → map⋊ identity E E (mapExtensionOrCollapse-identity E) ≈ identity
  map⋊-identity E =
    record { component≈ = λ j' → funExt (map⋊-identity-at E j') }


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
    record { component = backwards ; natural = naturalPath }
    where
      natural~ : {j₀ j₁ : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀ j₁))
               → Γ ⟨ f ⟩ ∘ backwards j₀ ~ backwards j₁ ∘ Δ ⟨ f ⟩
      natural~ {j₀} {j₁} f y =
           sym (backwardsRetraction j₁ ((Γ ⟨ f ⟩) (backwards j₀ y)))
        ⨾  ap (backwards j₁)
              (sym (ap (λ h → h (backwards j₀ y)) (ContextMorphism.natural α f)))
        ⨾  ap (λ z → backwards j₁ ((Δ ⟨ f ⟩) z)) (backwardsSection j₀ y)

      opaque
        naturalPath : {j₀ j₁ : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀ j₁))
                    → Γ ⟨ f ⟩ ∘ backwards j₀ ＝ backwards j₁ ∘ Δ ⟨ f ⟩
        naturalPath f = funExt (natural~ f)

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

      classΔ : (k : type (Judgment 𝒥)) → ⌞ Δ ⟨ k ⟩ ⌟ → ⌞ (Δ ⋊ₖ c₁) ⟨ k ⟩ ⌟
      classΔ k = [_]

      resp : (k : type (Judgment 𝒥)) {u v : ⌞ Δ ⟨ k ⟩ ⌟}
           → CollapseRelation c₁ k u v
           → classΓ k (backwards k u) ＝ classΓ k (backwards k v)
      resp _ collapseRelation =
           ap (λ z → classΓ j₀ (backwards j₀ z))
              (sym (ap (λ h → h (inr (inl refl))) (component≈ a≈ j₀)))
        ⨾  ap (classΓ j₀) (backwardsRetraction j₀ ((a₀ ⟨ j₀ ⟩) (inr (inl refl))))
        ⨾  respects collapseRelation
        ⨾  sym (ap (classΓ j₀) (backwardsRetraction j₀ ((a₀ ⟨ j₀ ⟩) (inr (inr refl)))))
        ⨾  ap (λ z → classΓ j₀ (backwards j₀ z))
              (ap (λ h → h (inr (inr refl))) (component≈ a≈ j₀))

      back : (k : type (Judgment 𝒥)) → ⌞ (Δ ⋊ₖ c₁) ⟨ k ⟩ ⌟ → ⌞ (Γ ⋊ₖ c₀) ⟨ k ⟩ ⌟
      back k = ⁄-rec ⦃ bset = level-proof ((Γ ⋊ₖ c₀) ⟨ k ⟩) ⦄
                     (λ y → classΓ k (backwards k y)) (resp k)

      isSection~ : (y : ⌞ (Δ ⋊ₖ c₁) ⟨ j' ⟩ ⌟)
                 → (map⋊ₖ α c₀ c₁ q ⟨ j' ⟩) (back j' y) ＝ y
      isSection~ =
        ⁄-elim-proposition
          (λ y → (map⋊ₖ α c₀ c₁ q ⟨ j' ⟩) (back j' y) ＝ y)
          (λ _ → ＝-isLevel ⦃ level-proof ((Δ ⋊ₖ c₁) ⟨ j' ⟩) ⦄)
          (λ y → ap (classΔ j') (backwardsSection j' y))
      isRetraction~ : (x : ⌞ (Γ ⋊ₖ c₀) ⟨ j' ⟩ ⌟)
                    → back j' ((map⋊ₖ α c₀ c₁ q ⟨ j' ⟩) x) ＝ x
      isRetraction~ =
        ⁄-elim-proposition
          (λ x → back j' ((map⋊ₖ α c₀ c₁ q ⟨ j' ⟩) x) ＝ x)
          (λ _ → ＝-isLevel ⦃ level-proof ((Γ ⋊ₖ c₀) ⟨ j' ⟩) ⦄)
          (λ x → ap (classΓ j') (backwardsRetraction j' x))

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


