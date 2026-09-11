module Context.Extension where

open import Prelude hiding (＝-in)
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

-- ============== Yoneda contexts ==============

𝒴 : ⦃ _ : FunExt ⦄ {o a : Level} {𝒥 : DependentSortVocabulary o a}
  → (j : type (Judgment 𝒥)) → Context 𝒥 a
𝒴 {𝒥 = 𝒥} j =
  record { semifunctor = record
           { onObjects = JudgmentDependency 𝒥 j
           ; semifunctorial = record
               { mappable = record { map = λ f g → f ∙ g }
               ; preservesComposition = record
                   { preserves-composition = preservesCompositionPath } } } }
  where
  open Semicategory.Reasoning (semicategory 𝒥)

  opaque
    preservesCompositionPath : {j₁ j₂ j₃ : type (Judgment 𝒥)}
                               (f : type (JudgmentDependency 𝒥 j₁ j₂)) (g : type (JudgmentDependency 𝒥 j₂ j₃))
                             → (λ (h : type (JudgmentDependency 𝒥 j j₁)) → (g ∙ f) ∙ h)
                               ＝ (λ h → g ∙ (f ∙ h))
    preservesCompositionPath f g = funExt (λ h → sym ⨾-associative)

𝒴⁺⁺ : ⦃ _ : FunExt ⦄ {o a : Level} {𝒥 : DependentSortVocabulary o a}
    → (j : type (Judgment 𝒥)) → Context 𝒥 (o ⊔ a)
𝒴⁺⁺ {o} {a} {𝒥} j =
  record { semifunctor = record
           { onObjects = onObjects
           ; semifunctorial = record
               { mappable = record { map = onMorphisms }
               ; preservesComposition = record
                   { preserves-composition = preservesCompositionPath } } } }
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

  opaque
    preservesCompositionPath : ∀ {j₁ j₂ j₃} (f : type (JudgmentDependency 𝒥 j₁ j₂)) (g : type (JudgmentDependency 𝒥 j₂ j₃))
                             → onMorphisms (g ∙ f) ＝ onMorphisms g ∘ onMorphisms f
    preservesCompositionPath f g = funExt (preservesComposition~ f g)


-- =============== Context extension and collapse ==============

record Extension
  ⦃ _ : FunExt ⦄
  {o a i : Level}
  {𝒥 : DependentSortVocabulary o a}
  (Γ : Context 𝒥 i)
  : Type (o ⊔ a ⊔ i) where
  constructor mkExtension
  field
    judgmentForm : type (Judgment 𝒥)
    arguments : 𝒴 judgmentForm ⇒ Γ

record ExtensionEquality
  ⦃ _ : FunExt ⦄
  {o a i : Level}
  {𝒥 : DependentSortVocabulary o a}
  {Γ : Context 𝒥 i}
  (e₀ e₁ : Extension Γ)
  : Type (o ⊔ a ⊔ i) where
  constructor mkExtensionEquality
  field
    judgmentFormEq : Extension.judgmentForm e₀ ＝ Extension.judgmentForm e₁
    argumentsEq : tr (λ j → 𝒴 j ⇒ Γ) judgmentFormEq (Extension.arguments e₀) ≈ Extension.arguments e₁

instance
    ExtensionEquality-isSamey : ⦃ _ : FunExt ⦄ {o a i : Level} {𝒥 : DependentSortVocabulary o a} {Γ : Context 𝒥 i}
                              → Samey 𝟙₀ (λ _ → Extension Γ)
    ExtensionEquality-isSamey = record { samey = ExtensionEquality }

record Collapse
  ⦃ _ : FunExt ⦄
  {o a i : Level}
  {𝒥 : DependentSortVocabulary o a}
  (Γ : Context 𝒥 i)
  : Type (o ⊔ a ⊔ i) where
  constructor mkCollapse
  field
    judgmentForm : type (Judgment 𝒥)
    arguments : 𝒴⁺⁺ judgmentForm ⇒ Γ

record CollapseEquality
  ⦃ _ : FunExt ⦄
  {o a i : Level}
  {𝒥 : DependentSortVocabulary o a}
  {Γ : Context 𝒥 i}
  (c₀ c₁ : Collapse Γ)
  : Type (o ⊔ a ⊔ i) where
  constructor mkCollapseEquality
  field
    judgmentFormEq : Collapse.judgmentForm c₀ ＝ Collapse.judgmentForm c₁
    argumentsEq : tr (λ j → 𝒴⁺⁺ j ⇒ Γ) judgmentFormEq (Collapse.arguments c₀) ≈ Collapse.arguments c₁

instance
    CollapseEquality-isSamey : ⦃ _ : FunExt ⦄ {o a i : Level} {𝒥 : DependentSortVocabulary o a} {Γ : Context 𝒥 i}
                              → Samey 𝟙₀ (λ _ → Collapse Γ)
    CollapseEquality-isSamey = record { samey = CollapseEquality }

data ExtensionOrCollapse
  ⦃ _ : FunExt ⦄
  {o a i : Level}
  {𝒥 : DependentSortVocabulary o a}
  (Γ : Context 𝒥 i)
  : Type (o ⊔ a ⊔ i) where
  extend : Extension Γ → ExtensionOrCollapse Γ
  collapse : Collapse Γ → ExtensionOrCollapse Γ
open ExtensionOrCollapse

data ExtensionOrCollapseEquality
  ⦃ _ : FunExt ⦄
  {o a i : Level}
  {𝒥 : DependentSortVocabulary o a}
  {Γ : Context 𝒥 i}
  : ExtensionOrCollapse Γ → ExtensionOrCollapse Γ → Type (o ⊔ a ⊔ i) where
  extendEq : {e₀ e₁ : Extension Γ} → e₀ ≈ e₁ → ExtensionOrCollapseEquality (extend e₀) (extend e₁)
  collapseEq : {c₀ c₁ : Collapse Γ} → c₀ ≈ c₁ → ExtensionOrCollapseEquality (collapse c₀) (collapse c₁)
open ExtensionOrCollapseEquality

instance
    ExtensionOrCollapseEquality-isSamey : ⦃ _ : FunExt ⦄ {o a i : Level} {𝒥 : DependentSortVocabulary o a} {Γ : Context 𝒥 i}
                              → Samey 𝟙₀ (λ _ → ExtensionOrCollapse Γ)
    ExtensionOrCollapseEquality-isSamey = record { samey = ExtensionOrCollapseEquality }

module _ ⦃ _ : FunExt ⦄
  {o a i : Level} {𝒥 : DependentSortVocabulary o a} {Γ : Context 𝒥 i} where

  extensionRefl≈ : (e : Extension Γ) → e ≈ e
  extensionRefl≈ e = mkExtensionEquality refl (refl≈ ⦃ equalityContextMorphism ⦄)

  collapseRefl≈ : (c : Collapse Γ) → c ≈ c
  collapseRefl≈ c = mkCollapseEquality refl (refl≈ ⦃ equalityContextMorphism ⦄)

  extensionOrCollapseRefl≈ : (E : ExtensionOrCollapse Γ) → E ≈ E
  extensionOrCollapseRefl≈ (extend e) = extendEq (extensionRefl≈ e)
  extensionOrCollapseRefl≈ (collapse c) = collapseEq (collapseRefl≈ c)

  extension≈→＝ : {e₀ e₁ : Extension Γ} → e₀ ≈ e₁ → e₀ ＝ e₁
  extension≈→＝ {mkExtension j α} {mkExtension _ β} (mkExtensionEquality refl q) =
    ap (mkExtension j) (eq q)

  collapse≈→＝ : {c₀ c₁ : Collapse Γ} → c₀ ≈ c₁ → c₀ ＝ c₁
  collapse≈→＝ {mkCollapse j α} {mkCollapse _ β} (mkCollapseEquality refl q) =
    ap (mkCollapse j) (eq q)

  extensionOrCollapse≈→＝ : {E₀ E₁ : ExtensionOrCollapse Γ} → E₀ ≈ E₁ → E₀ ＝ E₁
  extensionOrCollapse≈→＝ (extendEq q) = ap extend (extension≈→＝ q)
  extensionOrCollapse≈→＝ (collapseEq q) = ap collapse (collapse≈→＝ q)

  private
    extensionStep : {j : type (Judgment 𝒥)} {α β : 𝒴 j ⇒ Γ} (r : α ＝ β)
                  → tr (ExtensionEquality (mkExtension j α)) (ap (mkExtension j) r)
                       (extensionRefl≈ (mkExtension j α))
                    ＝ mkExtensionEquality refl (observe ⦃ equalityContextMorphism ⦄ r)
    extensionStep refl = refl

    collapseStep : {j : type (Judgment 𝒥)} {α β : 𝒴⁺⁺ j ⇒ Γ} (r : α ＝ β)
                 → tr (CollapseEquality (mkCollapse j α)) (ap (mkCollapse j) r)
                      (collapseRefl≈ (mkCollapse j α))
                   ＝ mkCollapseEquality refl (observe ⦃ equalityContextMorphism ⦄ r)
    collapseStep refl = refl

    extendStep : {e₀ e₁ : Extension Γ} (r : e₀ ＝ e₁)
               → tr (ExtensionOrCollapseEquality (extend e₀)) (ap extend r)
                    (extensionOrCollapseRefl≈ (extend e₀))
                 ＝ extendEq (tr (ExtensionEquality e₀) r (extensionRefl≈ e₀))
    extendStep refl = refl

    collapseStepEOC : {c₀ c₁ : Collapse Γ} (r : c₀ ＝ c₁)
                    → tr (ExtensionOrCollapseEquality (collapse c₀)) (ap collapse r)
                         (extensionOrCollapseRefl≈ (collapse c₀))
                      ＝ collapseEq (tr (CollapseEquality c₀) r (collapseRefl≈ c₀))
    collapseStepEOC refl = refl

  extensionSection : {e₀ e₁ : Extension Γ} (w : e₀ ≈ e₁)
                   → tr (ExtensionEquality e₀) (extension≈→＝ w) (extensionRefl≈ e₀) ＝ w
  extensionSection {mkExtension j α} {mkExtension _ β} (mkExtensionEquality refl q) =
    extensionStep (eq q) ⨾ ap (mkExtensionEquality refl) (observe-eq ⦃ equalityContextMorphism ⦄ q)

  collapseSection : {c₀ c₁ : Collapse Γ} (w : c₀ ≈ c₁)
                  → tr (CollapseEquality c₀) (collapse≈→＝ w) (collapseRefl≈ c₀) ＝ w
  collapseSection {mkCollapse j α} {mkCollapse _ β} (mkCollapseEquality refl q) =
    collapseStep (eq q) ⨾ ap (mkCollapseEquality refl) (observe-eq ⦃ equalityContextMorphism ⦄ q)

  extensionOrCollapseSection : {E₀ E₁ : ExtensionOrCollapse Γ} (w : E₀ ≈ E₁)
                             → tr (ExtensionOrCollapseEquality E₀) (extensionOrCollapse≈→＝ w)
                                  (extensionOrCollapseRefl≈ E₀)
                               ＝ w
  extensionOrCollapseSection (extendEq q) =
    extendStep (extension≈→＝ q) ⨾ ap extendEq (extensionSection q)
  extensionOrCollapseSection (collapseEq q) =
    collapseStepEOC (collapse≈→＝ q) ⨾ ap collapseEq (collapseSection q)

  instance
    extension-hasEquality : Equality 𝟙₀ (λ _ → Extension Γ)
    extension-hasEquality =
      record { characterisation =
                 decode-＝ (ExtensionEquality {Γ = Γ}) extensionRefl≈
                           extension≈→＝ extensionSection }

    collapse-hasEquality : Equality 𝟙₀ (λ _ → Collapse Γ)
    collapse-hasEquality =
      record { characterisation =
                 decode-＝ (CollapseEquality {Γ = Γ}) collapseRefl≈
                           collapse≈→＝ collapseSection }

    extensionOrCollapse-hasEquality : Equality 𝟙₀ (λ _ → ExtensionOrCollapse Γ)
    extensionOrCollapse-hasEquality =
      record { characterisation =
                 decode-＝ (ExtensionOrCollapseEquality {Γ = Γ}) extensionOrCollapseRefl≈
                           extensionOrCollapse≈→＝ extensionOrCollapseSection }


module _ ⦃ _ : FunExt ⦄
  {o a i j : Level}
  {𝒥 : DependentSortVocabulary o a}
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
    → {o a i : Level} {𝒥 : DependentSortVocabulary o a}
    → (Γ : Context 𝒥 i) → Extension Γ → Context 𝒥 (o ⊔ i)
_⋊ₑ_ {o} {a} {i} {𝒥} Γ ext =
  record { semifunctor = record
             { onObjects = onObjects
             ; semifunctorial = record
                 { mappable = record { map = onMorphisms }
                 ; preservesComposition = record
                     { preserves-composition = preservesCompositionPath } } } }
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

    opaque
      preservesCompositionPath : ∀ {j₀ j₁ j₂} (f : type (JudgmentDependency 𝒥 j₀ j₁)) (g : type (JudgmentDependency 𝒥 j₁ j₂))
                               → onMorphisms (g ∙ f) ＝ onMorphisms g ∘ onMorphisms f
      preservesCompositionPath f g = funExt (preservesComposition~ f g)

ι : ⦃ _ : FunExt ⦄
  → {o a i : Level} {𝒥 : DependentSortVocabulary o a}
  → {Γ : Context 𝒥 i} {ϵ : Extension Γ}
  → Γ ⇒ Γ ⋊ₑ ϵ
ι = record
      { component = λ j → inl
      ; natural = identity }

module _ ⦃ _ : FunExt ⦄ {o a : Level} {𝒥 : DependentSortVocabulary o a} where

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
      ; natural = naturalPath }
    where
      component : (j : type (Judgment 𝒥)) → ⌞ (𝒴⁺ (Extension.judgmentForm ϵ)) ⟨ j ⟩ ⌟ → ⌞ (Γ ⋊ₑ ϵ) ⟨ j ⟩ ⌟
      component j (inl x) = inl ((Extension.arguments ϵ ⟨ j ⟩) x)
      component j (inr refl) = inr refl

      natural~ : {j₀ j₁ : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀ j₁))
               → (Γ ⋊ₑ ϵ) ⟨ f ⟩ ∘ component j₀ ~ component j₁ ∘ (𝒴⁺ (Extension.judgmentForm ϵ)) ⟨ f ⟩
      natural~ f (inl x) = ap (λ h → inl (h x)) (ContextMorphism.natural (Extension.arguments ϵ) f)
      natural~ f (inr refl) = refl

      opaque
        naturalPath : {j₀ j₁ : type (Judgment 𝒥)} (f : type (JudgmentDependency 𝒥 j₀ j₁))
                    → (Γ ⋊ₑ ϵ) ⟨ f ⟩ ∘ component j₀ ＝ component j₁ ∘ (𝒴⁺ (Extension.judgmentForm ϵ)) ⟨ f ⟩
        naturalPath f = funExt (natural~ f)

data CollapseRelation
  ⦃ _ : FunExt ⦄
  {o a i : Level}
  {𝒥 : DependentSortVocabulary o a}
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
     → {o a i : Level} {𝒥 : DependentSortVocabulary o a}
     → (Γ : Context 𝒥 i) → Collapse Γ → Context 𝒥 (o ⊔ i)
_⋊ₖ_ {o} {a} {i} {𝒥} Γ col =
  record { semifunctor = record
             { onObjects = onObjects
             ; semifunctorial = record
                 { mappable = record { map = onMorphisms }
                 ; preservesComposition = record
                     { preserves-composition = preservesCompositionPath } } } }
  where
    open Semicategory.Reasoning (semicategory 𝒥)
    open Semifunctor.Reasoning (Context.semifunctor Γ)

    onObjects : type (Judgment 𝒥) → hSet (o ⊔ i)
    onObjects j = ((⌞ Γ ⟨ j ⟩ ⌟) ⁄ CollapseRelation col j) has-level fromInstance
    onMorphisms : ∀ {j₀ j₁} → type (JudgmentDependency 𝒥 j₀ j₁) → ⌞ onObjects j₀ ⌟ → ⌞ onObjects j₁ ⌟
    onMorphisms {j₀} {j₁} f = ⁄-rec ([_] ∘ (Γ ⟨ f ⟩)) respectsCollapseRelation
      where

        opaque
          respectsCollapseRelation : {x y : ⌞ Γ ⟨ j₀ ⟩ ⌟}
                                   → CollapseRelation col j₀ x y
                                   → [_] {R = CollapseRelation col j₁} ((Γ ⟨ f ⟩) x)
                                     ＝ [_] {R = CollapseRelation col j₁} ((Γ ⟨ f ⟩) y)
          respectsCollapseRelation collapseRelation =
            ap ([_] {R = CollapseRelation col j₁})
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
        open Semifunctor.Reasoning (Context.semifunctor Γ)
        open Semicategory.Reasoning (hSet-Semicategory i)

        set : ∀ q → isSet (onMorphisms (g ∙ f) q ＝ onMorphisms g (onMorphisms f q))
        set q = raise-level (pathLevel (onMorphisms (g ∙ f) q) (onMorphisms g (onMorphisms f q)))

        preserves : (x : ⌞ Γ ⟨ j₀ ⟩ ⌟) → onMorphisms (g ∙ f) ([ x ]) ＝ onMorphisms g (onMorphisms f ([ x ]))
        preserves x = ap (λ σ → [ σ x ]) (preserves-composition f g)

        resp : {x y : ⌞ Γ ⟨ j₀ ⟩ ⌟} (r : CollapseRelation col j₀ x y)
             → tr (λ x → onMorphisms (g ∙ f) x ＝ onMorphisms g (onMorphisms f x))
                  (respects r)
                  (preserves x)
               ＝ preserves y
        resp r = allEqual _ _

    opaque
      preservesCompositionPath : ∀ {j₀ j₁ j₂} (f : type (JudgmentDependency 𝒥 j₀ j₁)) (g : type (JudgmentDependency 𝒥 j₁ j₂))
                               → onMorphisms (g ∙ f) ＝ onMorphisms g ∘ onMorphisms f
      preservesCompositionPath f g = funExt (preservesComposition~ f g)

σ : ⦃ _ : FunExt ⦄
  → ⦃ _ : AllSetQuotients ⦄
  → {o a i : Level} {𝒥 : DependentSortVocabulary o a}
  → {Γ : Context 𝒥 i} {c : Collapse Γ}
  → Γ ⇒ Γ ⋊ₖ c
σ {𝒥 = 𝒥} {Γ = Γ} {c = c} = record
  { component = component
  ; natural = naturalPath }
  where
    component : ∀ j → ⌞ Γ ⟨ j ⟩ ⌟ → ⌞ (Γ ⋊ₖ c) ⟨ j ⟩ ⌟
    component j = [_]
    natural : ∀ {j₀ j₁} (f : type (JudgmentDependency 𝒥 j₀ j₁)) → (Γ ⋊ₖ c) ⟨ f ⟩ ∘ component j₀ ~ component j₁ ∘ Γ ⟨ f ⟩
    natural f x = refl

    opaque
      naturalPath : ∀ {j₀ j₁} (f : type (JudgmentDependency 𝒥 j₀ j₁))
                  → (Γ ⋊ₖ c) ⟨ f ⟩ ∘ component j₀ ＝ component j₁ ∘ Γ ⟨ f ⟩
      naturalPath f = funExt (natural f)

infix 20 _⋊_
_⋊_ : ⦃ _ : FunExt ⦄
    → ⦃ _ : AllSetQuotients ⦄
    → {o a i : Level} {𝒥 : DependentSortVocabulary o a}
    → (Γ : Context 𝒥 i) → ExtensionOrCollapse Γ → Context 𝒥 (o ⊔ i)
Γ ⋊ extend ext = Γ ⋊ₑ ext
Γ ⋊ collapse col = Γ ⋊ₖ col



-- ============== Extension and collapse equalities are propositions ==============

module _ ⦃ _ : FunExt ⦄
  {o a i : Level} {𝒥 : DependentSortVocabulary o a} {Γ : Context 𝒥 i} where

  extensionEquality-isProposition :
      {e₀ e₁ : Extension Γ} → isProposition (ExtensionEquality e₀ e₁)
  extensionEquality-isProposition {e₀} {e₁} =
    retract-level
      (λ q → ExtensionEquality.judgmentFormEq q , ExtensionEquality.argumentsEq q)
      (λ w → mkExtensionEquality (p₀ w) (p₁ w))
      (λ _ → refl)
      (∑-level (＝-isLevel ⦃ level-proof (Judgment 𝒥) ⦄)
               (λ _ → contextMorphismEquality-isProposition))

  collapseEquality-isProposition :
      {c₀ c₁ : Collapse Γ} → isProposition (CollapseEquality c₀ c₁)
  collapseEquality-isProposition {c₀} {c₁} =
    retract-level
      (λ q → CollapseEquality.judgmentFormEq q , CollapseEquality.argumentsEq q)
      (λ w → mkCollapseEquality (p₀ w) (p₁ w))
      (λ _ → refl)
      (∑-level (＝-isLevel ⦃ level-proof (Judgment 𝒥) ⦄)
               (λ _ → contextMorphismEquality-isProposition))

  extensionOrCollapseEquality-isProposition :
      {E₀ E₁ : ExtensionOrCollapse Γ} → isProposition (ExtensionOrCollapseEquality E₀ E₁)
  extensionOrCollapseEquality-isProposition {extend e₀} {extend e₁} =
    retract-level (λ { (extendEq q) → q }) extendEq (λ { (extendEq q) → refl })
      extensionEquality-isProposition
  extensionOrCollapseEquality-isProposition {collapse c₀} {collapse c₁} =
    retract-level (λ { (collapseEq q) → q }) collapseEq (λ { (collapseEq q) → refl })
      collapseEquality-isProposition
  extensionOrCollapseEquality-isProposition {extend e₀} {collapse c₁} =
    fromAllEqual (λ ())
  extensionOrCollapseEquality-isProposition {collapse c₀} {extend e₁} =
    fromAllEqual (λ ())


