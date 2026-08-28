module SequentStructureMorphism where

open import Prelude
open import Axioms
open import Homotopy.SetQuotient
open import Syntax.Addable
open import Syntax.Arrowable
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
open import ContextWithTerms
open import Sequent
open import SequentStructure


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
  {𝒥 : DependentSortVocabulary o a}
  (sd : SequentStructure 𝒥 so₀ sa₀ i₀)
  (sc : SequentStructure 𝒥 so₁ sa₁ i₁)
  : Type (o ⊔ a ⊔ so₀ ⊔ sa₀ ⊔ lsuc i₀ ⊔ so₁ ⊔ sa₁ ⊔ lsuc i₁ ) where
  constructor mkSequentStructureMorphism
  field
    onDependencies : Semifunctor (SequentStructure.dependency sd) (SequentStructure.dependency sc)
    dependenciesEquivalence : (x : Ob (SequentStructure.dependency sd))
                            → isEquivalence (mapDependencies onDependencies x)
    component : (x : Ob (SequentStructure.dependency sd))
              → SequentEquivalence (SequentStructure.sequent sd ⟨ x ⟩) (SequentStructure.sequent sc ⟨ onDependencies ⟨ x ⟩ ⟩)
    natural : {x y : Ob (SequentStructure.dependency sd)} (f : Hom (SequentStructure.dependency sd) x y)
            → toSequentMorphism (component x) ∙ SequentStructure.sequent sd ⟨ f ⟩
            ＝ SequentStructure.sequent sc ⟨ onDependencies ⟨ f ⟩ ⟩ ∙ toSequentMorphism (component y)

instance
  sequentStructuresAreArrowable : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
                                → {o a : Level} {𝒥 : DependentSortVocabulary o a}
                                → Arrowable (Level × Level × Level) Level
                                    (λ (so , sa , i) → SequentStructure 𝒥 so sa i)
                                    (λ k → Type k)
                                    (λ (so₀ , sa₀ , i₀) (so₁ , sa₁ , i₁)
                                       → o ⊔ a ⊔ so₀ ⊔ sa₀ ⊔ lsuc i₀ ⊔ so₁ ⊔ sa₁ ⊔ lsuc i₁)
  sequentStructuresAreArrowable .Arrowable.arrow = SequentStructureMorphism


-- =============== Adding the empty context ===============

addEmptyBaseContext : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
                    → {o a so₀ sa₀ i₀ so₁ sa₁ i₁ : Level}
                      {𝒥 : DependentSortVocabulary o a}
                      {sd : SequentStructure 𝒥 so₀ sa₀ i₀}
                      {sc : SequentStructure 𝒥 so₁ sa₁ i₁}
                    → sd ⇒ sc
                    → emptyContextWithTerms 𝒥 so₀ sa₀ i₀ ⧺ sd ⇒ sc
addEmptyBaseContext {so₀ = so₀} {sa₀ = sa₀} {i₀ = i₀} {𝒥 = 𝒥} {sd = sd} {sc = sc} φ =
  record
    { onDependencies = onDependencies
    ; dependenciesEquivalence = dependenciesEquivalence
    ; component = component
    ; natural = λ { {inr x} {inr y} f → natural f } }
  where
    𝒟 = SequentStructure.dependency sd
    𝒢 = SequentStructure.sequent sd
    ℰ = SequentStructure.dependency sc
    ℋ = SequentStructure.sequent sc

    source : SequentStructure 𝒥 _ _ i₀
    source = emptyContextWithTerms 𝒥 so₀ sa₀ i₀ ⧺ sd

    onDependencies : Semifunctor (SequentStructure.dependency source) ℰ
    onDependencies =
      record
        { onObjects = onObjects
        ; semifunctorial = record
            { mappable = record { map = λ {x} {y} → onMorphisms {x} {y} }
            ; preservesComposition = record
                { preserves-composition = λ { {inr x} {inr y} {inr z} g h →
                    PreservesComposition.preserves-composition pres g h } } } }
      where
        open Semicategory.Reasoning 𝒟
        open Semicategory.Reasoning ℰ
        open Semifunctor.Reasoning (SequentStructureMorphism.onDependencies φ)
          renaming (preservesCompositionₛ to pres)

        onObjects : Ob (SequentStructure.dependency source) → Ob ℰ
        onObjects (inr x) = SequentStructureMorphism.onDependencies φ ⟨ x ⟩

        onMorphisms : {x y : Ob (SequentStructure.dependency source)}
                    → Hom (SequentStructure.dependency source) x y
                    → Hom ℰ (onObjects x) (onObjects y)
        onMorphisms {inr x} {inr y} f = SequentStructureMorphism.onDependencies φ ⟨ f ⟩

    dependenciesEquivalence : (x : Ob (SequentStructure.dependency source))
                            → isEquivalence (mapDependencies onDependencies x)
    dependenciesEquivalence (inr x) =
      record
        { section = record
            { sectionBack = inject ∘ sectionBack (section w)
            ; isSection = isSection (section w) }
        ; retraction = record
            { retractionBack = inject ∘ retractionBack (retraction w)
            ; isRetraction = isRetraction~ } }
      where
        w = SequentStructureMorphism.dependenciesEquivalence φ x

        inject : dependenciesOf 𝒟 x → dependenciesOf (SequentStructure.dependency source) (inr x)
        inject (y , f) = inr y , f

        isRetraction~ : (d : dependenciesOf (SequentStructure.dependency source) (inr x))
                      → inject (retractionBack (retraction w) (mapDependencies onDependencies (inr x) d)) ＝ d
        isRetraction~ (inr y , f) = ap inject (isRetraction (retraction w) (y , f))

    component : (x : Ob (SequentStructure.dependency source))
              → SequentEquivalence (SequentStructure.sequent source ⟨ x ⟩)
                                   (ℋ ⟨ onDependencies ⟨ x ⟩ ⟩)
    component (inr x) =
      addEmptyContextToSequentEquivalence (𝒢 ⟨ x ⟩) ⨾ SequentStructureMorphism.component φ x

    natural : {x y : Ob 𝒟} (f : Hom 𝒟 x y)
            → toSequentMorphism (component (inr x))
              ∙ addContextToSequentMorphism (emptyContext 𝒥 i₀) (𝒢 ⟨ f ⟩)
            ＝ ℋ ⟨ SequentStructureMorphism.onDependencies φ ⟨ f ⟩ ⟩
              ∙ toSequentMorphism (component (inr y))
    natural {x} {y} f =
      begin
        (Φx ∙ Ex) ∙ C  ⟪ sym (∙-associative {f = C} {g = Ex} {h = Φx}) ⟫
        Φx ∙ (Ex ∙ C)  ⟪ ap (Φx ∙_) (addEmptyContextToSequentEquivalence-natural {k = i₀} (𝒢 ⟨ f ⟩)) ⟫
        Φx ∙ (G ∙ Ey)  ⟪ ∙-associative {f = Ey} {g = G} {h = Φx} ⟫
        (Φx ∙ G) ∙ Ey  ⟪ ap (_∙ Ey) (SequentStructureMorphism.natural φ f) ⟫
        (S ∙ Φy) ∙ Ey  ⟪ sym (∙-associative {f = Ey} {g = Φy} {h = S}) ⟫
        S ∙ (Φy ∙ Ey)  ∎
      where
        Φx = toSequentMorphism (SequentStructureMorphism.component φ x)
        Φy = toSequentMorphism (SequentStructureMorphism.component φ y)
        Ex = toSequentMorphism (addEmptyContextToSequentEquivalence {k = i₀} (𝒢 ⟨ x ⟩))
        Ey = toSequentMorphism (addEmptyContextToSequentEquivalence {k = i₀} (𝒢 ⟨ y ⟩))
        G  = 𝒢 ⟨ f ⟩
        C  = addContextToSequentMorphism (emptyContext 𝒥 i₀) (𝒢 ⟨ f ⟩)
        S  = ℋ ⟨ SequentStructureMorphism.onDependencies φ ⟨ f ⟩ ⟩
