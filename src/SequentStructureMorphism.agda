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


-- A sequent dependency morphism is a map of the dependency graphs
-- that respects the total number of dependencies for each sequent
record SequentDependencyMorphism
  ⦃ _ : FunExt ⦄
  ⦃ _ : AllSetQuotients ⦄
  {so₀ sa₀ so₁ sa₁ : Level}
  (s₀ : Semicategory so₀ sa₀)
  (s₁ : Semicategory so₁ sa₁)
  : Type (so₀ ⊔ sa₀ ⊔ so₁ ⊔ sa₁) where
  constructor mkSequentDependencyMorphism
  field
    onDependencies : Semifunctor s₀ s₁
    dependenciesEquivalence : (x : Ob s₀) → isEquivalence (mapDependencies onDependencies x)

instance
  appliableSequentDependencyMorphism-onObjects : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
                                               → {so₀ sa₀ so₁ sa₁ : Level}
                                               → {s₀ : Semicategory so₀ sa₀} {s₁ : Semicategory so₁ sa₁}
                                               → Appliable (SequentDependencyMorphism s₀ s₁) (Ob s₀) (λ _ _ → Ob s₁)
  appliableSequentDependencyMorphism-onObjects = record { function = λ F x → SequentDependencyMorphism.onDependencies F ⟨ x ⟩ }
  
  appliableSequentDependencyMorphism-onMorphisms : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
                                                 → {so₀ sa₀ so₁ sa₁ : Level}
                                                 → {s₀ : Semicategory so₀ sa₀} {s₁ : Semicategory so₁ sa₁}
                                                 → {x y : Ob s₀}
                                                 → Appliable (SequentDependencyMorphism s₀ s₁) (Hom s₀ x y) (λ F h → Hom s₁ (F ⟨ x ⟩) (F ⟨ y ⟩))
  appliableSequentDependencyMorphism-onMorphisms = record { function = λ F h → SequentDependencyMorphism.onDependencies F ⟨ h ⟩ }


record SequentStructureMorphism
  ⦃ _ : FunExt ⦄
  ⦃ _ : AllSetQuotients ⦄
  {o a so₀ sa₀ i₀ so₁ sa₁ i₁ : Level}
  {𝒥 : DependentSortVocabulary o a}
  (s₀ : SequentStructure 𝒥 so₀ sa₀ i₀)
  (s₁ : SequentStructure 𝒥 so₁ sa₁ i₁)
  : Type (o ⊔ a ⊔ so₀ ⊔ sa₀ ⊔ lsuc i₀ ⊔ so₁ ⊔ sa₁ ⊔ lsuc i₁ ) where
  constructor mkSequentStructureMorphism
  field
    dependencyMorphism : SequentDependencyMorphism (SequentStructure.dependency s₀) (SequentStructure.dependency s₁)
    sequentEquivalence : (x : Ob (SequentStructure.dependency s₀))
                       → SequentEquivalence (SequentStructure.sequent s₀ ⟨ x ⟩) (SequentStructure.sequent s₁ ⟨ dependencyMorphism ⟨ x ⟩ ⟩)
    natural : {x y : Ob (SequentStructure.dependency s₀)} (f : Hom (SequentStructure.dependency s₀) x y)
            → toSequentMorphism (sequentEquivalence x) ∙ SequentStructure.sequent s₀ ⟨ f ⟩
            ＝ SequentStructure.sequent s₁ ⟨ dependencyMorphism ⟨ f ⟩ ⟩ ∙ toSequentMorphism (sequentEquivalence y)

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
    { dependencyMorphism =
        record
          { onDependencies = onDependencies
          ; dependenciesEquivalence = dependenciesEquivalence }
    ; sequentEquivalence = sequentEquivalence
    ; natural = λ { {inr x} {inr y} f → natural f } }
  where
    𝒟 = SequentStructure.dependency sd
    𝒢 = SequentStructure.sequent sd
    ℰ = SequentStructure.dependency sc
    ℋ = SequentStructure.sequent sc

    Φ = SequentStructureMorphism.dependencyMorphism φ

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
        open Semifunctor.Reasoning (SequentDependencyMorphism.onDependencies Φ)
          renaming (preservesCompositionₛ to pres)

        onObjects : Ob (SequentStructure.dependency source) → Ob ℰ
        onObjects (inr x) = Φ ⟨ x ⟩

        onMorphisms : {x y : Ob (SequentStructure.dependency source)}
                    → Hom (SequentStructure.dependency source) x y
                    → Hom ℰ (onObjects x) (onObjects y)
        onMorphisms {inr x} {inr y} f = Φ ⟨ f ⟩

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
        w = SequentDependencyMorphism.dependenciesEquivalence Φ x

        inject : dependenciesOf 𝒟 x → dependenciesOf (SequentStructure.dependency source) (inr x)
        inject (y , f) = inr y , f

        isRetraction~ : (d : dependenciesOf (SequentStructure.dependency source) (inr x))
                      → inject (retractionBack (retraction w) (mapDependencies onDependencies (inr x) d)) ＝ d
        isRetraction~ (inr y , f) = ap inject (isRetraction (retraction w) (y , f))

    sequentEquivalence : (x : Ob (SequentStructure.dependency source))
                       → SequentEquivalence (SequentStructure.sequent source ⟨ x ⟩)
                                            (ℋ ⟨ onDependencies ⟨ x ⟩ ⟩)
    sequentEquivalence (inr x) =
      addEmptyContextToSequentEquivalence (𝒢 ⟨ x ⟩) ⨾ SequentStructureMorphism.sequentEquivalence φ x

    natural : {x y : Ob 𝒟} (f : Hom 𝒟 x y)
            → toSequentMorphism (sequentEquivalence (inr x))
              ∙ addContextToSequentMorphism (emptyContext 𝒥 i₀) (𝒢 ⟨ f ⟩)
            ＝ ℋ ⟨ Φ ⟨ f ⟩ ⟩
              ∙ toSequentMorphism (sequentEquivalence (inr y))
    natural {x} {y} f =
      begin
        toSequentMorphism (sequentEquivalence (inr x)) ∙ C  ⟪ ap (_∙ C) (toSequentMorphism-⨾ (Ex-equivalence) (Φ-equivalence x)) ⟫
        (Φx ∙ Ex) ∙ C                                       ⟪ sym (∙-associative {f = C} {g = Ex} {h = Φx}) ⟫
        Φx ∙ (Ex ∙ C)                                       ⟪ ap (Φx ∙_) (addEmptyContextToSequentEquivalence-natural {k = i₀} (𝒢 ⟨ f ⟩)) ⟫
        Φx ∙ (G ∙ Ey)                                       ⟪ ∙-associative {f = Ey} {g = G} {h = Φx} ⟫
        (Φx ∙ G) ∙ Ey                                       ⟪ ap (_∙ Ey) (SequentStructureMorphism.natural φ f) ⟫
        (S ∙ Φy) ∙ Ey                                       ⟪ sym (∙-associative {f = Ey} {g = Φy} {h = S}) ⟫
        S ∙ (Φy ∙ Ey)                                       ⟪ ap (S ∙_) (sym (toSequentMorphism-⨾ (Ey-equivalence) (Φ-equivalence y))) ⟫
        S ∙ toSequentMorphism (sequentEquivalence (inr y))  ∎
      where
        Φ-equivalence = SequentStructureMorphism.sequentEquivalence φ
        Ex-equivalence = addEmptyContextToSequentEquivalence {k = i₀} (𝒢 ⟨ x ⟩)
        Ey-equivalence = addEmptyContextToSequentEquivalence {k = i₀} (𝒢 ⟨ y ⟩)

        Φx = toSequentMorphism (Φ-equivalence x)
        Φy = toSequentMorphism (Φ-equivalence y)
        Ex = fromEmptyContext {k = i₀} (𝒢 ⟨ x ⟩)
        Ey = fromEmptyContext {k = i₀} (𝒢 ⟨ y ⟩)
        G  = 𝒢 ⟨ f ⟩
        C  = addContextToSequentMorphism (emptyContext 𝒥 i₀) (𝒢 ⟨ f ⟩)
        S  = ℋ ⟨ Φ ⟨ f ⟩ ⟩

