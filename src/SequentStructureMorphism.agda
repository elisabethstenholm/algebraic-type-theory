module SequentStructureMorphism where

open import Prelude
open import Axioms
open import Homotopy.SetQuotient.Nominal
open import Syntax.Addable
open import Syntax.Arrowable
open import Structure.Associativity
open import Structure.Composable
open import Structure.Identity
open import Structure.PreservesComposition
open import Structure.Reasoning
open import Structure.Symmetric
open import Homotopy.StructuredType
open import Algebra.Wild.Semicategory
open import Algebra.Wild.Semifunctor
open Semicategory
open import Homotopy.Equality
open import Homotopy.Fibre
open import Homotopy.Levels
open import Foundation.DependentPair.Equivalence
open import Foundation.Sum.Equivalence

open import DependentSortVocabulary
open import Context
open import Context.Morphism
open import Context.Extension
open import Context.ExtensionMorphism
open import Sequent
open import Sequent.Morphism
open import SequentStructure
open import SequentStructure.Equality
open import SequentDependencyStructure
open import ContextWithTerms
open import Weakening.Sequent
open import Weakening.SequentStructure
open SequentDependencyStructure.SequentDependencyStructure
open ContextWithTerms.ContextWithTerms


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

weakenWithEmptyContext : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
                    → {o a so₀ sa₀ i₀ so₁ sa₁ i₁ : Level}
                      {𝒥 : DependentSortVocabulary o a}
                      {sd : SequentStructure 𝒥 so₀ sa₀ i₀}
                      {sc : SequentStructure 𝒥 so₁ sa₁ i₁}
                    → sd ⇒ sc
                    → emptyContextWithTerms 𝒥 so₀ sa₀ i₀ ⧺ sd ⇒ sc
weakenWithEmptyContext {so₀ = so₀} {sa₀ = sa₀} {i₀ = i₀} {𝒥 = 𝒥} {sd = sd} {sc = sc} φ =
  record
    { dependencyMorphism =
        record
          { onDependencies = onDependencies
          ; dependenciesEquivalence = dependenciesEquivalence }
    ; sequentEquivalence = sequentEquivalence
    ; natural = λ { {inr x} {inr y} f → naturalOpaque f } }
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
      weakenWithEmptySequentEquivalence (𝒢 ⟨ x ⟩) ⨾ SequentStructureMorphism.sequentEquivalence φ x

    natural : {x y : Ob 𝒟} (f : Hom 𝒟 x y)
            → toSequentMorphism (sequentEquivalence (inr x))
              ∙ weakenSequentMorphism (emptyContext 𝒥 i₀) (𝒢 ⟨ f ⟩)
            ＝ ℋ ⟨ Φ ⟨ f ⟩ ⟩
              ∙ toSequentMorphism (sequentEquivalence (inr y))
    natural {x} {y} f =
         ap (_∙ C) (toSequentMorphism-⨾ (Ex-equivalence) (Φ-equivalence x))
      ⨾  sym (∙-associative {f = C} {g = Ex} {h = Φx})
      ⨾  ap (Φx ∙_) (weakenWithEmptySequentEquivalence-natural {k = i₀} (𝒢 ⟨ f ⟩))
      ⨾  ∙-associative {f = Ey} {g = G} {h = Φx}
      ⨾  ap (_∙ Ey) (SequentStructureMorphism.natural φ f)
      ⨾  sym (∙-associative {f = Ey} {g = Φy} {h = S})
      ⨾  ap (S ∙_) (sym (toSequentMorphism-⨾ (Ey-equivalence) (Φ-equivalence y)))
      where
        Φ-equivalence = SequentStructureMorphism.sequentEquivalence φ
        Ex-equivalence = weakenWithEmptySequentEquivalence {k = i₀} (𝒢 ⟨ x ⟩)
        Ey-equivalence = weakenWithEmptySequentEquivalence {k = i₀} (𝒢 ⟨ y ⟩)

        Φx = toSequentMorphism (Φ-equivalence x)
        Φy = toSequentMorphism (Φ-equivalence y)
        Ex = fromEmptyContext {k = i₀} (𝒢 ⟨ x ⟩)
        Ey = fromEmptyContext {k = i₀} (𝒢 ⟨ y ⟩)
        G  = 𝒢 ⟨ f ⟩
        C  = weakenSequentMorphism (emptyContext 𝒥 i₀) (𝒢 ⟨ f ⟩)
        S  = ℋ ⟨ Φ ⟨ f ⟩ ⟩

    opaque
      naturalOpaque : {x y : Ob 𝒟} (f : Hom 𝒟 x y)
                    → toSequentMorphism (sequentEquivalence (inr x))
                      ∙ weakenSequentMorphism (emptyContext 𝒥 i₀) (𝒢 ⟨ f ⟩)
                    ＝ ℋ ⟨ Φ ⟨ f ⟩ ⟩
                      ∙ toSequentMorphism (sequentEquivalence (inr y))
      naturalOpaque f = natural f



-- =============== Composition of sequent structure morphisms ===============

module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a : Level} {𝒥 : DependentSortVocabulary o a} where

  sequentDependencyMorphism-⨾ :
      {so₀ sa₀ so₁ sa₁ so₂ sa₂ : Level}
      {d₀ : Semicategory so₀ sa₀} {d₁ : Semicategory so₁ sa₁} {d₂ : Semicategory so₂ sa₂}
    → SequentDependencyMorphism d₀ d₁ → SequentDependencyMorphism d₁ d₂
    → SequentDependencyMorphism d₀ d₂
  sequentDependencyMorphism-⨾ Φ Ψ =
    record
      { onDependencies = compose (SequentDependencyMorphism.onDependencies Φ)
                                 (SequentDependencyMorphism.onDependencies Ψ)
      ; dependenciesEquivalence = λ x →
          ≃→isEquivalence
            (  isEquivalence→≃ (SequentDependencyMorphism.dependenciesEquivalence Φ x)
            ⨾  isEquivalence→≃
                 (SequentDependencyMorphism.dependenciesEquivalence Ψ (Φ ⟨ x ⟩))) }

  sequentStructureMorphism-⨾ :
      {so₀ sa₀ i₀ so₁ sa₁ i₁ so₂ sa₂ i₂ : Level}
      {s₀ : SequentStructure 𝒥 so₀ sa₀ i₀}
      {s₁ : SequentStructure 𝒥 so₁ sa₁ i₁}
      {s₂ : SequentStructure 𝒥 so₂ sa₂ i₂}
    → SequentStructureMorphism s₀ s₁ → SequentStructureMorphism s₁ s₂
    → SequentStructureMorphism s₀ s₂
  sequentStructureMorphism-⨾ {s₀ = s₀} {s₁ = s₁} {s₂ = s₂} φ ψ =
    record
      { dependencyMorphism = dependencyMorphism
      ; sequentEquivalence = sequentEquivalence
      ; natural = λ {x} {y} f → naturalOpaque {x} {y} f }
    where
      𝒟 = SequentStructure.dependency s₀
      𝒢 = SequentStructure.sequent s₀
      ℋ = SequentStructure.sequent s₁
      ℐ = SequentStructure.sequent s₂

      Φ = SequentStructureMorphism.dependencyMorphism φ
      Ψ = SequentStructureMorphism.dependencyMorphism ψ

      seφ = SequentStructureMorphism.sequentEquivalence φ
      seψ = SequentStructureMorphism.sequentEquivalence ψ

      dependencyMorphism : SequentDependencyMorphism 𝒟 (SequentStructure.dependency s₂)
      dependencyMorphism = sequentDependencyMorphism-⨾ Φ Ψ

      sequentEquivalence : (x : Ob 𝒟)
                         → SequentEquivalence (𝒢 ⟨ x ⟩) (ℐ ⟨ dependencyMorphism ⟨ x ⟩ ⟩)
      sequentEquivalence x = seφ x ⨾ seψ (Φ ⟨ x ⟩)

      natural : {x y : Ob 𝒟} (f : Hom 𝒟 x y)
              → toSequentMorphism (sequentEquivalence x) ∙ 𝒢 ⟨ f ⟩
              ＝ ℐ ⟨ dependencyMorphism ⟨ f ⟩ ⟩ ∙ toSequentMorphism (sequentEquivalence y)
      natural {x} {y} f =
           ap (_∙ Gf) (toSequentMorphism-⨾ (seφ x) (seψ (Φ ⟨ x ⟩)))
        ⨾  sym (∙-associative {f = Gf} {g = Ax} {h = Bx})
        ⨾  ap (Bx ∙_) (SequentStructureMorphism.natural φ f)
        ⨾  ∙-associative {f = Ay} {g = Hf} {h = Bx}
        ⨾  ap (_∙ Ay) (SequentStructureMorphism.natural ψ (Φ ⟨ f ⟩))
        ⨾  sym (∙-associative {f = Ay} {g = By} {h = If})
        ⨾  ap (If ∙_) (sym (toSequentMorphism-⨾ (seφ y) (seψ (Φ ⟨ y ⟩))))
        where
          Ax = toSequentMorphism (seφ x)
          Ay = toSequentMorphism (seφ y)
          Bx = toSequentMorphism (seψ (Φ ⟨ x ⟩))
          By = toSequentMorphism (seψ (Φ ⟨ y ⟩))
          Gf = 𝒢 ⟨ f ⟩
          Hf = ℋ ⟨ Φ ⟨ f ⟩ ⟩
          If = ℐ ⟨ Ψ ⟨ Φ ⟨ f ⟩ ⟩ ⟩

      opaque
        naturalOpaque : {x y : Ob 𝒟} (f : Hom 𝒟 x y)
                      → toSequentMorphism (sequentEquivalence x) ∙ 𝒢 ⟨ f ⟩
                      ＝ ℐ ⟨ dependencyMorphism ⟨ f ⟩ ⟩ ∙ toSequentMorphism (sequentEquivalence y)
        naturalOpaque f = natural f



-- =============== Sequent structure morphisms from equalities ===============

module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a}
  {s₀ s₁ : SequentStructure 𝒥 so sa i} where

  equivToSSM : SequentStructureEquality s₀ s₁ → SequentStructureMorphism s₀ s₁
  equivToSSM w =
    record
      { dependencyMorphism = record
          { onDependencies = onDependencies
          ; dependenciesEquivalence = dependenciesEquivalence }
      ; sequentEquivalence = SequentStructureEquality.sequent≈ w
      ; natural = λ {x} {y} f → naturalPath {x} {y} f }
    where
      𝒟₀ = SequentStructure.dependency s₀
      𝒟₁ = SequentStructure.dependency s₁

      d≈ = SequentStructureEquality.dependency≈ w

      onDependencies : Semifunctor 𝒟₀ 𝒟₁
      onDependencies =
        record
          { onObjects = there (Semicategory-Equality.objects≈ d≈)
          ; semifunctorial = record
              { mappable = record { map = λ {x} {y} → there (Semicategory-Equality.hom≈ d≈ x y) }
              ; preservesComposition = record
                  { preserves-composition = λ {x} {y} {z} f g →
                      Semicategory-Equality.composition≈ d≈ x y z f g } } }

      dependenciesEquivalence : (x : Ob 𝒟₀)
                              → isEquivalence (mapDependencies onDependencies x)
      dependenciesEquivalence x =
        ~transfer-isEquivalence
          (equiv-∑ (Semicategory-Equality.objects≈ d≈) (λ y → Semicategory-Equality.hom≈ d≈ x y))
          pointwise
        where
          pointwise : there (equiv-∑ (Semicategory-Equality.objects≈ d≈) (λ y → Semicategory-Equality.hom≈ d≈ x y))
                      ~ mapDependencies onDependencies x
          pointwise (y , f) = refl

      opaque
        naturalPath : {x y : Ob 𝒟₀} (f : Hom 𝒟₀ x y)
                    → toSequentMorphism (SequentStructureEquality.sequent≈ w x)
                        ∙ SequentStructure.sequent s₀ ⟨ f ⟩
                      ＝ SequentStructure.sequent s₁ ⟨ onDependencies ⟨ f ⟩ ⟩
                        ∙ toSequentMorphism (SequentStructureEquality.sequent≈ w y)
        naturalPath f =
          eq ⦃ equalitySequentMorphism ⦄ (SequentStructureEquality.natural≈ w f)


