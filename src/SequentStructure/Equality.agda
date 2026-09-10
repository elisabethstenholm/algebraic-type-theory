module SequentStructure.Equality where

open import Prelude
open import Axioms
open import Algebra.Wild.Semicategory
open import Algebra.Wild.Semifunctor
open import Syntax.Opposable using (_ᵒᵖ)
open Semicategory
open import Algebra.Wild.TruncatedTypeSemicategory
open import Homotopy.Equality
open import Homotopy.Fibre
open import Homotopy.Levels
open import Homotopy.StructuredType
open import Homotopy.SetQuotient.Nominal
open import Structure.Composable
open import Structure.PreservesComposition
open import Structure.Symmetric
open import Foundation.Empty

open import DependentSortVocabulary
open import Context
open import Context.Morphism
open import Context.Extension
open import Context.ExtensionMorphism
open import Sequent
open import Sequent.Morphism
open import SequentStructure

-- ============= Equality of sequent structures =============


record SequentStructureEquality
  ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a}
  (s₀ s₁ : SequentStructure 𝒥 so sa i)
  : Type (o ⊔ a ⊔ so ⊔ sa ⊔ lsuc i) where
  constructor mkSequentStructureEquality
  field
    dependency≈ : SequentStructure.dependency s₀ ≈ SequentStructure.dependency s₁
    sequent≈ : (x : Ob (SequentStructure.dependency s₀))
              → SequentEquivalence
                  (SequentStructure.sequent s₀ ⟨ x ⟩)
                  (SequentStructure.sequent s₁ ⟨ there (Semicategory-Equality.objects≈ dependency≈) x ⟩)
    natural≈ : {x y : Ob (SequentStructure.dependency s₀)}
                (f : Hom (SequentStructure.dependency s₀) x y)
              → SequentMorphismEquality
                  (toSequentMorphism (sequent≈ x) ∙ (SequentStructure.sequent s₀ ⟨ f ⟩))
                  ((SequentStructure.sequent s₁ ⟨ there (Semicategory-Equality.hom≈ dependency≈ x y) f ⟩)
                    ∙ toSequentMorphism (sequent≈ y))
open SequentStructureEquality


module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a} where

  identitySequentStructureEquality :
      (s : SequentStructure 𝒥 so sa i) → SequentStructureEquality s s
  identitySequentStructureEquality s =
    record
      { dependency≈ = refl≈ ⦃ Semicategory-hasEquality ⦄
      ; sequent≈ = λ x → sequentEquivalence-identity
      ; natural≈ = natural~ }
    where
      ℱ = SequentStructure.sequent s

      natural~ : {x y : Ob (SequentStructure.dependency s)}
                 (f : Hom (SequentStructure.dependency s) x y)
               → SequentMorphismEquality
                   (toSequentMorphism (sequentEquivalence-identity {s = ℱ ⟨ x ⟩}) ∙ (ℱ ⟨ f ⟩))
                   ((ℱ ⟨ f ⟩) ∙ toSequentMorphism (sequentEquivalence-identity {s = ℱ ⟨ y ⟩}))
      natural~ {x} {y} f =
        mkSequentMorphismEquality (record { component≈ = λ j → funExt (pointwise j) })
        where
          pointwise : (j : type (Judgment 𝒥)) (z : _) → _ ＝ _
          pointwise j z =
               toSequentMorphism-identity-at {s = ℱ ⟨ x ⟩} j ((ℱ ⟨ f ⟩ ⟨ j ⟩) z)
            ⨾  sym (ap (ℱ ⟨ f ⟩ ⟨ j ⟩)
                       (toSequentMorphism-identity-at {s = ℱ ⟨ y ⟩} j z))

  private
    arrowFibre-Contractible :
        {𝒞 : Semicategory so sa}
        (ℱ : Semifunctor (𝒞 ᵒᵖ) (SequentSemicategory 𝒥 i))
        (ob𝒢 : Ob 𝒞 → Sequent 𝒥 i)
        (se : (x : Ob 𝒞) → SequentEquivalence (ℱ ⟨ x ⟩) (ob𝒢 x))
        {x y : Ob 𝒞} (f : Hom 𝒞 x y)
      → Contractible
          (∑[ mf ∶ SequentMorphism (ob𝒢 y) (ob𝒢 x) ]
             SequentMorphismEquality
               (toSequentMorphism (se x) ∙ (ℱ ⟨ f ⟩))
               (mf ∙ toSequentMorphism (se y)))
    arrowFibre-Contractible ℱ ob𝒢 se {x} {y} f =
      retract-Contractible toParts fromParts roundTrip
        (≃-Contractible fibre≃∑
           (equivalenceFibresAreContractible
              (isEquivalence→≃
                 (precompose-isEquivalence (toSequentMorphism (se y))
                                           (toSequentMorphism-isEquivalence (se y))))
              (toSequentMorphism (se x) ∙ (ℱ ⟨ f ⟩))))
      where
        toParts : (∑[ mf ∶ SequentMorphism (ob𝒢 y) (ob𝒢 x) ]
                     SequentMorphismEquality
                       (toSequentMorphism (se x) ∙ (ℱ ⟨ f ⟩))
                       (mf ∙ toSequentMorphism (se y)))
                → ∑[ mf ∶ SequentMorphism (ob𝒢 y) (ob𝒢 x) ]
                    (mf ∙ toSequentMorphism (se y)
                     ＝ toSequentMorphism (se x) ∙ (ℱ ⟨ f ⟩))
        toParts (mf , h) = mf , sym (eq h)

        fromParts : (∑[ mf ∶ SequentMorphism (ob𝒢 y) (ob𝒢 x) ]
                      (mf ∙ toSequentMorphism (se y)
                       ＝ toSequentMorphism (se x) ∙ (ℱ ⟨ f ⟩)))
                  → ∑[ mf ∶ SequentMorphism (ob𝒢 y) (ob𝒢 x) ]
                      SequentMorphismEquality
                        (toSequentMorphism (se x) ∙ (ℱ ⟨ f ⟩))
                        (mf ∙ toSequentMorphism (se y))
        fromParts (mf , p) = mf , observe (sym p)

        roundTrip : fromParts ∘ toParts ~ id
        roundTrip (mf , h) =
          ap (λ z → (mf , z))
             (allEqual ⦃ sequentMorphismEquality-isProposition ⦄ _ _)

    transportedMap :
        {𝒞 : Semicategory so sa}
        (ℱ : Semifunctor (𝒞 ᵒᵖ) (SequentSemicategory 𝒥 i))
        (ob𝒢 : Ob 𝒞 → Sequent 𝒥 i)
        (se : (x : Ob 𝒞) → SequentEquivalence (ℱ ⟨ x ⟩) (ob𝒢 x))
        {x y : Ob 𝒞} (f : Hom 𝒞 x y)
      → SequentMorphism (ob𝒢 y) (ob𝒢 x)
    transportedMap ℱ ob𝒢 se {x} {y} f =
      (toSequentMorphism (se x) ∙ (ℱ ⟨ f ⟩))
        ∙ inverseSequentMorphism (toSequentMorphism (se y))
                                 (toSequentMorphism-isEquivalence (se y))

    transportedMap-natural :
        {𝒞 : Semicategory so sa}
        (ℱ : Semifunctor (𝒞 ᵒᵖ) (SequentSemicategory 𝒥 i))
        (ob𝒢 : Ob 𝒞 → Sequent 𝒥 i)
        (se : (x : Ob 𝒞) → SequentEquivalence (ℱ ⟨ x ⟩) (ob𝒢 x))
        {x y : Ob 𝒞} (f : Hom 𝒞 x y)
      → SequentMorphismEquality
          (toSequentMorphism (se x) ∙ (ℱ ⟨ f ⟩))
          (transportedMap ℱ ob𝒢 se f ∙ toSequentMorphism (se y))
    transportedMap-natural ℱ ob𝒢 se {x} {y} f =
      mkSequentMorphismEquality
        (record { component≈ = λ j → funExt (λ z →
           sym (ap (λ v → (toSequentMorphism (se x) ⟨ j ⟩) ((ℱ ⟨ f ⟩ ⟨ j ⟩) v))
                   (backwardsRetraction
                      (sequentMorphismEquivalence (toSequentMorphism (se y))
                                                  (toSequentMorphism-isEquivalence (se y)))
                      j z))) })

    transportedSemifunctor :
        {𝒞 : Semicategory so sa}
        (ℱ : Semifunctor (𝒞 ᵒᵖ) (SequentSemicategory 𝒥 i))
        (ob𝒢 : Ob 𝒞 → Sequent 𝒥 i)
        (se : (x : Ob 𝒞) → SequentEquivalence (ℱ ⟨ x ⟩) (ob𝒢 x))
      → Semifunctor (𝒞 ᵒᵖ) (SequentSemicategory 𝒥 i)
    transportedSemifunctor {𝒞} ℱ ob𝒢 se =
      record
        { onObjects = ob𝒢
        ; semifunctorial =
            record
              { mappable = record { map = λ {A} {B} f → transportedMap ℱ ob𝒢 se f }
              ; preservesComposition =
                  record { preserves-composition = λ g h →
                    eq (mkSequentMorphismEquality
                          (record { component≈ = λ j → funExt (lawAt g h j) })) } } }
      where
        open Semicategory.Reasoning (𝒞 ᵒᵖ)
        open Semicategory.Reasoning (SequentSemicategory 𝒥 i)
        open Semifunctor.Reasoning ℱ renaming (preservesCompositionₛ to pres)

        bw : (x : Ob 𝒞) (j : type (Judgment 𝒥))
           → ⌞ extendedContext (ob𝒢 x) ⟨ j ⟩ ⌟ → ⌞ extendedContext (ℱ ⟨ x ⟩) ⟨ j ⟩ ⌟
        bw x j = backwards (sequentMorphismEquivalence (toSequentMorphism (se x))
                                                       (toSequentMorphism-isEquivalence (se x))) j

        lawAt : {A B E : Ob 𝒞} (g : Hom (𝒞 ᵒᵖ) A B) (h : Hom (𝒞 ᵒᵖ) B E)
                (j : type (Judgment 𝒥))
                (z : ⌞ extendedContext (ob𝒢 A) ⟨ j ⟩ ⌟)
              → (transportedMap ℱ ob𝒢 se (g ⨾ h) ⟨ j ⟩) z
                ＝ (toSequentMorphism (se E) ⟨ j ⟩)
                     ((ℱ ⟨ h ⟩ ⟨ j ⟩)
                       ((bw B j)
                         ((toSequentMorphism (se B) ⟨ j ⟩)
                           ((ℱ ⟨ g ⟩ ⟨ j ⟩) (bw A j z)))))
        lawAt {A} {B} {E} g h j z =
             ap (λ v → (toSequentMorphism (se E) ⟨ j ⟩)
                         ((SequentMorphism.sequentMorphism v ⟨ j ⟩) (bw A j z)))
                (PreservesComposition.preserves-composition pres g h)
          ⨾  ap (λ v → (toSequentMorphism (se E) ⟨ j ⟩) ((ℱ ⟨ h ⟩ ⟨ j ⟩) v))
                (sym (backwardsRetraction
                        (sequentMorphismEquivalence (toSequentMorphism (se B))
                                                    (toSequentMorphism-isEquivalence (se B)))
                        j ((ℱ ⟨ g ⟩ ⟨ j ⟩) (bw A j z))))

    mapNatAt-Contractible :
        {𝒞 : Semicategory so sa}
        (ℱ : Semifunctor (𝒞 ᵒᵖ) (SequentSemicategory 𝒥 i))
        (ob𝒢 : Ob 𝒞 → Sequent 𝒥 i)
        (se : (x : Ob 𝒞) → SequentEquivalence (ℱ ⟨ x ⟩) (ob𝒢 x))
        (x y : Ob 𝒞)
      → Contractible
          (∑[ mp ∶ ((f : Hom 𝒞 x y) → SequentMorphism (ob𝒢 y) (ob𝒢 x)) ]
             ((f : Hom 𝒞 x y)
               → SequentMorphismEquality
                   (toSequentMorphism (se x) ∙ (ℱ ⟨ f ⟩))
                   (mp f ∙ toSequentMorphism (se y))))
    mapNatAt-Contractible ℱ ob𝒢 se x y =
      Π-witness-Contractible
        (λ f mf → SequentMorphismEquality
                    (toSequentMorphism (se x) ∙ (ℱ ⟨ f ⟩))
                    (mf ∙ toSequentMorphism (se y)))
        (λ f → arrowFibre-Contractible ℱ ob𝒢 se {x} {y} f)

    mapNatFrom-Contractible :
        {𝒞 : Semicategory so sa}
        (ℱ : Semifunctor (𝒞 ᵒᵖ) (SequentSemicategory 𝒥 i))
        (ob𝒢 : Ob 𝒞 → Sequent 𝒥 i)
        (se : (x : Ob 𝒞) → SequentEquivalence (ℱ ⟨ x ⟩) (ob𝒢 x))
        (x : Ob 𝒞)
      → Contractible
          (∑[ mp ∶ ((y : Ob 𝒞) (f : Hom 𝒞 x y) → SequentMorphism (ob𝒢 y) (ob𝒢 x)) ]
             ((y : Ob 𝒞) (f : Hom 𝒞 x y)
               → SequentMorphismEquality
                   (toSequentMorphism (se x) ∙ (ℱ ⟨ f ⟩))
                   (mp y f ∙ toSequentMorphism (se y))))
    mapNatFrom-Contractible {𝒞} ℱ ob𝒢 se x =
      Π-witness-Contractible
        (λ y mp → (f : Hom 𝒞 x y)
                → SequentMorphismEquality
                    (toSequentMorphism (se x) ∙ (ℱ ⟨ f ⟩))
                    (mp f ∙ toSequentMorphism (se y)))
        (λ y → mapNatAt-Contractible ℱ ob𝒢 se x y)

    mapNat-Contractible :
        {𝒞 : Semicategory so sa}
        (ℱ : Semifunctor (𝒞 ᵒᵖ) (SequentSemicategory 𝒥 i))
        (ob𝒢 : Ob 𝒞 → Sequent 𝒥 i)
        (se : (x : Ob 𝒞) → SequentEquivalence (ℱ ⟨ x ⟩) (ob𝒢 x))
      → Contractible
          (∑[ mp ∶ ((x y : Ob 𝒞) (f : Hom 𝒞 x y) → SequentMorphism (ob𝒢 y) (ob𝒢 x)) ]
             ((x y : Ob 𝒞) (f : Hom 𝒞 x y)
               → SequentMorphismEquality
                   (toSequentMorphism (se x) ∙ (ℱ ⟨ f ⟩))
                   (mp x y f ∙ toSequentMorphism (se y))))
    mapNat-Contractible {𝒞} ℱ ob𝒢 se =
      Π-witness-Contractible
        (λ x mp → (y : Ob 𝒞) (f : Hom 𝒞 x y)
                → SequentMorphismEquality
                    (toSequentMorphism (se x) ∙ (ℱ ⟨ f ⟩))
                    (mp y f ∙ toSequentMorphism (se y)))
        (λ x → mapNatFrom-Contractible ℱ ob𝒢 se x)

    objSe-Contractible :
        {𝒞 : Semicategory so sa}
        (ℱ : Semifunctor (𝒞 ᵒᵖ) (SequentSemicategory 𝒥 i))
      → Contractible
          (∑[ ob𝒢 ∶ (Ob 𝒞 → Sequent 𝒥 i) ]
             ((x : Ob 𝒞) → SequentEquivalence (ℱ ⟨ x ⟩) (ob𝒢 x)))
    objSe-Contractible ℱ =
      Π-witness-Contractible
        (λ x t → SequentEquivalence (ℱ ⟨ x ⟩) t)
        (λ x → sequentTotalSpace-Contractible (ℱ ⟨ x ⟩))

    module _ {𝒞 : Semicategory so sa} where

      open Semicategory.Reasoning (𝒞 ᵒᵖ)

      ArrowsOf : (ob𝒢 : Ob 𝒞 → Sequent 𝒥 i) → Type (so ⊔ sa ⊔ o ⊔ a ⊔ lsuc i)
      ArrowsOf ob𝒢 = (x y : Ob 𝒞) (f : Hom 𝒞 x y) → SequentMorphism (ob𝒢 y) (ob𝒢 x)

      LawOf : (ob𝒢 : Ob 𝒞 → Sequent 𝒥 i) → ArrowsOf ob𝒢 → Type (so ⊔ sa ⊔ o ⊔ a ⊔ lsuc i)
      LawOf ob𝒢 mp =
        (A B E : Ob 𝒞) (g : Hom (𝒞 ᵒᵖ) A B) (h : Hom (𝒞 ᵒᵖ) B E)
        → mp E A (g ⨾ h) ＝ mp B A g ⨾ mp E B h

      lawOf-isProposition : (ob𝒢 : Ob 𝒞 → Sequent 𝒥 i) (mp : ArrowsOf ob𝒢)
                          → isProposition (LawOf ob𝒢 mp)
      lawOf-isProposition ob𝒢 mp =
        →-level λ A → →-level λ B → →-level λ E → →-level λ g → →-level λ h →
          ＝-isLevel ⦃ sequentMorphism-isSet ⦄

      buildSemifunctor : (ob𝒢 : Ob 𝒞 → Sequent 𝒥 i) (mp : ArrowsOf ob𝒢)
                       → LawOf ob𝒢 mp
                       → Semifunctor (𝒞 ᵒᵖ) (SequentSemicategory 𝒥 i)
      buildSemifunctor ob𝒢 mp law =
        record
          { onObjects = ob𝒢
          ; semifunctorial =
              record
                { mappable = record { map = λ {A} {B} f → mp B A f }
                ; preservesComposition =
                    record { preserves-composition = λ {A} {B} {E} g h → law A B E g h } } }

      SemifunctorTarget : (ℱ : Semifunctor (𝒞 ᵒᵖ) (SequentSemicategory 𝒥 i))
                        → Type (o ⊔ a ⊔ so ⊔ sa ⊔ lsuc i)
      SemifunctorTarget ℱ =
        ∑[ 𝒢 ∶ Semifunctor (𝒞 ᵒᵖ) (SequentSemicategory 𝒥 i) ]
          ∑[ se ∶ ((x : Ob 𝒞) → SequentEquivalence (ℱ ⟨ x ⟩) (𝒢 ⟨ x ⟩)) ]
            ({x y : Ob 𝒞} (f : Hom 𝒞 x y)
              → SequentMorphismEquality
                  (toSequentMorphism (se x) ∙ (ℱ ⟨ f ⟩))
                  ((𝒢 ⟨ f ⟩) ∙ toSequentMorphism (se y)))

      SemifunctorData : (ℱ : Semifunctor (𝒞 ᵒᵖ) (SequentSemicategory 𝒥 i))
                      → Type (o ⊔ a ⊔ so ⊔ sa ⊔ lsuc i)
      SemifunctorData ℱ =
        ∑[ p ∶ (∑[ ob𝒢 ∶ (Ob 𝒞 → Sequent 𝒥 i) ]
                  ((x : Ob 𝒞) → SequentEquivalence (ℱ ⟨ x ⟩) (ob𝒢 x))) ]
          ∑[ q ∶ (∑[ mp ∶ ArrowsOf (p₀ p) ]
                    ((x y : Ob 𝒞) (f : Hom 𝒞 x y)
                      → SequentMorphismEquality
                          (toSequentMorphism (p₁ p x) ∙ (ℱ ⟨ f ⟩))
                          (mp x y f ∙ toSequentMorphism (p₁ p y)))) ]
            LawOf (p₀ p) (p₀ q)

      toData : (ℱ : Semifunctor (𝒞 ᵒᵖ) (SequentSemicategory 𝒥 i))
             → SemifunctorTarget ℱ → SemifunctorData ℱ
      toData ℱ (𝒢 , se , nat) =
        (Semifunctor.onObjects 𝒢 , se)
        , ((λ x y f → 𝒢 ⟨ f ⟩) , (λ x y f → nat f))
        , (λ A B E g h → PreservesComposition.preserves-composition pres𝒢 g h)
        where
          open Semicategory.Reasoning (SequentSemicategory 𝒥 i)
          open Semifunctor.Reasoning 𝒢 renaming (preservesCompositionₛ to pres𝒢)

      fromData : (ℱ : Semifunctor (𝒞 ᵒᵖ) (SequentSemicategory 𝒥 i))
               → SemifunctorData ℱ → SemifunctorTarget ℱ
      fromData ℱ ((ob𝒢 , se) , (mp , nat) , law) =
        buildSemifunctor ob𝒢 mp law , se , (λ {x} {y} f → nat x y f)

      dataRoundTrip : (ℱ : Semifunctor (𝒞 ᵒᵖ) (SequentSemicategory 𝒥 i))
                    → fromData ℱ ∘ toData ℱ ~ id
      dataRoundTrip ℱ (𝒢 , se , nat) = refl

      semifunctorData-Contractible :
          (ℱ : Semifunctor (𝒞 ᵒᵖ) (SequentSemicategory 𝒥 i))
        → Contractible (SemifunctorData ℱ)
      semifunctorData-Contractible ℱ =
        ∑-Contractible (objSe-Contractible ℱ)
          (λ p → ∑-Contractible (mapNat-Contractible ℱ (p₀ p) (p₁ p))
                                (λ q → lawContractible p q))
        where
          lawContractible :
              (p : ∑[ ob𝒢 ∶ (Ob 𝒞 → Sequent 𝒥 i) ]
                     ((x : Ob 𝒞) → SequentEquivalence (ℱ ⟨ x ⟩) (ob𝒢 x)))
              (q : ∑[ mp ∶ ArrowsOf (p₀ p) ]
                     ((x y : Ob 𝒞) (f : Hom 𝒞 x y)
                       → SequentMorphismEquality
                           (toSequentMorphism (p₁ p x) ∙ (ℱ ⟨ f ⟩))
                           (mp x y f ∙ toSequentMorphism (p₁ p y))))
            → Contractible (LawOf (p₀ p) (p₀ q))
          lawContractible p q =
            inhabited-proposition→contractible
              ⦃ lawOf-isProposition (p₀ p) (p₀ q) ⦄
              (tr (LawOf (p₀ p)) toQ law*)
            where
              c = mapNat-Contractible ℱ (p₀ p) (p₁ p)

              centre : ∑[ mp ∶ ArrowsOf (p₀ p) ]
                         ((x y : Ob 𝒞) (f : Hom 𝒞 x y)
                           → SequentMorphismEquality
                               (toSequentMorphism (p₁ p x) ∙ (ℱ ⟨ f ⟩))
                               (mp x y f ∙ toSequentMorphism (p₁ p y)))
              centre = (λ x y f → transportedMap ℱ (p₀ p) (p₁ p) f)
                     , (λ x y f → transportedMap-natural ℱ (p₀ p) (p₁ p) f)

              toQ : p₀ centre ＝ p₀ q
              toQ = ap p₀ (sym (contraction c centre) ⨾ contraction c q)

              law* : LawOf (p₀ p) (p₀ centre)
              law* A B E g h = PreservesComposition.preserves-composition presT g h
                where
                  open Semicategory.Reasoning (SequentSemicategory 𝒥 i)
                  open Semifunctor.Reasoning (transportedSemifunctor ℱ (p₀ p) (p₁ p))
                    renaming (preservesCompositionₛ to presT)

    DependencyFibre : (s₀ : SequentStructure 𝒥 so sa i)
            (𝒟 : Semicategory so sa)
          → SequentStructure.dependency s₀ ≈ 𝒟
          → Type (o ⊔ a ⊔ so ⊔ sa ⊔ lsuc i)
    DependencyFibre s₀ 𝒟 w =
      ∑[ ob ∶ isSet (Ob 𝒟) ]
        ∑[ hm ∶ ((x y : Ob 𝒟) → isSet (Hom 𝒟 x y)) ]
          ∑[ 𝒢 ∶ Semifunctor (𝒟 ᵒᵖ) (SequentSemicategory 𝒥 i) ]
            ∑[ se ∶ ((x : Ob (SequentStructure.dependency s₀))
                      → SequentEquivalence (SequentStructure.sequent s₀ ⟨ x ⟩)
                                           (𝒢 ⟨ there (Semicategory-Equality.objects≈ w) x ⟩)) ]
              ({x y : Ob (SequentStructure.dependency s₀)}
                 (f : Hom (SequentStructure.dependency s₀) x y)
               → SequentMorphismEquality
                   (toSequentMorphism (se x) ∙ (SequentStructure.sequent s₀ ⟨ f ⟩))
                   ((𝒢 ⟨ there (Semicategory-Equality.hom≈ w x y) f ⟩) ∙ toSequentMorphism (se y)))

    totalSpace≃Fibres :
        (s₀ : SequentStructure 𝒥 so sa i)
      → (∑[ s₁ ∶ SequentStructure 𝒥 so sa i ] SequentStructureEquality s₀ s₁)
        → ∑[ p ∶ (∑[ 𝒟 ∶ Semicategory so sa ] (SequentStructure.dependency s₀ ≈ 𝒟)) ]
            DependencyFibre s₀ (p₀ p) (p₁ p)
    totalSpace≃Fibres s₀ (mkSequentStructure 𝒟 ob hm 𝒢 , mkSequentStructureEquality w se nat) =
      (𝒟 , w) , (ob , hm , 𝒢 , se , nat)

    fibres≃totalSpace :
        (s₀ : SequentStructure 𝒥 so sa i)
      → (∑[ p ∶ (∑[ 𝒟 ∶ Semicategory so sa ] (SequentStructure.dependency s₀ ≈ 𝒟)) ]
           DependencyFibre s₀ (p₀ p) (p₁ p))
        → ∑[ s₁ ∶ SequentStructure 𝒥 so sa i ] SequentStructureEquality s₀ s₁
    fibres≃totalSpace s₀ ((𝒟 , w) , (ob , hm , 𝒢 , se , nat)) =
      mkSequentStructure 𝒟 ob hm 𝒢 , mkSequentStructureEquality w se nat

    baseFibre-Contractible :
        (s₀ : SequentStructure 𝒥 so sa i)
      → Contractible (DependencyFibre s₀ (SequentStructure.dependency s₀)
                        (refl≈ ⦃ Semicategory-hasEquality ⦄))
    baseFibre-Contractible s₀ =
      ∑-Contractible
        (inhabited-proposition→contractible
           ⦃ is-level-isProposition ⦄ (SequentStructure.dependency-Ob-isSet s₀))
        (λ _ → ∑-Contractible
                 (inhabited-proposition→contractible
                    ⦃ →-level (λ x → →-level (λ y → is-level-isProposition)) ⦄
                    (SequentStructure.dependency-Hom-isSet s₀))
                 (λ _ → retract-Contractible
                          (toData (SequentStructure.sequent s₀))
                          (fromData (SequentStructure.sequent s₀))
                          (dataRoundTrip (SequentStructure.sequent s₀))
                          (semifunctorData-Contractible (SequentStructure.sequent s₀))))

    dependencyFibre-Contractible :
        (s₀ : SequentStructure 𝒥 so sa i)
        {𝒟 : Semicategory so sa} (w : SequentStructure.dependency s₀ ≈ 𝒟)
      → Contractible (DependencyFibre s₀ 𝒟 w)
    dependencyFibre-Contractible s₀ w =
      ≈-induction (λ 𝒟' w' → Contractible (DependencyFibre s₀ 𝒟' w'))
                  (baseFibre-Contractible s₀) w

  sequentStructureTotalSpace-Contractible :
      (s₀ : SequentStructure 𝒥 so sa i)
    → Contractible (∑[ s₁ ∶ SequentStructure 𝒥 so sa i ] SequentStructureEquality s₀ s₁)
  sequentStructureTotalSpace-Contractible s₀ =
    retract-Contractible (totalSpace≃Fibres s₀) (fibres≃totalSpace s₀) roundTrip
      (∑-Contractible (equality-Contractible (SequentStructure.dependency s₀))
                      (λ p → dependencyFibre-Contractible s₀ (p₁ p)))
    where
      roundTrip : fibres≃totalSpace s₀ ∘ totalSpace≃Fibres s₀ ~ id
      roundTrip (mkSequentStructure 𝒟 ob hm 𝒢 , mkSequentStructureEquality w se nat) = refl

instance
  sameySequentStructure : ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
                        → {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a}
                        → Samey 𝟙₀ (λ _ → SequentStructure 𝒥 so sa i)
  sameySequentStructure = record { samey = SequentStructureEquality }


module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a} where

  instance
    equalitySequentStructure : Equality 𝟙₀ (λ _ → SequentStructure 𝒥 so sa i)
    equalitySequentStructure =
      record { characterisation =
                 fundamentalTheorem SequentStructureEquality
                                    identitySequentStructureEquality
                                    sequentStructureTotalSpace-Contractible }


