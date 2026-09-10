module SequentStructureMorphism.Equality where

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
open import SequentStructureMorphism


-- =============== Equality of sequent dependency morphisms ===============

record SequentDependencyMorphismEquality
  ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {so₀ sa₀ so₁ sa₁ : Level}
  {s₀ : Semicategory so₀ sa₀} {s₁ : Semicategory so₁ sa₁}
  (F₀ F₁ : SequentDependencyMorphism s₀ s₁)
  : Type (so₀ ⊔ sa₀ ⊔ so₁ ⊔ sa₁) where
  constructor mkSequentDependencyMorphismEquality
  field
    onObjects≈ :
      Semifunctor.onObjects (SequentDependencyMorphism.onDependencies F₀)
      ~ Semifunctor.onObjects (SequentDependencyMorphism.onDependencies F₁)
    witness≈ :
      SemifunctorWitness {C = s₀} {D = s₁}
        (Semifunctor.semifunctorial (SequentDependencyMorphism.onDependencies F₀))
        onObjects≈
        (Semifunctor.semifunctorial (SequentDependencyMorphism.onDependencies F₁))

module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {so₀ sa₀ so₁ sa₁ : Level}
  {s₀ : Semicategory so₀ sa₀} {s₁ : Semicategory so₁ sa₁} where

  identitySequentDependencyMorphismEquality :
      (F : SequentDependencyMorphism s₀ s₁) → SequentDependencyMorphismEquality F F
  identitySequentDependencyMorphismEquality F =
    record { onObjects≈ = ~-refl
           ; witness≈ =
               semifunctorWitness-refl {C = s₀} {D = s₁}
                 (Semifunctor.semifunctorial
                    (SequentDependencyMorphism.onDependencies F)) }

  instance
    sameySequentDependencyMorphism :
        Samey 𝟙₀ (λ _ → SequentDependencyMorphism s₀ s₁)
    sameySequentDependencyMorphism =
      record { samey = SequentDependencyMorphismEquality }

  private
    equivalenceField-Contractible :
        (Φ : Semifunctor s₀ s₁)
      → ((x : Ob s₀) → isEquivalence (mapDependencies Φ x))
      → Contractible ((x : Ob s₀) → isEquivalence (mapDependencies Φ x))
    equivalenceField-Contractible Φ e =
      →-Contractible
        (λ x → inhabited-proposition→contractible ⦃ isEquivalenceIsProposition ⦄ (e x))

    sequentDependencyMorphismTotalSpace-Contractible :
        (F₀ : SequentDependencyMorphism s₀ s₁)
      → Contractible (∑[ F₁ ∶ SequentDependencyMorphism s₀ s₁ ]
                        SequentDependencyMorphismEquality F₀ F₁)
    sequentDependencyMorphismTotalSpace-Contractible F₀ =
      retract-Contractible toParts fromParts roundTrip
        (∑-Contractible-over
           (equality-Contractible ⦃ w = Semifunctor-hasEquality ⦄
              (SequentDependencyMorphism.onDependencies F₀))
           (equivalenceField-Contractible
              (SequentDependencyMorphism.onDependencies F₀)
              (SequentDependencyMorphism.dependenciesEquivalence F₀)))
      where
        Base : Type (so₀ ⊔ sa₀ ⊔ so₁ ⊔ sa₁)
        Base = ∑[ Φ ∶ Semifunctor s₀ s₁ ]
                 Semifunctor-Equality
                   (SequentDependencyMorphism.onDependencies F₀) Φ

        Parts : Type (so₀ ⊔ sa₀ ⊔ so₁ ⊔ sa₁)
        Parts = ∑[ w ∶ Base ] ((x : Ob s₀) → isEquivalence (mapDependencies (p₀ w) x))

        toParts : (∑[ F₁ ∶ SequentDependencyMorphism s₀ s₁ ]
                     SequentDependencyMorphismEquality F₀ F₁)
                → Parts
        toParts (mkSequentDependencyMorphism Φ e , w) =
          (Φ , semifunctor≈ (SequentDependencyMorphismEquality.onObjects≈ w)
                            (p₀ (SequentDependencyMorphismEquality.witness≈ w))
                            (p₁ (SequentDependencyMorphismEquality.witness≈ w))) , e

        fromParts : Parts
                  → ∑[ F₁ ∶ SequentDependencyMorphism s₀ s₁ ]
                      SequentDependencyMorphismEquality F₀ F₁
        fromParts ((Φ , w) , e) =
          mkSequentDependencyMorphism Φ e ,
          record { onObjects≈ = Semifunctor-Equality.objects≈ w
                 ; witness≈ = Semifunctor-Equality.map≈ w , Semifunctor-Equality.preservesComposition≈ w }

        roundTrip : fromParts ∘ toParts ~ id
        roundTrip (mkSequentDependencyMorphism Φ e , w) = refl

  instance
    equalitySequentDependencyMorphism :
        Equality 𝟙₀ (λ _ → SequentDependencyMorphism s₀ s₁)
    equalitySequentDependencyMorphism =
      record { characterisation =
                 fundamentalTheorem SequentDependencyMorphismEquality
                                    identitySequentDependencyMorphismEquality
                                    sequentDependencyMorphismTotalSpace-Contractible }


-- =============== Equality of sequent structure morphisms ===============

record SequentStructureMorphismEquality
  ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so₀ sa₀ i₀ so₁ sa₁ i₁ : Level}
  {𝒥 : DependentSortVocabulary o a}
  {s₀ : SequentStructure 𝒥 so₀ sa₀ i₀} {s₁ : SequentStructure 𝒥 so₁ sa₁ i₁}
  (φ₀ φ₁ : SequentStructureMorphism s₀ s₁)
  : Type (o ⊔ a ⊔ so₀ ⊔ sa₀ ⊔ so₁ ⊔ sa₁ ⊔ i₀ ⊔ i₁) where
  constructor mkSequentStructureMorphismEquality
  field
    dependencyMorphism≈ :
      SequentDependencyMorphismEquality
        (SequentStructureMorphism.dependencyMorphism φ₀)
        (SequentStructureMorphism.dependencyMorphism φ₁)
    sequentEquivalence≈ :
      (x : Ob (SequentStructure.dependency s₀))
      → SequentEquivalenceEquality
          (tr (λ y → SequentEquivalence (SequentStructure.sequent s₀ ⟨ x ⟩) (SequentStructure.sequent s₁ ⟨ y ⟩))
              (SequentDependencyMorphismEquality.onObjects≈ dependencyMorphism≈ x)
              (SequentStructureMorphism.sequentEquivalence φ₀ x))
          (SequentStructureMorphism.sequentEquivalence φ₁ x)

module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so₀ sa₀ i₀ so₁ sa₁ i₁ : Level}
  {𝒥 : DependentSortVocabulary o a}
  {s₀ : SequentStructure 𝒥 so₀ sa₀ i₀} {s₁ : SequentStructure 𝒥 so₁ sa₁ i₁} where

  private
    𝒟 = SequentStructure.dependency s₀
    ℰ = SequentStructure.dependency s₁
    𝒢 = SequentStructure.sequent s₀
    ℋ = SequentStructure.sequent s₁

  identitySequentStructureMorphismEquality :
      (φ : SequentStructureMorphism s₀ s₁) → SequentStructureMorphismEquality φ φ
  identitySequentStructureMorphismEquality φ =
    record
      { dependencyMorphism≈ =
          identitySequentDependencyMorphismEquality
            (SequentStructureMorphism.dependencyMorphism φ)
      ; sequentEquivalence≈ =
          λ x → identitySequentEquivalenceEquality
                  (SequentStructureMorphism.sequentEquivalence φ x) }

  instance
    sameySequentStructureMorphism :
        Samey 𝟙₀ (λ _ → SequentStructureMorphism s₀ s₁)
    sameySequentStructureMorphism =
      record { samey = SequentStructureMorphismEquality }

  private
    module TotalSpace (φ₀ : SequentStructureMorphism s₀ s₁) where
      Φ : SequentDependencyMorphism 𝒟 ℰ
      Φ = SequentStructureMorphism.dependencyMorphism φ₀

      SE : (x : Ob 𝒟) → SequentEquivalence (𝒢 ⟨ x ⟩) (ℋ ⟨ Φ ⟨ x ⟩ ⟩)
      SE = SequentStructureMorphism.sequentEquivalence φ₀

      Base : Type (so₀ ⊔ sa₀ ⊔ so₁ ⊔ sa₁)
      Base = ∑[ dm ∶ SequentDependencyMorphism 𝒟 ℰ ]
               SequentDependencyMorphismEquality Φ dm

      SeqPart : Base → Type (o ⊔ a ⊔ so₀ ⊔ lsuc i₀ ⊔ lsuc i₁)
      SeqPart w =
        ∑[ se ∶ ((x : Ob 𝒟) → SequentEquivalence (𝒢 ⟨ x ⟩) (ℋ ⟨ p₀ w ⟨ x ⟩ ⟩)) ]
          ((x : Ob 𝒟)
           → SequentEquivalenceEquality
               (tr (λ y → SequentEquivalence (𝒢 ⟨ x ⟩) (ℋ ⟨ y ⟩))
                   (SequentDependencyMorphismEquality.onObjects≈ (p₁ w) x)
                   (SE x))
               (se x))

      NatPart : (w : Base) → SeqPart w → Type (o ⊔ a ⊔ so₀ ⊔ sa₀ ⊔ lsuc i₀ ⊔ lsuc i₁)
      NatPart w v =
        (x y : Ob 𝒟) (f : Hom 𝒟 x y)
        → toSequentMorphism (p₀ v x) ∙ 𝒢 ⟨ f ⟩
          ＝ ℋ ⟨ p₀ w ⟨ f ⟩ ⟩ ∙ toSequentMorphism (p₀ v y)

      natPart-isProposition : {w : Base} {v : SeqPart w} → isProposition (NatPart w v)
      natPart-isProposition =
        →-level (λ _ → →-level (λ _ → →-level (λ _ → ＝-isLevel ⦃ sequentMorphism-isSet ⦄)))

      Parts : Type (o ⊔ a ⊔ so₀ ⊔ sa₀ ⊔ so₁ ⊔ sa₁ ⊔ lsuc i₀ ⊔ lsuc i₁)
      Parts = ∑[ w ∶ Base ] ∑[ v ∶ SeqPart w ] NatPart w v

      toParts : (∑[ φ₁ ∶ SequentStructureMorphism s₀ s₁ ]
                   SequentStructureMorphismEquality φ₀ φ₁)
              → Parts
      toParts (mkSequentStructureMorphism dm se nat , q) =
          (dm , SequentStructureMorphismEquality.dependencyMorphism≈ q)
        , (se , SequentStructureMorphismEquality.sequentEquivalence≈ q)
        , (λ x y f → nat {x} {y} f)

      fromParts : Parts
                → ∑[ φ₁ ∶ SequentStructureMorphism s₀ s₁ ]
                    SequentStructureMorphismEquality φ₀ φ₁
      fromParts ((dm , dq) , (se , sq) , nat) =
          mkSequentStructureMorphism dm se (λ {x} {y} f → nat x y f)
        , record { dependencyMorphism≈ = dq ; sequentEquivalence≈ = sq }

      roundTrip : fromParts ∘ toParts ~ id
      roundTrip (mkSequentStructureMorphism dm se nat , q) = refl

      parts-Contractible : Contractible Parts
      parts-Contractible =
        ∑-Contractible-over
          (inhabited-proposition→contractible
             ⦃ contractible→level ⦃ contractible-type
                 (equality-Contractible ⦃ w = equalitySequentDependencyMorphism ⦄ Φ) ⦄ ⦄
             (Φ , identitySequentDependencyMorphismEquality Φ))
          (∑-Contractible-over
             (Π-witness-Contractible
                (λ x se → SequentEquivalenceEquality (SE x) se)
                (λ x → equality-Contractible ⦃ w = equalitySequentEquivalence ⦄ (SE x)))
             (inhabited-proposition→contractible
                ⦃ natPart-isProposition
                    {w = Φ , identitySequentDependencyMorphismEquality Φ}
                    {v = SE , (λ x → identitySequentEquivalenceEquality (SE x))} ⦄
                (λ x y f → SequentStructureMorphism.natural φ₀ f)))

    sequentStructureMorphismTotalSpace-Contractible :
        (φ₀ : SequentStructureMorphism s₀ s₁)
      → Contractible (∑[ φ₁ ∶ SequentStructureMorphism s₀ s₁ ]
                        SequentStructureMorphismEquality φ₀ φ₁)
    sequentStructureMorphismTotalSpace-Contractible φ₀ =
      retract-Contractible (TotalSpace.toParts φ₀) (TotalSpace.fromParts φ₀)
                           (TotalSpace.roundTrip φ₀) (TotalSpace.parts-Contractible φ₀)

  instance
    equalitySequentStructureMorphism :
        Equality 𝟙₀ (λ _ → SequentStructureMorphism s₀ s₁)
    equalitySequentStructureMorphism =
      record { characterisation =
                 fundamentalTheorem SequentStructureMorphismEquality
                                    identitySequentStructureMorphismEquality
                                    sequentStructureMorphismTotalSpace-Contractible }


