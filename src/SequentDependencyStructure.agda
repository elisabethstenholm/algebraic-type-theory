module SequentDependencyStructure where

open import Prelude
open import Axioms
open import Algebra.Wild.Semicategory
open import Algebra.Wild.Semifunctor
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

-- ================ Sequent dependency structure ================

-- A sequent structure plus an added head with dependencies
-- in the structure. Generalises both ContextWithTerms and Rule

record SequentDependencyStructure
  ⦃ _ : FunExt ⦄
  ⦃ _ : AllSetQuotients ⦄
  {o a t : Level}
  (𝒥 : DependentSortVocabulary o a)
  (so sa i : Level)
  (A : Type t)
  (f : A → Context 𝒥 i)
  : Type (o ⊔ a ⊔ lsuc so ⊔ lsuc sa ⊔ lsuc i ⊔ t) where
  constructor mkSequentDependencyStructure
  field
    head : A
    sequentStructure : SequentStructure 𝒥 so sa i
    dependency : Semifunctor (SequentStructure.dependency sequentStructure) (hSet-Semicategory sa)
    realiseDependency : (d : Ob (SequentStructure.dependency sequentStructure))
                      → ⌞ (dependency ⟨ d ⟩) ⌟
                      → ContextMorphism
                          (extendedContext (SequentStructure.sequent sequentStructure ⟨ d ⟩))
                          (f head)
    coherenceRealisation : {d₀ d₁ : Ob (SequentStructure.dependency sequentStructure)}
                         → (f : ⌞ (dependency ⟨ d₀ ⟩) ⌟)
                         → (g : Hom (SequentStructure.dependency sequentStructure) d₀ d₁)
                         → realiseDependency d₁ ((dependency ⟨ g ⟩) f)
                         ＝ realiseDependency d₀ f ∙ SequentMorphism.sequentMorphism (SequentStructure.sequent sequentStructure ⟨ g ⟩)
open SequentDependencyStructure



-- ============= Dependency vocabulary =============

dependencyVocabulary : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
                     → {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a}
                     → SequentStructure 𝒥 so sa i → DependentSortVocabulary so sa
dependencyVocabulary s =
  record
    { semicategory = SequentStructure.dependency s
    ; judgmentForms-isSet = SequentStructure.dependency-Ob-isSet s
    ; judgmentDependencies-isSet = λ {x} {y} → SequentStructure.dependency-Hom-isSet s x y }


module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a}
  (ss : SequentStructure 𝒥 so sa i) where

  private
    𝒱 = dependencyVocabulary ss
    𝒟 = SequentStructure.dependency ss

  dependencyTotalSpace-Contractible :
      (dep₀ : Semifunctor 𝒟 (hSet-Semicategory sa))
    → Contractible
        (∑[ dep₁ ∶ Semifunctor 𝒟 (hSet-Semicategory sa) ]
           ∑[ te ∶ ((x : Ob 𝒟) → ⌞ (dep₀ ⟨ x ⟩) ⌟ ≃ ⌞ (dep₁ ⟨ x ⟩) ⌟) ]
             ({x y : Ob 𝒟} (g : Hom 𝒟 x y)
               → (dep₁ ⟨ g ⟩) ∘ there (te x) ＝ there (te y) ∘ (dep₀ ⟨ g ⟩)))
  dependencyTotalSpace-Contractible dep₀ =
    retract-Contractible toCtx fromCtx roundTrip
      (contextTotalSpace-Contractible {𝒥 = 𝒱} (mkContext dep₀))
    where
      toCtx : (∑[ dep₁ ∶ Semifunctor 𝒟 (hSet-Semicategory sa) ]
                ∑[ te ∶ ((x : Ob 𝒟) → ⌞ (dep₀ ⟨ x ⟩) ⌟ ≃ ⌞ (dep₁ ⟨ x ⟩) ⌟) ]
                  ({x y : Ob 𝒟} (g : Hom 𝒟 x y)
                    → (dep₁ ⟨ g ⟩) ∘ there (te x) ＝ there (te y) ∘ (dep₀ ⟨ g ⟩)))
            → ∑[ Δ ∶ Context 𝒱 sa ] ContextEquivalence (mkContext dep₀) Δ
      toCtx (dep₁ , te , nat) =
        mkContext dep₁
        , record
            { morphism = record { component = λ x → there (te x) ; natural = nat }
            ; component-isEquivalence = λ x → ≃→isEquivalence (te x) }

      fromCtx : (∑[ Δ ∶ Context 𝒱 sa ] ContextEquivalence (mkContext dep₀) Δ)
              → ∑[ dep₁ ∶ Semifunctor 𝒟 (hSet-Semicategory sa) ]
                  ∑[ te ∶ ((x : Ob 𝒟) → ⌞ (dep₀ ⟨ x ⟩) ⌟ ≃ ⌞ (dep₁ ⟨ x ⟩) ⌟) ]
                    ({x y : Ob 𝒟} (g : Hom 𝒟 x y)
                      → (dep₁ ⟨ g ⟩) ∘ there (te x) ＝ there (te y) ∘ (dep₀ ⟨ g ⟩))
      fromCtx (Δ , w) =
        Context.semifunctor Δ
        , (λ x → isEquivalence→≃ (ContextEquivalence.component-isEquivalence w x))
        , (λ g → ContextMorphism.natural (ContextEquivalence.morphism w) g)

      roundTrip : fromCtx ∘ toCtx ~ id
      roundTrip (dep₁ , te , nat) = refl


module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a i j k : Level} {𝒥 : DependentSortVocabulary o a}
  {Γ : Context 𝒥 i} {Δ : Context 𝒥 j} {Θ : Context 𝒥 k} where

  contextArrowFibre-Contractible :
      (T : Γ ⇒ Δ) (w : (j' : type (Judgment 𝒥)) → isEquivalence (T ⟨ j' ⟩))
      (K : Γ ⇒ Θ)
    → Contractible (∑[ m ∶ (Δ ⇒ Θ) ] ContextMorphismEquality K (m ∙ T))
  contextArrowFibre-Contractible T w K =
    retract-Contractible toParts fromParts roundTrip
      (≃-Contractible fibre≃∑
        (equivalenceFibresAreContractible
           (isEquivalence→≃ (precomposeContext-isEquivalence (mkContextEquivalence T w))) K))
    where
      toParts : (∑[ m ∶ (Δ ⇒ Θ) ] ContextMorphismEquality K (m ∙ T))
              → ∑[ m ∶ (Δ ⇒ Θ) ] (m ∙ T ＝ K)
      toParts (m , h) = m , sym (eq h)

      fromParts : (∑[ m ∶ (Δ ⇒ Θ) ] (m ∙ T ＝ K))
                → ∑[ m ∶ (Δ ⇒ Θ) ] ContextMorphismEquality K (m ∙ T)
      fromParts (m , p) = m , observe (sym p)

      roundTrip : fromParts ∘ toParts ~ id
      roundTrip (m , h) =
        ap (λ z → (m , z))
           (allEqual ⦃ contextMorphismEquality-isProposition ⦄ _ _)


