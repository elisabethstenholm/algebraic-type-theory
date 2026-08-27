module SequentStructureMorphism where

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
  {𝒥 : DependentSortVocabulary {o} {a}}
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
