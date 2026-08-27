module SequentStructure where

open import Prelude
open import Axioms
open import Homotopy.SetQuotient
open import Structure.Composable
open import Algebra.Wild.Semi
open Semicategory.Semicategory
open import Algebra.Wild.TypeSemicategory

open import DependentSortVocabulary
open import Context
open import Sequent

-- ============= Sequent structures ============

record SequentStructure
  ⦃ _ : FunExt ⦄
  ⦃ _ : AllSetQuotients ⦄
  {o a : Level}
  (𝒥 : DependentSortVocabulary {o} {a})
  (so sa i : Level)
  : Type (o ⊔ a ⊔ lsuc so ⊔ lsuc sa ⊔ lsuc i) where
  constructor mkSequentStructure
  field
    dependency : Semicategory so sa
    sequent : Semifunctor (dependency ᵒᵖ) (SequentSemicategory 𝒥 i)

data EmptyOb (so : Level) : Type so where

EmptyHom' : {so : Level} (sa : Level) → EmptyOb so → EmptyOb so → Type sa
EmptyHom' sa () ()

data EmptyHom {so : Level} (sa : Level) (x y : EmptyOb so) : Type sa where
  emptyHom : EmptyHom' sa x y → EmptyHom sa x y

emptySemicategory : (so sa : Level) → Semicategory so sa
emptySemicategory so sa =
  record
    { Ob = EmptyOb so
    ; Hom = EmptyHom sa
    ; semicategorical = record
      { composable = record { composition = λ { {A = ()} _ _ } }
      ; associativeComposition = record { ⨾-associative = λ { {A = ()} } } } }

module _ {co ca : Level} (𝒞 : Semicategory co ca) where

  open Semicategory.Reasoning 𝒞

  emptySemifunctorOnObjects : {so : Level} → EmptyOb so → Ob 𝒞
  emptySemifunctorOnObjects ()

  emptySemifunctor : (so sa : Level) → Semifunctor (emptySemicategory so sa) 𝒞
  emptySemifunctor so sa =
    record
      { onObjects = emptySemifunctorOnObjects
      ; semifunctorial = record
        { mappable = record { map = λ { {A = ()} } }
        ; preservesComposition = record { preserves-composition = λ { {A = ()} } } } }

  emptySemifunctorᵒᵖ : (so sa : Level) → Semifunctor (emptySemicategory so sa ᵒᵖ) 𝒞
  emptySemifunctorᵒᵖ so sa =
    record
      { onObjects = emptySemifunctorOnObjects
      ; semifunctorial = record
        { mappable = record { map = λ { {A = ()} } }
        ; preservesComposition = record { preserves-composition = λ { {A = ()} } } } }

emptySequentStructure : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄ {o a : Level}
                      → (𝒥 : DependentSortVocabulary {o} {a}) (so sa i : Level)
                      → SequentStructure 𝒥 so sa i
emptySequentStructure 𝒥 so sa i =
  record
    { dependency = emptySemicategory so sa
    ; sequent = emptySemifunctorᵒᵖ (SequentSemicategory 𝒥 i) so sa }

record SequentDependencyStructure
  ⦃ _ : FunExt ⦄
  ⦃ _ : AllSetQuotients ⦄
  {o a t : Level}
  (𝒥 : DependentSortVocabulary {o} {a})
  (so sa i : Level)
  (A : Type t)
  (f : A → Context 𝒥 i)
  : Type (o ⊔ a ⊔ lsuc so ⊔ lsuc sa ⊔ lsuc i ⊔ t) where
  constructor mkSequentDependencyStructure
  field
    head : A
    sequentStructure : SequentStructure 𝒥 so sa i
    dependency : Semifunctor (SequentStructure.dependency sequentStructure) (TypeSemicategory sa)
    realiseDependency : (d : Ob (SequentStructure.dependency sequentStructure))
                      → dependency ⟨ d ⟩
                      → ContextMorphism
                          (extendedContext (SequentStructure.sequent sequentStructure ⟨ d ⟩))
                          (f head)
    coherenceRealisation : {d₀ d₁ : Ob (SequentStructure.dependency sequentStructure)}
                         → (f : dependency ⟨ d₀ ⟩) 
                         → (g : Hom (SequentStructure.dependency sequentStructure) d₀ d₁)
                         → realiseDependency d₁ ((dependency ⟨ g ⟩) f)
                         ＝ realiseDependency d₀ f ∙ SequentMorphism.sequentMorphism (SequentStructure.sequent sequentStructure ⟨ g ⟩)
open SequentDependencyStructure

