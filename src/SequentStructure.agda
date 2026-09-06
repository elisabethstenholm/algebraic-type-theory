module SequentStructure where

open import Prelude
open import Axioms
open import Algebra.Wild.Semi
open Semicategory.Semicategory
open import Algebra.Wild.TruncatedTypeSemicategory
open import Homotopy.Equality
open import Homotopy.Fibre
open import Homotopy.Levels
open import Homotopy.StructuredType
open import Homotopy.SetQuotient
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

-- ============= Sequent structures ============

record SequentStructure
  ⦃ _ : FunExt ⦄
  ⦃ _ : AllSetQuotients ⦄
  {o a : Level}
  (𝒥 : DependentSortVocabulary o a)
  (so sa i : Level)
  : Type (o ⊔ a ⊔ lsuc so ⊔ lsuc sa ⊔ lsuc i) where
  constructor mkSequentStructure
  field
    dependency : Semicategory so sa
    dependency-Ob-isSet : isSet (Ob dependency)
    dependency-Hom-isSet : (x y : Ob dependency) → isSet (Hom dependency x y)
    sequent : Semifunctor (dependency ᵒᵖ) (SequentSemicategory 𝒥 i)


-- ============== Empty sequent structure =============

emptySemicategory : (so sa : Level) → Semicategory so sa
emptySemicategory so sa =
  record
    { Ob = Empty
    ; Hom = absurd
    ; semicategorical = record
      { composable = record { composition = λ { {A = ()} _ _ } }
      ; associativeComposition = record { ⨾-associative = λ { {A = ()} } } } }

module _ {co ca : Level} (𝒞 : Semicategory co ca) where

  open Semicategory.Reasoning 𝒞

  emptySemifunctor : (so sa : Level) → Semifunctor (emptySemicategory so sa) 𝒞
  emptySemifunctor so sa =
    record
      { onObjects = λ ()
      ; semifunctorial = record
        { mappable = record { map = λ { {A = ()} } }
        ; preservesComposition = record { preserves-composition = λ { {A = ()} } } } }

  emptySemifunctorᵒᵖ : (so sa : Level) → Semifunctor (emptySemicategory so sa ᵒᵖ) 𝒞
  emptySemifunctorᵒᵖ so sa =
    record
      { onObjects = λ ()
      ; semifunctorial = record
        { mappable = record { map = λ { {A = ()} } }
        ; preservesComposition = record { preserves-composition = λ { {A = ()} } } } }

emptySequentStructure : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄ {o a : Level}
                      → (𝒥 : DependentSortVocabulary o a) (so sa i : Level)
                      → SequentStructure 𝒥 so sa i
emptySequentStructure 𝒥 so sa i =
  record
    { dependency = emptySemicategory so sa
    ; dependency-Ob-isSet = 𝟘-isLevel
    ; dependency-Hom-isSet = λ ()
    ; sequent = emptySemifunctorᵒᵖ (SequentSemicategory 𝒥 i) so sa }


-- ================= One element sequent structure ===============

unitSemicategory : (so sa : Level) → Semicategory so sa
unitSemicategory so sa =
  record
    { Ob = Unit
    ; Hom = λ _ _ → Empty
    ; semicategorical = record
        { composable = record { composition = absurd }
        ; associativeComposition = record { ⨾-associative = λ { {f = ()} } } } }

module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a i : Level} {𝒥 : DependentSortVocabulary o a} (s : Sequent 𝒥 i) where

  open Semicategory.Reasoning (DependentSortVocabulary.semicategory 𝒥)

  unitSemifunctor : (so sa : Level) → Semifunctor (unitSemicategory so sa) (SequentSemicategory 𝒥 i)
  unitSemifunctor so sa =
    record
      { onObjects = λ _ → s
      ; semifunctorial = record
        { mappable = record { map = absurd }
        ; preservesComposition = record { preserves-composition = λ () } } }

  unitSemifunctorᵒᵖ : (so sa : Level) → Semifunctor (unitSemicategory so sa ᵒᵖ) (SequentSemicategory 𝒥 i)
  unitSemifunctorᵒᵖ so sa =
    record
      { onObjects = λ _ → s
      ; semifunctorial = record
        { mappable = record { map = absurd }
        ; preservesComposition = record { preserves-composition = λ () } } }

unitSequentStructure : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
                     → {o a i : Level} {𝒥 : DependentSortVocabulary o a}
                     → Sequent 𝒥 i → (so sa : Level) → SequentStructure 𝒥 so sa i
unitSequentStructure s so sa =
  record
    { dependency = unitSemicategory so sa
    ; dependency-Ob-isSet = 𝟙-isLevel
    ; dependency-Hom-isSet = λ _ _ → 𝟘-isLevel
    ; sequent = unitSemifunctorᵒᵖ s so sa }

