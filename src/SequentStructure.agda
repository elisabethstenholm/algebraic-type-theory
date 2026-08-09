module SequentStructure where

open import Prelude
open import Axioms
open import Homotopy.SetQuotient
open import Algebra.Wild.Semi
open Semicategory.Semicategory

open import Context
open import Sequent

-- ============= Sequent structures ============

record SequentStructure
  ⦃ _ : FunExt ⦄
  ⦃ _ : AllSetQuotients ⦄
  {o a : Level}
  (𝒥 : Semicategory o a)
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
                      → (𝒥 : Semicategory o a) (so sa i : Level)
                      → SequentStructure 𝒥 so sa i
emptySequentStructure 𝒥 so sa i =
  record
    { dependency = emptySemicategory so sa
    ; sequent = emptySemifunctorᵒᵖ (SequentSemicategory 𝒥 i) so sa }

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
  {𝒥 : Semicategory o a}
  (sd : SequentStructure 𝒥 so₀ sa₀ i₀)
  (sc : SequentStructure 𝒥 so₁ sa₁ i₁)
  (j : Level)
  : Type (o ⊔ a ⊔ so₀ ⊔ sa₀ ⊔ i₀ ⊔ so₁ ⊔ sa₁ ⊔ i₁ ⊔ lsuc j) where
  constructor mkSequentStructureMorphism
  field
    onDependencies : Semifunctor (SequentStructure.dependency sd) (SequentStructure.dependency sc)
    dependenciesEquivalence : (x : Ob (SequentStructure.dependency sd))
                            → isEquivalence (mapDependencies onDependencies x)
    -- TODO: add terms to the base context
    baseContext : Context 𝒥 j
    contextEquivalence : (x : Ob (SequentStructure.dependency sd))
                       → baseContext + Sequent.context (SequentStructure.sequent sd ⟨ x ⟩)
                       ≈ Sequent.context (SequentStructure.sequent sc ⟨ onDependencies ⟨ x ⟩ ⟩)
    -- TODO: add naturality condition wrt onDependencies and SequentStructure.sequent
