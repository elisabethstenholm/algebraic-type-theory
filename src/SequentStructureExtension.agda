module SequentStructureExtension where

open import Foundation
open import Foundation.Axioms
open import Foundation.SetQuotient
open import Foundation.Structure.Wild.Semi
open Semicategory.Semicategory
open import Foundation.Structure.Wild.TypeSemicategory

open import Sequent
open import SequentStructure

record SequentStructureExtension
  ⦃ _ : FunExt ⦄
  ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level}
  {𝒥 : Semicategory o a}
  (s : SequentStructure 𝒥 so sa i)
  : Type (o ⊔ a ⊔ lsuc i ⊔ so ⊔ lsuc sa) where
  constructor mkSequentStructureExtension
  field
    dependency : Semifunctor (SequentStructure.sequentDependency s) (TypeSemicategory sa)
    head : Sequent 𝒥 i
    realiseDependency : (d : Ob (SequentStructure.sequentDependency s))
                      → dependency ⟨ d ⟩
                      → SequentMorphism (SequentStructure.sequent s ⟨ d ⟩) head
    coherenceRealisation : {d₀ d₁ : Ob (SequentStructure.sequentDependency s)}
                         → (f : dependency ⟨ d₀ ⟩) 
                         → (g : Hom (SequentStructure.sequentDependency s) d₀ d₁)
                         → realiseDependency d₁ ((dependency ⟨ g ⟩) f)
                         ＝ realiseDependency d₀ f ∙ SequentStructure.sequent s ⟨ g ⟩

open SequentStructureExtension


module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : Semicategory o a}
  (s : SequentStructure 𝒥 so sa i) (e : SequentStructureExtension s) where

  extendSequentStructure : SequentStructure 𝒥 so sa i
  extendSequentStructure =
    record
      { sequentDependency = sequentDependency
      ; sequent = sequent }
    where
      𝒟 = SequentStructure.sequentDependency s
      ℱ = SequentStructure.sequent s
      open Semicategory.Reasoning 𝒟
      open Semicategory.Reasoning (𝒟 ᵒᵖ)
      open Semicategory.Reasoning (TypeSemicategory sa)
      open Semifunctor.Reasoning (dependency e)

      data ob : Type so where
        injOb : Ob 𝒟 → ob
        newOb : ob

      hom' : ob → ob → Type sa
      hom' (injOb x) (injOb y) = Hom 𝒟 x y
      hom' (injOb x) newOb = 𝟘
      hom' newOb (injOb x) = dependency e ⟨ x ⟩
      hom' newOb newOb = 𝟘

      data hom (x y : ob) : Type sa where
        include : hom' x y → hom x y

      composition : {A B C : ob} → hom A B → hom B C → hom A C
      composition {injOb x} {injOb y} {injOb z} (include f) (include g) = include (g ∙ f)
      composition {newOb} {injOb y} {injOb z} (include f) (include g) = include ((dependency e ⟨ g ⟩) f)
      composition {injOb x} {newOb} {injOb z} (include ()) g
      composition {newOb} {newOb} {injOb z} (include ()) g
      composition {A} {injOb y} {newOb} f (include ())
      composition {A} {newOb} {newOb} f (include ())

      instance
        composable : Composable 𝟙 (λ _ → ob) hom
        composable = record { composition = composition }

      associativeComposition : {A B C D : ob} {f : hom A B} {g : hom B C} {h : hom C D}
                             → h ∙ (g ∙ f) ＝ (h ∙ g) ∙ f
      associativeComposition {injOb w} {injOb x} {injOb y} {injOb z} {include f} {include g} {include h} = ap include ∙-associative
      associativeComposition {newOb} {injOb x} {injOb y} {injOb z} {include f} {include g} {include h} = ap (λ σ → include (σ f)) (sym (preserves-composition _ _))
      associativeComposition {A} {injOb y} {injOb x} {newOb} {f} {g} {include ()}
      associativeComposition {A} {injOb y} {newOb} {D} {f} {include ()} {h}
      associativeComposition {injOb x} {newOb} {C} {D} {include ()} {g} {h}
      associativeComposition {newOb} {newOb} {C} {D} {include ()} {g} {h}

      instance
        assoc : AssociativeComposition hom (λ _ _ → _＝_)
        assoc = record { ⨾-associative = associativeComposition }

        semicat : Semicategorical 𝟙 (λ _ → ob) hom (λ _ _ → _＝_)
        semicat = record {}

      sequentDependency : Semicategory so sa
      sequentDependency = asSemicategory (λ _ → ob) hom ★

      obMap : ob → Sequent 𝒥 i
      obMap (injOb x) = ℱ ⟨ x ⟩
      obMap newOb = head e

      homMap : {x y : ob} → hom y x → SequentMorphism (obMap x) (obMap y)
      homMap {injOb x} {injOb y} (include f) = ℱ ⟨ f ⟩
      homMap {newOb} {injOb y} (include ())
      homMap {injOb x} {newOb} (include f) = realiseDependency e x f
      homMap {newOb} {newOb} (include ())

      preserves : {A B C : ob} (f : hom A B) (g : hom B C)
                → homMap (g ∙ f) ＝ homMap f ∙ homMap g
      preserves {injOb x} {injOb y} {injOb z} (include f) (include g) = PreservesComposition.preserves-composition pres _ _
        where
          open Semifunctor.Reasoning ℱ renaming (preservesCompositionₛ to pres)
          open Semicategory.Reasoning (SequentSemicategory 𝒥 i)
      preserves {newOb} {injOb y} {injOb z} (include f) (include g) = coherenceRealisation e f g
      preserves {A} {injOb x} {newOb} f (include ())
      preserves {injOb x} {newOb} {C} (include ()) g
      preserves {newOb} {newOb} {C} (include ()) g

      sequent : Semifunctor (sequentDependency ᵒᵖ) (SequentSemicategory 𝒥 i)
      sequent = 
        record
          { onObjects = obMap
          ; semifunctorial = record
              { mappable = record { map = homMap }
              ; preservesComposition = record { preserves-composition = flip preserves } } }
