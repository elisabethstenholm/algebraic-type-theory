module SequentStructureExtension where

open import Prelude
open import Axioms
open import Homotopy.SetQuotient
open import Structure.Associativity
open import Structure.Composable
open import Structure.PreservesComposition
open import Structure.Reasoning
open import Structure.Symmetric
open import Algebra.Wild.Semi
open Semicategory.Semicategory
open import Algebra.Wild.TypeSemicategory

open import DependentSortVocabulary
open import Context
open import Sequent
open import SequentStructure
open SequentDependencyStructure

SequentStructureWithExtension : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
                              → {o a : Level} (𝒥 : DependentSortVocabulary {o} {a})
                              → (so sa i : Level)
                              → Type (o ⊔ a ⊔ lsuc so ⊔ lsuc sa ⊔ lsuc i)
SequentStructureWithExtension {o = o}  𝒥 so sa i = SequentDependencyStructure 𝒥 so sa i (Sequent 𝒥 i) Sequent.context

emptySequentStructureWithExtension : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄ {o a so sa : Level} (𝒥 : DependentSortVocabulary {o} {a}) (i : Level)
                                   → Sequent 𝒥 i → SequentStructureWithExtension 𝒥 so sa i
emptySequentStructureWithExtension {so = so} {sa = sa} 𝒥 i s =
  record
    { head = s
    ; sequentStructure = emptySequentStructure 𝒥 so sa i
    ; dependency = emptySemifunctor (TypeSemicategory sa) so sa
    ; realiseDependency = λ ()
    ; coherenceRealisation = λ { {()} } }


module ExtendedSequentStructure ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : DependentSortVocabulary {o} {a}}
  (e : SequentStructureWithExtension 𝒥 so sa i) where

  𝒟 = SequentStructure.dependency (sequentStructure e)
  ℱ = SequentStructure.sequent (sequentStructure e)

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
  homMap {injOb x} {newOb} (include f) = mkSequentMorphism (→⋊ (head e) ∙ realiseDependency e x f)
  homMap {newOb} {newOb} (include ())

  preserves : {A B C : ob} (f : hom A B) (g : hom B C)
            → homMap (g ∙ f) ＝ homMap f ∙ homMap g
  preserves {injOb x} {injOb y} {injOb z} (include f) (include g) = PreservesComposition.preserves-composition pres _ _
    where
      open Semifunctor.Reasoning ℱ renaming (preservesCompositionₛ to pres)
      open Semicategory.Reasoning (SequentSemicategory 𝒥 i)
  preserves {newOb} {injOb y} {injOb z} (include f) (include g) = ap mkSequentMorphism
    (begin
      →⋊ (head e) ∙ realiseDependency e z ((dependency e ⟨ g ⟩) f)                         ⟪ ap (→⋊ (head e) ∙_) (coherenceRealisation e f g) ⟫
      →⋊ (head e) ∙ (realiseDependency e y f ∙ SequentMorphism.sequentMorphism (ℱ ⟨ g ⟩))  ⟪ ∙-associative {g = realiseDependency e y f} ⟫
      (→⋊ (head e) ∙ realiseDependency e y f) ∙ SequentMorphism.sequentMorphism (ℱ ⟨ g ⟩)  ∎)
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

  extended : SequentStructure 𝒥 so sa i
  extended =
    record
      { dependency = sequentDependency
      ; sequent = sequent }

extendSequentStructure : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
                       → {o a so sa i : Level} {𝒥 : DependentSortVocabulary {o} {a}}
                       → SequentStructureWithExtension 𝒥 so sa i
                       → SequentStructure 𝒥 so sa i
extendSequentStructure e = ExtendedSequentStructure.extended e

⋊ₛ_ : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
    → {o a so sa i : Level} {𝒥 : DependentSortVocabulary {o} {a}}
    → SequentStructureWithExtension 𝒥 so sa i
    → SequentStructure 𝒥 so sa i
⋊ₛ_ = extendSequentStructure
