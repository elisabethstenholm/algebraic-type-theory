module Example.Category where

open import Foundation.Axioms
open import Foundation.Base
import Foundation.Structure.Wild.Semicategory as Semicategory
open Semicategory using (Semicategory; asSemicategory)
open import Foundation.Structure.Semicategorical
open import Foundation.Structure.Composable
open import Foundation.Structure.Associativity
import Foundation.Structure.Wellfounded as Wellfounded
open Wellfounded using (Wellfounded)
import Foundation.Structure.Accessible as Accessible
open Accessible using (Accessible)
open import Foundation.Structure.Wild.SemiYoneda
open import Foundation.Structure.Appliable
open import Foundation.Structure.Wild.Semifunctor

open import DependentSortVocabulary
open import Sequent
open Sequent.Sequent

-- The dependent sort vocabulary for categories is the semicategory given by
--
--    sc   lhs
--   <--   <--
-- Ob   Hom   Eq
--   <--   <--
--    tg   rhs
--
-- and the equalities: sc ∘ lhs = sc ∘ rhs and tg ∘ lhs = tg ∘ rhs

data Judgment : Type lzero where
  Ob  : Judgment
  Hom : Judgment
  Eq  : Judgment

data Dependency : (j j' : Judgment) → Type lzero where
  Hom-sc : Dependency Hom Ob
  Hom-tg : Dependency Hom Ob
  Eq-lhs : Dependency Eq Hom
  Eq-rhs : Dependency Eq Hom
  Eq-sc  : Dependency Eq Ob
  Eq-tg  : Dependency Eq Ob

instance
  composable : Composable 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Judgment) Dependency
  Composable.composition composable Hom-sc ()
  Composable.composition composable Hom-tg ()
  Composable.composition composable Eq-lhs Hom-sc = Eq-sc
  Composable.composition composable Eq-lhs Hom-tg = Eq-tg
  Composable.composition composable Eq-rhs Hom-sc = Eq-sc
  Composable.composition composable Eq-rhs Hom-tg = Eq-tg
  Composable.composition composable Eq-sc ()
  Composable.composition composable Eq-tg ()

  associativeComposition : AssociativeComposition (λ _ _ → lzero) Dependency (λ _ _ → _＝_)
  AssociativeComposition.⨾-associative associativeComposition {f = Hom-sc} {g = ()} {h = h}
  AssociativeComposition.⨾-associative associativeComposition {f = Hom-tg} {g = ()} {h = h}
  AssociativeComposition.⨾-associative associativeComposition {f = Eq-lhs} {g = Hom-sc} {h = ()}
  AssociativeComposition.⨾-associative associativeComposition {f = Eq-lhs} {g = Hom-tg} {h = ()}
  AssociativeComposition.⨾-associative associativeComposition {f = Eq-rhs} {g = Hom-sc} {h = ()}
  AssociativeComposition.⨾-associative associativeComposition {f = Eq-rhs} {g = Hom-tg} {h = ()}
  AssociativeComposition.⨾-associative associativeComposition {f = Eq-sc} {g = ()} {h = h}
  AssociativeComposition.⨾-associative associativeComposition {f = Eq-tg} {g = ()} {h = h}

  semicategorical : Semicategorical 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Judgment) (λ _ _ → lzero) Dependency (λ _ _ → _＝_)
  semicategorical = record {}

CategorySort : Semicategory lzero lzero
CategorySort = asSemicategory (λ _ → Judgment) Dependency ★

accessibleOb : Accessible 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Judgment) (λ x y → Dependency y x) Ob
accessibleOb = Accessible.accessible λ { Ob () ; Hom () ; Eq () }

accessibleHom : Accessible 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Judgment) (λ x y → Dependency y x) Hom
accessibleHom = Accessible.accessible λ { Ob Hom-sc → accessibleOb ; Ob Hom-tg → accessibleOb ; Hom () ; Eq () }

accessibleEq : Accessible 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Judgment) (λ x y → Dependency y x) Eq
accessibleEq = Accessible.accessible λ { Ob Eq-sc → accessibleOb ; Ob Eq-tg → accessibleOb ; Hom Eq-lhs → accessibleHom ; Hom Eq-rhs → accessibleHom ; Eq () }

accessible : (x : Judgment) → Accessible 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Judgment) (λ x y → Dependency y x) x
accessible Ob = accessibleOb
accessible Hom = accessibleHom
accessible Eq = accessibleEq

instance
  wellfounded : Wellfounded 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Judgment) (λ x y → Dependency y x)
  wellfounded = Wellfounded.wellfounded accessible

CategoryDSV : DependentSortVocabulary
DependentSortVocabulary.sort CategoryDSV = CategorySort
DependentSortVocabulary.wellfoundedness CategoryDSV = Wellfounded.atLevel ★


-- Sequents

-- x : Ob ⊢ id : Hom x x
data id-onObjects : Judgment → Type lzero where
  x : id-onObjects Ob

idSequent : ⦃ _ : FunExt ⦄ → Sequent CategorySort
context idSequent =
  record
    { onObjects = id-onObjects
    ; semifunctorial = record
        { mappable = record { map = onMorphisms }
        ; preservesComposition = record { preserves-composition = preservesComposition } } }
  where
    onMorphisms : ∀ {j j'} → Dependency j j' → id-onObjects j → id-onObjects j'
    onMorphisms () x

    preservesComposition~ : ∀ {j j' j''} (f : Dependency j j') (g : Dependency j' j'')
                          → onMorphisms (g ∙ f) ~ onMorphisms g ∙ onMorphisms f
    preservesComposition~ () _ x

    preservesComposition : ∀ {j j' j''} (f : Dependency j j') (g : Dependency j' j'')
                         → onMorphisms (g ∙ f) ＝ onMorphisms g ∙ onMorphisms f
    preservesComposition f g = funExt (preservesComposition~ f g)

judgmentForm idSequent = Hom
arguments idSequent = 
  record
    { component = component
    ; natural = record
        { naturality = natural } }
  where
    component : (j : Judgment) → SemiCoYoneda CategorySort Hom ⟨ j ⟩ → context idSequent ⟨ j ⟩
    component Ob Hom-sc = x
    component Ob Hom-tg = x

    natural~ : ∀ {j j'} (d : Dependency j j')
             → context idSequent ⟨ d ⟩ ∙ component j ~ component j' ∙ SemiCoYoneda CategorySort Hom ⟨ d ⟩
    natural~ () Hom-sc
    natural~ () Hom-tg

    natural : ∀ {j j'} (d : Dependency j j')
            → context idSequent ⟨ d ⟩ ∙ component j ＝ component j' ∙ SemiCoYoneda CategorySort Hom ⟨ d ⟩
    natural = funExt ∘ natural~

-- ⊢ t : Ob
tSequent : ⦃ _ : FunExt ⦄ → Sequent CategorySort
context tSequent =
  record
    { onObjects = λ j → 𝟘
    ; semifunctorial = record
        { mappable = record { map = λ f () }
        ; preservesComposition = record { preserves-composition = λ f g → refl } } }
judgmentForm tSequent = Ob
arguments tSequent =
  record
    { component = λ j ()
    ; natural = record
        { naturality = λ f → refl } }

-- x : Ob, f g : Hom x t ⊢ f = g
data tEq-onObjects : Judgment → Type lzero where
  x : tEq-onObjects Ob
  t : tEq-onObjects Ob
  f : tEq-onObjects Hom
  g : tEq-onObjects Hom

tEqSequent : ⦃ _ : FunExt ⦄ → Sequent CategorySort
context tEqSequent =
  record
    { onObjects = tEq-onObjects
    ; semifunctorial = record
        { mappable = record { map = onMorphisms }
        ; preservesComposition = record { preserves-composition = preservesComposition } } }
  where
    onMorphisms : ∀ {j j'} → Dependency j j' → tEq-onObjects j → tEq-onObjects j'
    onMorphisms Hom-sc f = x
    onMorphisms Hom-tg f = t
    onMorphisms Hom-sc g = x
    onMorphisms Hom-tg g = t

    preservesComposition~ : ∀ {j j' j''} (f : Dependency j j') (g : Dependency j' j'')
                          → onMorphisms (g ∙ f) ~ onMorphisms g ∙ onMorphisms f
    preservesComposition~ Hom-sc ()
    preservesComposition~ Hom-tg ()

    preservesComposition : ∀ {j j' j''} (f : Dependency j j') (g : Dependency j' j'')
                         → onMorphisms (g ∙ f) ＝ onMorphisms g ∙ onMorphisms f
    preservesComposition α β = funExt (preservesComposition~ α β)
judgmentForm tEqSequent = Eq
arguments tEqSequent = 
  record
    { component = component
    ; natural = record
        { naturality = natural } }
  where
    component : (j : Judgment) → SemiCoYoneda CategorySort Eq ⟨ j ⟩ → context tEqSequent ⟨ j ⟩
    component Ob Eq-sc = x
    component Ob Eq-tg = t
    component Hom Eq-lhs = f
    component Hom Eq-rhs = g

    natural~ : ∀ {j j'} (d : Dependency j j')
             → context tEqSequent ⟨ d ⟩ ∙ component j ~ component j' ∙ SemiCoYoneda CategorySort Eq ⟨ d ⟩
    natural~ Hom-sc Eq-lhs = refl
    natural~ Hom-sc Eq-rhs = refl
    natural~ Hom-tg Eq-lhs = refl
    natural~ Hom-tg Eq-rhs = refl

    natural : ∀ {j j'} (d : Dependency j j')
            → context tEqSequent ⟨ d ⟩ ∙ component j ＝ component j' ∙ SemiCoYoneda CategorySort Eq ⟨ d ⟩
    natural = funExt ∘ natural~
