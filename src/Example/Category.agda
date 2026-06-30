module Example.Category where

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

open import DependentSortVocabulary

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
DependentSortVocabulary.wellfounded CategoryDSV = Wellfounded.atLevel ★
