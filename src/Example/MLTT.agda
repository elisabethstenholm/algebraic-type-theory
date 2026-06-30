module Example.MLTT where

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

-- The dependent sort vocabulary for Martin-Löf type theory is the semicategory given by
--
--   EqTy      EqEl
--    ||        ||
-- lhs||rhs  lhs||rhs
--    ↓↓        ↓↓
--    Ty <----- El
--       typeOf
--
--
-- and the equality: typeOf ∘ lhs = typeOf ∘ rhs

data Judgment : Type lzero where
  Ty   : Judgment
  El   : Judgment
  EqTy : Judgment
  EqEl : Judgment

data Dependency : (j j' : Judgment) → Type lzero where
  typeOf      : Dependency El Ty
  EqEl-typeOf : Dependency EqEl Ty
  EqEl-lhs    : Dependency EqEl El
  EqEl-rhs    : Dependency EqEl El
  EqTy-lhs    : Dependency EqTy Ty
  EqTy-rhs    : Dependency EqTy Ty

instance
  composable : Composable 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Judgment) Dependency
  Composable.composition composable typeOf ()
  Composable.composition composable EqEl-typeOf ()
  Composable.composition composable EqEl-lhs typeOf = EqEl-typeOf
  Composable.composition composable EqEl-rhs typeOf = EqEl-typeOf
  Composable.composition composable EqTy-lhs ()
  Composable.composition composable EqTy-rhs ()

  associativeComposition : AssociativeComposition (λ _ _ → lzero) Dependency (λ _ _ → _＝_)
  AssociativeComposition.⨾-associative associativeComposition {f = typeOf} {g = ()} {h = h}
  AssociativeComposition.⨾-associative associativeComposition {f = EqEl-typeOf} {g = ()} {h = h}
  AssociativeComposition.⨾-associative associativeComposition {f = EqEl-lhs} {g = typeOf} {h = ()}
  AssociativeComposition.⨾-associative associativeComposition {f = EqEl-rhs} {g = typeOf} {h = ()}
  AssociativeComposition.⨾-associative associativeComposition {f = EqTy-lhs} {g = ()} {h = h}
  AssociativeComposition.⨾-associative associativeComposition {f = EqTy-rhs} {g = ()} {h = h}

  semicategorical : Semicategorical 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Judgment) (λ _ _ → lzero) Dependency (λ _ _ → _＝_)
  semicategorical = record {}

MLTTSort : Semicategory lzero lzero
MLTTSort = asSemicategory (λ _ → Judgment) Dependency ★

accessibleTy : Accessible 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Judgment) (λ x y → Dependency y x) Ty
accessibleTy = Accessible.accessible λ { Ty () ; El () ; EqTy () ; EqEl () }

accessibleEl : Accessible 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Judgment) (λ x y → Dependency y x) El
accessibleEl = Accessible.accessible λ { Ty typeOf → accessibleTy ; El () ; EqTy () ; EqEl () }

accessibleEqTy : Accessible 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Judgment) (λ x y → Dependency y x) EqTy
accessibleEqTy = Accessible.accessible λ { Ty EqTy-lhs → accessibleTy ; Ty EqTy-rhs → accessibleTy ; El () ; EqTy () ; EqEl () }

accessibleEqEl : Accessible 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Judgment) (λ x y → Dependency y x) EqEl
accessibleEqEl = Accessible.accessible λ { Ty EqEl-typeOf → accessibleTy ; El EqEl-lhs → accessibleEl ; El EqEl-rhs → accessibleEl ; EqTy () ; EqEl () }

accessible : (x : Judgment) → Accessible 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Judgment) (λ x y → Dependency y x) x
accessible Ty = accessibleTy
accessible El = accessibleEl
accessible EqTy = accessibleEqTy
accessible EqEl = accessibleEqEl

instance
  wellfounded : Wellfounded 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Judgment) (λ x y → Dependency y x)
  wellfounded = Wellfounded.wellfounded accessible

MLTTDSV : DependentSortVocabulary
DependentSortVocabulary.sort MLTTDSV = MLTTSort
DependentSortVocabulary.wellfounded MLTTDSV = Wellfounded.atLevel ★
