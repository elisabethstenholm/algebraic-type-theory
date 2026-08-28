module Example.MLTT.DependentSortVocabulary where

open import Prelude
open import Axioms
open import Structure.Associativity
open import Structure.Composable
open import Algebra.Wild.Semi
open Semicategory.Semicategory
import Structure.Wellfounded as Wellfounded
open Wellfounded using (Wellfounded)
import Structure.Accessible as Accessible
open Accessible using (Accessible)

open import Context
open import DependentSortVocabulary hiding (Judgment)

-- The dependent sort vocabulary for Martin-Löf type theory is the semicategory given by
--
--    Ty <----- El
--       typeOf
--


data Judgment : Type lzero where
  Ty   : Judgment
  El   : Judgment

data Dependency : (j j' : Judgment) → Type lzero where
  typeOf      : Dependency El Ty

instance
  composableDependency : Composable 𝟙 (λ _ → Judgment) Dependency
  Composable.composition composableDependency typeOf ()

  associativeCompositionDependency : AssociativeComposition Dependency (λ _ _ → _＝_)
  AssociativeComposition.⨾-associative associativeCompositionDependency {f = typeOf} {g = ()} {h = h}

  semicategoricalDependency : Semicategorical 𝟙 (λ _ → Judgment) Dependency (λ _ _ → _＝_)
  semicategoricalDependency = record {}

MLTTSort : Semicategory lzero lzero
MLTTSort = asSemicategory (λ _ → Judgment) Dependency ★

accessibleTy : Accessible 𝟙 (λ _ → Judgment) (λ x y → Dependency y x) Ty
accessibleTy = Accessible.accessible λ { Ty () ; El () }

accessibleEl : Accessible 𝟙 (λ _ → Judgment) (λ x y → Dependency y x) El
accessibleEl = Accessible.accessible λ { Ty typeOf → accessibleTy ; El () }

accessible : (x : Judgment) → Accessible 𝟙 (λ _ → Judgment) (λ x y → Dependency y x) x
accessible Ty = accessibleTy
accessible El = accessibleEl

instance
  wellfoundedMLTT : Wellfounded 𝟙 (λ _ → Judgment) (λ x y → Dependency y x)
  wellfoundedMLTT = Wellfounded.wellfounded accessible

judgment-isSet : isSet Judgment
judgment-isSet = ofLevel λ x y → fromAllEqual (allEq x y)
  where
    allEq : (x y : Judgment) (p q : x ＝ y) → p ＝ q
    allEq Ty Ty refl refl = refl
    allEq Ty El () q
    allEq El Ty () q
    allEq El El refl refl = refl

dependency-isSet : {j j' : Judgment} → isSet (Dependency j j')
dependency-isSet {j} {j'} = ofLevel (λ x y → fromAllEqual (allEq x y))
  where
    allEq : (x y : Dependency j j') (p q : x ＝ y) → p ＝ q
    allEq typeOf typeOf refl refl = refl

MLTTDSV : DependentSortVocabulary lzero lzero
MLTTDSV =
  record
    { semicategory = MLTTSort
    ; judgmentForms-isSet = judgment-isSet
    ; judgmentDependencies-isSet = dependency-isSet }
