module Example.MLTT where

open import Foundation
open import Foundation.Axioms
open import Foundation.Structure.Wild.Semi
open Semicategory.Semicategory
import Foundation.Structure.Wellfounded as Wellfounded
open Wellfounded using (Wellfounded)
import Foundation.Structure.Accessible as Accessible
open Accessible using (Accessible)

open import DependentSortVocabulary
open import Sequent

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

MLTTDSV : DependentSortVocabulary
MLTTDSV = record { semicategory = MLTTSort; wellfounded = Wellfounded.atLevel ★ }


-- ########### Sequents ###########

-- ⊢ X Type

typeSequent : ⦃ _ : FunExt ⦄ → Sequent MLTTSort lzero
Sequent.context typeSequent = emptyContext MLTTSort lzero
Sequent.extensionOrCollapse typeSequent = extend
  record
    { judgmentForm = Ty
    ; arguments = record
        { component = λ j ()
        ; natural = λ f → refl } }

-- ########### Rules ###########

-- ========== Unit type ========

-- Type former
--
--   ---------------
--     ⊢ Unit Type

-- Introduction rule
--
--   ---------------
--    ⊢ unit : Unit

-- Elimination rule
--
--    ⊢ A Type  ⊢ a : A
--   --------------------------
--    x : Unit ⊢ unit-elim : A


-- ======== Sum type ==========

-- Type former
--
--    ⊢ A Type  ⊢ B Type
--   --------------------
--       ⊢ A + B Type

-- Introduction rules
--
--    ⊢ A Type  ⊢ B Type
--   ---------------------
--    x : A ⊢ inl : A + B

--    ⊢ A Type  ⊢ B Type
--   ---------------------
--    x : B ⊢ inr : A + B

-- Elimination rule
--
--    ⊢ A Type  ⊢ B Type  x : A + B ⊢ C Type
--       x : A ⊢ f : C  y : B ⊢ g : C
--   -----------------------------------------
--         x : A + B ⊢ sum-elim : C


-- ========= Natural numbers ==========

-- Type former
--
--   -------------
--    ⊢ Nat Type

-- Introduction rule
--
--   ----------------------------------
--    x : Nat + Unit ⊢ nat-intro : Nat

-- Elimination rule
--
--    x : Nat ⊢ A Type  ⊢ f₀ : A(nat-intro(inr(unit)))  x : Nat, a : A(x) ⊢ f : A(nat-intro(inl(x)))
--   -----------------------------------------------------------------------------------------------
--                                 x : Nat ⊢ nat-elim : A
