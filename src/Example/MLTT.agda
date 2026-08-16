module Example.MLTT where

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

open import Data.Bool

open import Context
open import DependentSortVocabulary hiding (Judgment)
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

judgment-isSet : isSet Judgment
judgment-isSet = retract-level toBool fromBool retract Bool-isSet
  where
    toBool : Judgment → Bool {lzero}
    toBool Ty = true
    toBool El = false

    fromBool : Bool {lzero} → Judgment
    fromBool true  = Ty
    fromBool false = El

    retract : fromBool ∘ toBool ~ id
    retract Ty = refl
    retract El = refl

dependency-isSet : {j j' : Judgment} → isSet (Dependency j j')
dependency-isSet {Ty} {_}  = retract-level (λ ()) (λ ()) (λ ()) (𝟘-isLevel {lzero})
dependency-isSet {El} {Ty} = retract-level (λ _ → ★) (λ _ → typeOf) (λ { typeOf → refl }) (𝟙-isLevel {lzero})
dependency-isSet {El} {El} = retract-level (λ ()) (λ ()) (λ ()) (𝟘-isLevel {lzero})

MLTTDSV : DependentSortVocabulary
MLTTDSV =
  record
    { semicategory = MLTTSort
    ; judgmentForms-isSet = judgment-isSet
    ; judgmentDependencies-isSet = dependency-isSet }



-- ########### Rules ###########

-- ========== Unit type ========

-- Type former
--
--   ---------------
--     ⊢ Unit Type



{-

R1
--  ⊢ A Type  ⊢ B Type
-- --------------------
--   ⊢ A × B Type

The extended sequent structure

A <- AB -> B



Rule morphism from R1 to R2

Functor from semi category of R1 to semicategory of R2

  <--
A     X
  <--


R2
--    ⊢ A Type  ⊢ X Type
-- -----------------------
--    x : A ⊢ Δ : X

  ⊢ A Type  x : A ⊢ t :
--------------------------
 x : A ⊢ proj₀ (Δ x) = x

-- X -> A × A


 ⊢ A Type    X := A Type, x : X ⊢ f : A
-----------------------------------------
      X := A Type  ⊢ λ : X → X

A <- fA <- λ






 ⊢ A Type        X := A Type, a : A, b : A ⊢ a + b : A                        ⊢ 1 : A      X := A type, x : X, e := 1 : X ⊢ f := e + x : X      X := A Type ⊢ t := λ x . 1 + x : A → A

 X := A Type ⊢ λ x . x + b : A → A
---------------------------------------------------------------------------------------------------------------------------------------------------
  ⊢ λ x . 1 + x = λ x . x + 1





-}

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
