module WellfoundedSemicategory where

open import Foundation
open import Algebra.Wild.Semi
open Semicategory.Semicategory
import Structure.Wellfounded as Wellfounded

record WellfoundedSemicategory
  {o a : Level}
  : Type (lsuc (o ⊔ a)) where
  constructor wellfoundedSemicategory
  field
    semicategory : Semicategory o a
    wellfounded : Wellfounded.Bounded (flip (Hom semicategory))

open WellfoundedSemicategory public
