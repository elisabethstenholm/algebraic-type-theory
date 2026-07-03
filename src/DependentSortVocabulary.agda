module DependentSortVocabulary where

open import Foundation.Base
import Foundation.Structure.Wild.Semicategory as Semicategory
open Semicategory using (Semicategory)
import Foundation.Structure.Wellfounded as Wellfounded

-- A dependent sort vocabulary is a (usually finite) wellfounded semicategory

record DependentSortVocabulary
  {o a : Level}
  : Type (lsuc (o ⊔ a)) where
  constructor dependentSortVocabulary
  field
    sort : Semicategory o a
    wellfoundedness : Wellfounded.Bounded (flip (Semicategory.Hom sort))

open DependentSortVocabulary public
