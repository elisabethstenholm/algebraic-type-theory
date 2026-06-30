module Sequent where

open import Foundation.Primitive
import Foundation.Structure.Wild.Semicategory as Semicategory
open Semicategory using (Semicategory)
import Foundation.Structure.Wild.Semifunctor as Semifunctor
open Semifunctor using (Semifunctor)
open import Foundation.HomotopyLevels.Semicategorical
open import Foundation.Structure.Wild.SeminaturalTransformation
open import Foundation.StructuredType

open import Judgment
open DependentSortVocabulary


record Sequent
  {o a : Level}
  (𝒥 : DependentSortVocabulary {o} {a})
  (i : Level)
  : Type (lsuc (o ⊔ a ⊔ i)) where
  constructor sequent
  field
    context : Semifunctor (sort 𝒥) (hSet-Semicategory i)
    judgmentForm : Semicategory.Ob (sort 𝒥)
    arguments : {!!} ⟹ context
