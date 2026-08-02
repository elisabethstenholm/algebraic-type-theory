module Rule where

open import Foundation
open import Foundation.Axioms
open import Foundation.Structure.Wild.Semi

open import SequentStructure
open import SequentStructureExtension

record Rule
  ⦃ _ : FunExt ⦄
  ⦃ _ : AllSetQuotients ⦄
  {o a : Level}
  (𝒥 : Semicategory o a)
  (so sa i : Level)
  : Type (o ⊔ a ⊔ lsuc so ⊔ lsuc sa ⊔ lsuc i) where
  constructor mkRule
  field
    premises : SequentStructure 𝒥 so sa i
    extension : SequentStructureExtension premises

