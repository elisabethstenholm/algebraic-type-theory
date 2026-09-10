module RuleStructure where

open import Prelude
open import Axioms
open import Algebra.Wild.Semicategory
open import Algebra.Wild.Semifunctor
open import Syntax.Opposable using (_ᵒᵖ)
open Semicategory
open import Homotopy.Levels
open import Homotopy.SetQuotient.Nominal

open import DependentSortVocabulary
open import Rule
open import RuleMorphism
open import RuleSemicategory

record RuleStructure
  ⦃ _ : FunExt ⦄
  ⦃ _ : Univalence ⦄
  ⦃ _ : AllSetQuotients ⦄
  {o a : Level}
  (𝒥 : DependentSortVocabulary o a)
  (ro ra so sa i : Level)
  : Type (o ⊔ a ⊔ lsuc ro ⊔ lsuc ra ⊔ lsuc so ⊔ lsuc sa ⊔ lsuc i) where
  constructor mkRuleStructure
  field
    dependency : Semicategory ro ra
    dependency-Ob-isSet : isSet (Ob dependency)
    dependency-Hom-isSet : (x y : Ob dependency) → isSet (Hom dependency x y)
    rule : Semifunctor (dependency ᵒᵖ) (RuleSemicategory 𝒥 so sa i)
