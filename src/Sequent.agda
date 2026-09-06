module Sequent where

open import Prelude
open import Axioms
open import Homotopy.SetQuotient
open import Structure.Associativity
open import Structure.Composable
open import Structure.Identity
open import Structure.Reasoning
open import Homotopy.StructuredType
open import Syntax.Arrowable
open import Algebra.Wild.Semi
open Semicategory.Semicategory

open import DependentSortVocabulary
open import Context
open import Context.Morphism
open import Context.Extension

-- ================ Sequents ===============

record Sequent
  ⦃ _ : FunExt ⦄
  {o a : Level}
  (𝒥 : DependentSortVocabulary o a)
  (i : Level)
  : Type (o ⊔ a ⊔ lsuc i) where
  constructor mkSequent
  field
    context : Context 𝒥 i
    extensionOrCollapse : ExtensionOrCollapse context
open Sequent

module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a i : Level} {𝒥 : DependentSortVocabulary o a} where

  extendedContext : Sequent 𝒥 i → Context 𝒥 (o ⊔ i)
  extendedContext s = Sequent.context s ⋊ Sequent.extensionOrCollapse s

  ⋊ₑₛ : Sequent 𝒥 i → Context 𝒥 (o ⊔ i)
  ⋊ₑₛ = extendedContext

  →⋊ : (s : Sequent 𝒥 i) → Sequent.context s ⇒ extendedContext s
  →⋊ (mkSequent context (extend x)) = ι
  →⋊ (mkSequent context (collapse x)) = σ


