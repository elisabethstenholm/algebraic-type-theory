module DependentSortVocabulary where

open import Prelude
open import Homotopy.Levels
open import Homotopy.StructuredType
open import Algebra.Wild.Semi
open Semicategory.Semicategory

record DependentSortVocabulary
  {o a : Level}
  : Type (lsuc (o ⊔ a)) where
  constructor mkDependentSortVocabulary
  field
    semicategory : Semicategory o a
    judgmentForms-isSet : isSet (SemicategoryProjections.Ob semicategory)
    judgmentDependencies-isSet : {j₀ j₁ : SemicategoryProjections.Ob semicategory}
                               → isSet (SemicategoryProjections.Hom semicategory j₀ j₁)
open DependentSortVocabulary public

Judgment : {o a : Level} → DependentSortVocabulary {o} {a} → hSet o
Judgment 𝒥 = Ob (semicategory 𝒥) has-level judgmentForms-isSet 𝒥

JudgmentDependency : {o a : Level} (𝒥 : DependentSortVocabulary {o} {a})
                   → ⌞ Judgment 𝒥 ⌟ → ⌞ Judgment 𝒥 ⌟ → hSet a
JudgmentDependency 𝒥 j₀ j₁ =
  Hom (semicategory 𝒥) j₀ j₁ has-level judgmentDependencies-isSet 𝒥

judgmentPaths-isSet : {o a : Level} (𝒥 : DependentSortVocabulary {o} {a})
                    → {j₀ j₁ : ⌞ Judgment 𝒥 ⌟} → isSet (j₀ ＝ j₁)
judgmentPaths-isSet 𝒥 {j₀} {j₁} =
  raise-level (pathLevel ⦃ judgmentForms-isSet 𝒥 ⦄ j₀ j₁)

JudgmentPath : {o a : Level} (𝒥 : DependentSortVocabulary {o} {a})
             → ⌞ Judgment 𝒥 ⌟ → ⌞ Judgment 𝒥 ⌟ → hSet o
JudgmentPath 𝒥 j₀ j₁ = (j₀ ＝ j₁) has-level judgmentPaths-isSet 𝒥

syntax JudgmentPath 𝒥 j₀ j₁ = j₀ ＝[ 𝒥 ] j₁
