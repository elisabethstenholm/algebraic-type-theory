module DependentSortVocabulary where

open import Foundation

open import WellfoundedSemicategory public

-- A dependent sort vocabulary is a (usually finite) wellfounded semicategory

DependentSortVocabulary : {o a : Level} → Type (lsuc (o ⊔ a))
DependentSortVocabulary {o} {a} = WellfoundedSemicategory {o} {a}
