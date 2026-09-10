module Example.Category.DependentSortVocabulary where

open import Prelude
open import Structure.Associativity
open import Structure.Composable
import Structure.Wellfounded as Wellfounded
open Wellfounded using (Wellfounded)
import Structure.Accessible as Accessible
open Accessible using (Accessible)
open import Algebra.Wild.Semicategory
open import Structure.Semicategorical using (Semicategorical)

open import DependentSortVocabulary hiding (Judgment; JudgmentDependency)

-- The dependent sort vocabulary for categories is the semicategory given by
--
--    sc
--   <--
-- Ob   Hom
--   <--
--    tg


data Judgment : Type lzero where
  Ob  : Judgment
  Hom : Judgment

data JudgmentDependency : (j j' : Judgment) → Type lzero where
  Hom-sc : JudgmentDependency Hom Ob
  Hom-tg : JudgmentDependency Hom Ob

instance
  composableJudgment : Composable 𝟙 (λ _ → Judgment) JudgmentDependency
  Composable.composition composableJudgment Hom-sc ()
  Composable.composition composableJudgment Hom-tg ()

  associativeCompositionJudgment : AssociativeComposition JudgmentDependency (λ _ _ → _＝_)
  AssociativeComposition.⨾-associative associativeCompositionJudgment {f = Hom-sc} {g = ()} {h = h}
  AssociativeComposition.⨾-associative associativeCompositionJudgment {f = Hom-tg} {g = ()} {h = h}

  semicategoricalJudgment : Semicategorical 𝟙 (λ _ → Judgment) JudgmentDependency (λ _ _ → _＝_)
  semicategoricalJudgment = record {}

CategorySort : Semicategory lzero lzero
CategorySort = asSemicategory (λ _ → Judgment) JudgmentDependency ★

accessibleOb : Accessible 𝟙 (λ _ → Judgment) (λ x y → JudgmentDependency y x) Ob
accessibleOb = Accessible.accessible λ { Ob () ; Hom () }

accessibleHom : Accessible 𝟙 (λ _ → Judgment) (λ x y → JudgmentDependency y x) Hom
accessibleHom = Accessible.accessible λ { Ob Hom-sc → accessibleOb ; Ob Hom-tg → accessibleOb ; Hom () }

accessible : (x : Judgment) → Accessible 𝟙 (λ _ → Judgment) (λ x y → JudgmentDependency y x) x
accessible Ob = accessibleOb
accessible Hom = accessibleHom

instance
  wellfoundedCategory : Wellfounded 𝟙 (λ _ → Judgment) (λ x y → JudgmentDependency y x)
  wellfoundedCategory = Wellfounded.wellfounded accessible

judgment-isSet : isSet Judgment
judgment-isSet = ofLevel λ x y → fromAllEqual (allEq x y)
  where
    allEq : (x y : Judgment) (p q : x ＝ y) → p ＝ q
    allEq Ob Ob refl refl = refl
    allEq Ob Hom () q
    allEq Hom Ob () q
    allEq Hom Hom refl refl = refl

judgmentDependency-isSet : {j j' : Judgment} → isSet (JudgmentDependency j j')
judgmentDependency-isSet {j} {j'} = ofLevel (λ x y → fromAllEqual (allEq x y))
  where
    allEq : (x y : JudgmentDependency j j') (p q : x ＝ y) → p ＝ q
    allEq Hom-sc Hom-sc refl refl = refl
    allEq Hom-sc Hom-tg () q
    allEq Hom-tg Hom-sc () q
    allEq Hom-tg Hom-tg refl refl = refl

CategoryDSV : DependentSortVocabulary lzero lzero
CategoryDSV =
  record
    { semicategory = CategorySort
    ; judgmentForms-isSet = judgment-isSet
    ; judgmentDependencies-isSet = judgmentDependency-isSet }
