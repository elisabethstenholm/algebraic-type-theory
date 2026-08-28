module Example.MLTT.Rules.UnitType where

open import Prelude
open import Axioms
open import Algebra.Wild.Semi
open Semicategory.Semicategory
open import Algebra.Wild.TypeSemicategory
open import Homotopy.SetQuotient
open import Homotopy.StructuredType
open import Structure.Composable
open import Structure.Identity

open import Context
open ExtensionOrCollapse
open import ContextWithTerms
open import Rule
open import RuleMorphism
open import Sequent
open import SequentStructure
open import SequentStructureMorphism

open import Example.MLTT.Common
open import Example.MLTT.DependentSortVocabulary as MLTT
open MLTT


-- =============== Type former ================
--
--   ---------------
--     ⊢ Unit Type

unitTypeFormer : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄ → Rule MLTTDSV lzero lzero lzero
unitTypeFormer = ruleWithEmptyPremises emptyTySequent


-- =============== Introduction rule ================
--
--   ---------------
--    ⊢ unit : Unit

-- As algebraic type theory rule:
--
--    ⊢ U' ≔ Unit Ty
--  -----------------------
--   U ≔ U' Ty ⊢ unit : U

data unitIntro-onObjects-Type : MLTT.Judgment → Type lzero where
  U : unitIntro-onObjects-Type Ty

unitIntro-onObjects-isSet : (j : MLTT.Judgment) → isSet (unitIntro-onObjects-Type j)
unitIntro-onObjects-isSet j = ofLevel (λ x y → fromAllEqual (allEq x y))
  where
    allEq : (x y : unitIntro-onObjects-Type j) (p q : x ＝ y) → p ＝ q
    allEq U U refl refl = refl

unitIntro-onObjects : MLTT.Judgment → hSet lzero
unitIntro-onObjects j = unitIntro-onObjects-Type j has-level unitIntro-onObjects-isSet j

module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄ where

  unitIntro-head : Sequent MLTTDSV lzero
  unitIntro-head =
    record
      { context = record
          { semifunctor = record
              { onObjects = unitIntro-onObjects
              ; semifunctorial = record
                  { mappable = record { map = onMorphisms }
                  ; preservesComposition = record { preserves-composition = λ f g → funExt (preservesComposition~ f g) } } } }
      ; extensionOrCollapse = extend (record
          { judgmentForm = El
          ; arguments = record
              { component = component
              ; natural = funExt ∘ natural~ } }) }
    where
      onMorphisms : ∀ {j j'} → MLTT.Dependency j j' → ⌞ unitIntro-onObjects j ⌟ → ⌞ unitIntro-onObjects j' ⌟
      onMorphisms typeOf ()

      preservesComposition~ : ∀ {j j' j''} (f : MLTT.Dependency j j') (g : MLTT.Dependency j' j'')
                            → onMorphisms (g ∙ f) ~ onMorphisms g ∘ onMorphisms f
      preservesComposition~ typeOf () x

      component : (j : MLTT.Judgment) → ⌞ 𝒴 {𝒥 = MLTTDSV} El ⟨ j ⟩ ⌟ → ⌞ unitIntro-onObjects j ⌟
      component Ty typeOf = U
      component El ()

      natural~ : ∀ {j j'} (d : MLTT.Dependency j j')
               → onMorphisms d ∘ component j ~ component j' ∘ 𝒴 {𝒥 = MLTTDSV} El ⟨ d ⟩
      natural~ typeOf ()

  unitIntro-premises : SequentStructure MLTTDSV lzero lzero lzero
  unitIntro-premises = unitSequentStructure emptyTySequent lzero lzero

  unitIntro-dependency : Semifunctor (unitSemicategory lzero lzero) (TypeSemicategory lzero)
  unitIntro-dependency =
    record
      { onObjects = λ _ → Unit
      ; semifunctorial = record
          { mappable = record { map = absurd }
          ; preservesComposition = record { preserves-composition = λ () } } }

  unitIntro-premiseMorphism : ⋊ₑₛ emptyTySequent ⇒ Sequent.context unitIntro-head
  unitIntro-premiseMorphism =
    record
      { component = component
      ; natural = λ { typeOf → funExt λ { (inl ()) ; (inr ()) } } }
    where
      component : (j : MLTT.Judgment) → ⌞ ⋊ₑₛ emptyTySequent ⟨ j ⟩ ⌟ → ⌞ Sequent.context unitIntro-head ⟨ j ⟩ ⌟
      component Ty (inr refl) = U

  unitIntro : Rule MLTTDSV lzero lzero lzero
  unitIntro =
    record
      { rule = record
          { head = unitIntro-head
          ; sequentStructure = unitIntro-premises
          ; dependency = unitIntro-dependency
          ; realiseDependency = λ _ _ → unitIntro-premiseMorphism
          ; coherenceRealisation = λ { f () } } }

  unitTypeFormer⇒unitIntro-core :  ⋊ₛ unitTypeFormer ⇒ unitIntro-premises
  unitTypeFormer⇒unitIntro-core =
    record
      { onDependencies = record
          { onObjects = λ _ → ★
          ; semifunctorial = record
              { mappable = record { map = λ { {ExtendedSequentStructure.newOb} {ExtendedSequentStructure.newOb} (ExtendedSequentStructure.include ()) } }
              ; preservesComposition = record
                  { preserves-composition =
                      λ { {ExtendedSequentStructure.newOb} {ExtendedSequentStructure.newOb}
                          (ExtendedSequentStructure.include ()) } } } }
      ; dependenciesEquivalence =
          λ { ExtendedSequentStructure.newOb →
                record
                  { section = record
                      { sectionBack = λ { (_ , ()) }
                      ; isSection = λ { (_ , ()) } }
                  ; retraction = record
                      { retractionBack = λ { (_ , ()) }
                      ; isRetraction =
                          λ { (ExtendedSequentStructure.newOb , ExtendedSequentStructure.include ()) } } } }
      ; component = λ { ExtendedSequentStructure.newOb → identity }
      ; natural = λ { {ExtendedSequentStructure.newOb} {ExtendedSequentStructure.newOb}
                      (ExtendedSequentStructure.include ()) } }


  unitTypeFormer⇒unitIntro : unitTypeFormer ⇒ unitIntro
  unitTypeFormer⇒unitIntro =
    record
      { baseContext = emptyContextWithTerms MLTTDSV lzero lzero lzero
      ; ruleMorphism = addEmptyBaseContext unitTypeFormer⇒unitIntro-core }


-- ============== Elimination rule =================
--
--    ⊢ A Type  ⊢ a : A
--   --------------------------
--    x : Unit ⊢ unit-elim : A

-- As an algebraic type theory rule
--
--   ⊢ U' ≔ Unit Ty   ⊢ A Ty   A' ≔ A Ty ⊢ a : A
--  -----------------------------------------------
--    A' ≔ A Ty, U ≔ U' Ty, x : U ⊢ unit-elim : A
