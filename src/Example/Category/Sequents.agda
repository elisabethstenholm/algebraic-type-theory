module Example.Category.Sequents where

open import Prelude
open import Axioms
open import Homotopy.SetQuotient
open import Structure.Associativity
open import Structure.Composable
import Structure.Wellfounded as Wellfounded
open Wellfounded using (Wellfounded)
import Structure.Accessible as Accessible
open Accessible using (Accessible)
open import Algebra.Wild.Semi
open Semicategory
open import Homotopy.StructuredType

open import DependentSortVocabulary hiding (Judgment; JudgmentDependency)
open import Context
open import Context.Morphism
open import Context.Extension
open import Context.ExtensionMorphism
open import Sequent
open import Sequent.Morphism
open Sequent.Sequent
open import SequentStructure
open import SequentDependencyStructure

open import Example.Category.DependentSortVocabulary

-- Sequents

-- =============== Identity homomorphism intro ===============
-- x : Ob ⊢ id : Hom x x

data id-onObjects-Type : Judgment → Type lzero where
  x : id-onObjects-Type Ob

id-onObjects-isSet : (j : Judgment) → isSet (id-onObjects-Type j)
id-onObjects-isSet j = ofLevel (λ x y → fromAllEqual (allEq x y))
  where
    allEq : (y z : id-onObjects-Type j) (p q : y ＝ z) → p ＝ q
    allEq x x refl refl = refl

id-onObjects : Judgment → hSet lzero
id-onObjects j = id-onObjects-Type j has-level id-onObjects-isSet j

idSequent : ⦃ _ : FunExt ⦄ → Sequent CategoryDSV lzero
context idSequent =
  record
    { semifunctor = record
      { onObjects = id-onObjects
      ; semifunctorial = record
          { mappable = record { map = onMorphisms }
          ; preservesComposition = record { preserves-composition = preservesComposition } } } }
  where
    onMorphisms : ∀ {j j'} → JudgmentDependency j j' → ⌞ id-onObjects j ⌟ → ⌞ id-onObjects j' ⌟
    onMorphisms () x

    preservesComposition~ : ∀ {j j' j''} (f : JudgmentDependency j j') (g : JudgmentDependency j' j'')
                          → onMorphisms (g ∙ f) ~ onMorphisms g ∘ onMorphisms f
    preservesComposition~ () _ x

    preservesComposition : ∀ {j j' j''} (f : JudgmentDependency j j') (g : JudgmentDependency j' j'')
                         → onMorphisms (g ∙ f) ＝ onMorphisms g ∘ onMorphisms f
    preservesComposition f g = funExt (preservesComposition~ f g)
extensionOrCollapse idSequent = extend
  record
    { judgmentForm = Hom
    ; arguments =  record
      { component = component
      ; natural = natural } }
  where
    component : (j : Judgment) → JudgmentDependency Hom j → ⌞ id-onObjects j ⌟
    component Ob Hom-sc = x
    component Ob Hom-tg = x

    natural~ : ∀ {j j'} (d : JudgmentDependency j j')
             → context idSequent ⟨ d ⟩ ∘ component j ~ component j' ∘ 𝒴 {𝒥 = CategoryDSV} Hom ⟨ d ⟩
    natural~ () Hom-sc
    natural~ () Hom-tg

    natural : ∀ {j j'} (d : JudgmentDependency j j')
            → context idSequent ⟨ d ⟩ ∘ component j ＝ component j' ∘ 𝒴 {𝒥 = CategoryDSV} Hom ⟨ d ⟩
    natural = funExt ∘ natural~


-- =================== Terminal object intro ===================
-- ⊢ t : Ob

tSequent : ⦃ _ : FunExt ⦄ → Sequent CategoryDSV lzero
context tSequent = emptyContext CategoryDSV lzero
extensionOrCollapse tSequent = extend
  record
    { judgmentForm = Ob
    ; arguments = record
        { component = λ j ()
        ; natural = λ f → refl } }



-- ===================== Equality of homomorphisms into terminal object =================
-- x : Ob, f g : Hom x t ⊢ f = g

data tEq-onObjects-Type : Judgment → Type lzero where
  x : tEq-onObjects-Type Ob
  t : tEq-onObjects-Type Ob
  f : tEq-onObjects-Type Hom
  g : tEq-onObjects-Type Hom

tEq-onObjects-isSet : (j : Judgment) → isSet (tEq-onObjects-Type j)
tEq-onObjects-isSet j = ofLevel (λ y z → fromAllEqual (allEq y z))
  where
    allEq : (y z : tEq-onObjects-Type j) (p q : y ＝ z) → p ＝ q
    allEq x x refl refl = refl
    allEq t t refl refl = refl
    allEq f f refl refl = refl
    allEq g g refl refl = refl

tEq-onObjects : Judgment → hSet lzero
tEq-onObjects j = tEq-onObjects-Type j has-level tEq-onObjects-isSet j

tEqSequent : ⦃ _ : FunExt ⦄ → Sequent CategoryDSV lzero
context tEqSequent =
  record
    { semifunctor = record
      { onObjects = tEq-onObjects
      ; semifunctorial = record
          { mappable = record { map = onMorphisms }
          ; preservesComposition = record { preserves-composition = preservesComposition } } } }
  where
    onMorphisms : ∀ {j j'} → JudgmentDependency j j' → ⌞ tEq-onObjects j ⌟ → ⌞ tEq-onObjects j' ⌟
    onMorphisms Hom-sc f = x
    onMorphisms Hom-tg f = t
    onMorphisms Hom-sc g = x
    onMorphisms Hom-tg g = t

    preservesComposition~ : ∀ {j j' j''} (f : JudgmentDependency j j') (g : JudgmentDependency j' j'')
                          → onMorphisms (g ∙ f) ~ onMorphisms g ∘ onMorphisms f
    preservesComposition~ Hom-sc ()
    preservesComposition~ Hom-tg ()

    preservesComposition : ∀ {j j' j''} (f : JudgmentDependency j j') (g : JudgmentDependency j' j'')
                         → onMorphisms (g ∙ f) ＝ onMorphisms g ∘ onMorphisms f
    preservesComposition α β = funExt (preservesComposition~ α β)
extensionOrCollapse tEqSequent = collapse
  record
    { judgmentForm = Hom
    ; arguments = record
        { component = component
        ; natural = funExt ∘ natural~ } }
  where
    component : (j : Judgment)
              → JudgmentDependency Hom j + ((j ＝ Hom) + (j ＝ Hom))
              → ⌞ tEq-onObjects j ⌟
    component Ob (inl Hom-sc) = x
    component Ob (inl Hom-tg) = t
    component Ob (inr (inl ()))
    component Ob (inr (inr ()))
    component Hom (inr (inl refl)) = f
    component Hom (inr (inr refl)) = g

    natural~ : ∀ {j j'} (d : JudgmentDependency j j')
             → context tEqSequent ⟨ d ⟩ ∘ component j ~ component j' ∘ 𝒴⁺⁺ {𝒥 = CategoryDSV} Hom ⟨ d ⟩
    natural~ Hom-sc (inr (inl refl)) = refl
    natural~ Hom-sc (inr (inr refl)) = refl
    natural~ Hom-tg (inr (inl refl)) = refl
    natural~ Hom-tg (inr (inr refl)) = refl

tSequent⇒tEqSequent : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄ → SequentMorphism tSequent tEqSequent
tSequent⇒tEqSequent =
  record { sequentMorphism = →⋊ tEqSequent ∙ intoTEqContext }
  where
    intoTEqContext : (context tSequent ⋊ extensionOrCollapse tSequent) ⇒ context tEqSequent
    intoTEqContext =
      record
        { component = component
        ; natural = funExt ∘ natural }
      where
        component : (j : Judgment)
                  → ⌞ (context tSequent ⋊ extensionOrCollapse tSequent) ⟨ j ⟩ ⌟
                  → ⌞ tEq-onObjects j ⌟
        component Ob (inr refl) = t

        natural : {j₀ j₁ : Judgment} → (d : JudgmentDependency j₀ j₁)
                → context tEqSequent ⟨ d ⟩ ∘ component j₀
                  ~ component j₁ ∘ (context tSequent ⋊ extensionOrCollapse tSequent) ⟨ d ⟩
        natural Hom-sc (inl ())
        natural Hom-sc (inr ())
        natural Hom-tg (inl ())
        natural Hom-tg (inr ())


-- =================== The full sequent structure ==================

data Operation : Type lzero where
  Id-intro : Operation
  T-intro  : Operation
  THom-eq  : Operation

data OperationDependency : (o o' : Operation) → Type lzero where
  THom-eq-tg : OperationDependency THom-eq T-intro

instance
  composableOperation : Composable 𝟙 (λ _ → Operation) OperationDependency
  Composable.composition composableOperation THom-eq-tg ()

  associativeCompositionOperation : AssociativeComposition OperationDependency (λ _ _ → _＝_)
  AssociativeComposition.⨾-associative associativeCompositionOperation {f = THom-eq-tg} {g = ()} {h = h}

  semicategoricalOperation : Semicategorical 𝟙 (λ _ → Operation) OperationDependency (λ _ _ → _＝_)
  semicategoricalOperation = record {}

OperationSemicategory : Semicategory lzero lzero
OperationSemicategory = asSemicategory (λ _ → Operation) OperationDependency ★

OperationSemifunctor : ⦃ _ : FunExt ⦄
                     → ⦃ _ : AllSetQuotients ⦄
                     → Semifunctor (OperationSemicategory ᵒᵖ) (SequentSemicategory CategoryDSV lzero)
OperationSemifunctor = 
  record
    { onObjects = onObjects
    ; semifunctorial = record
        { mappable = record
            { map = onMorphisms }
        ; preservesComposition = record
            { preserves-composition = preservesComposition } } }
  where
    onObjects : (o : Operation) → Sequent CategoryDSV lzero
    onObjects Id-intro = idSequent
    onObjects T-intro = tSequent
    onObjects THom-eq = tEqSequent

    onMorphisms : {o₀ o₁ : Operation} → OperationDependency o₁ o₀ → SequentMorphism (onObjects o₀) (onObjects o₁)
    onMorphisms THom-eq-tg = tSequent⇒tEqSequent

    preservesComposition : {o₀ o₁ o₂ : Operation} (d₀ : OperationDependency o₁ o₀) (d₁ : OperationDependency o₂ o₁)
                         → onMorphisms (d₀ ∙ d₁) ＝ onMorphisms d₁ ∙ onMorphisms d₀
    preservesComposition THom-eq-tg ()


