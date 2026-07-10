module Example.Category where

open import Foundation
open import Foundation.Axioms
import Foundation.Structure.Wellfounded as Wellfounded
open Wellfounded using (Wellfounded)
import Foundation.Structure.Accessible as Accessible
open Accessible using (Accessible)
open import Foundation.Structure.Wild.Semi
open Semicategory
open import Foundation.Structure.Wild.SemiYoneda

open import DependentSortVocabulary
open import Sequent
open Sequent.Sequent
open import SequentStructure

-- The dependent sort vocabulary for categories is the semicategory given by
--
--    sc
--   <--
-- Ob   Hom
--   <--
--    tg
--
-- and the equalities: sc ∘ lhs = sc ∘ rhs and tg ∘ lhs = tg ∘ rhs

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

CategoryDSV : DependentSortVocabulary
CategoryDSV = record { semicategory = CategorySort; wellfounded = Wellfounded.atLevel ★ }


-- Sequents

-- x : Ob ⊢ id : Hom x x
data id-onObjects : Judgment → Type lzero where
  x : id-onObjects Ob

idSequent : ⦃ _ : FunExt ⦄ → Sequent CategorySort lzero
context idSequent =
  record
    { semifunctor = record
      { onObjects = id-onObjects
      ; semifunctorial = record
          { mappable = record { map = onMorphisms }
          ; preservesComposition = record { preserves-composition = preservesComposition } } } }
  where
    onMorphisms : ∀ {j j'} → JudgmentDependency j j' → id-onObjects j → id-onObjects j'
    onMorphisms () x

    preservesComposition~ : ∀ {j j' j''} (f : JudgmentDependency j j') (g : JudgmentDependency j' j'')
                          → onMorphisms (g ∙ f) ~ onMorphisms g ∙ onMorphisms f
    preservesComposition~ () _ x

    preservesComposition : ∀ {j j' j''} (f : JudgmentDependency j j') (g : JudgmentDependency j' j'')
                         → onMorphisms (g ∙ f) ＝ onMorphisms g ∙ onMorphisms f
    preservesComposition f g = funExt (preservesComposition~ f g)
extensionOrCollapse idSequent = extend
  record
    { judgmentForm = Hom
    ; arguments =  record
      { component = component
      ; natural = natural } }
  where
    component : (j : Judgment) → SemiCoYoneda CategorySort Hom ⟨ j ⟩ → context idSequent ⟨ j ⟩
    component Ob Hom-sc = x
    component Ob Hom-tg = x

    natural~ : ∀ {j j'} (d : JudgmentDependency j j')
             → context idSequent ⟨ d ⟩ ∙ component j ~ component j' ∙ SemiCoYoneda CategorySort Hom ⟨ d ⟩
    natural~ () Hom-sc
    natural~ () Hom-tg

    natural : ∀ {j j'} (d : JudgmentDependency j j')
            → context idSequent ⟨ d ⟩ ∙ component j ＝ component j' ∙ SemiCoYoneda CategorySort Hom ⟨ d ⟩
    natural = funExt ∘ natural~

-- ⊢ t : Ob
tSequent : ⦃ _ : FunExt ⦄ → Sequent CategorySort lzero
context tSequent =
  record
    { semifunctor = record
      { onObjects = λ j → 𝟘
      ; semifunctorial = record
          { mappable = record { map = λ f () }
          ; preservesComposition = record { preserves-composition = λ f g → refl } } } }
extensionOrCollapse tSequent = extend
  record
    { judgmentForm = Ob
    ; arguments = record
        { component = λ j ()
        ; natural = λ f → refl } }

-- x : Ob, f g : Hom x t ⊢ f = g
data tEq-onObjects : Judgment → Type lzero where
  x : tEq-onObjects Ob
  t : tEq-onObjects Ob
  f : tEq-onObjects Hom
  g : tEq-onObjects Hom

tEqSequent : ⦃ _ : FunExt ⦄ → Sequent CategorySort lzero
context tEqSequent =
  record
    { semifunctor = record
      { onObjects = tEq-onObjects
      ; semifunctorial = record
          { mappable = record { map = onMorphisms }
          ; preservesComposition = record { preserves-composition = preservesComposition } } } }
  where
    onMorphisms : ∀ {j j'} → JudgmentDependency j j' → tEq-onObjects j → tEq-onObjects j'
    onMorphisms Hom-sc f = x
    onMorphisms Hom-tg f = t
    onMorphisms Hom-sc g = x
    onMorphisms Hom-tg g = t

    preservesComposition~ : ∀ {j j' j''} (f : JudgmentDependency j j') (g : JudgmentDependency j' j'')
                          → onMorphisms (g ∙ f) ~ onMorphisms g ∙ onMorphisms f
    preservesComposition~ Hom-sc ()
    preservesComposition~ Hom-tg ()

    preservesComposition : ∀ {j j' j''} (f : JudgmentDependency j j') (g : JudgmentDependency j' j'')
                         → onMorphisms (g ∙ f) ＝ onMorphisms g ∙ onMorphisms f
    preservesComposition α β = funExt (preservesComposition~ α β)
extensionOrCollapse tEqSequent = collapse
  record
    { judgmentForm = Hom
    ; arguments = record
        { component = component
        ; natural = funExt ∘ natural~ } }
  where
    component : (j : Judgment) → 𝒴⁺⁺ {𝒥 = CategorySort} Hom ⟨ j ⟩ → context tEqSequent ⟨ j ⟩
    component Ob (inl Hom-sc) = x
    component Ob (inl Hom-tg) = t
    component Ob (inr (inl ()))
    component Ob (inr (inr ()))
    component Hom (inr (inl refl)) = f
    component Hom (inr (inr refl)) = g

    natural~ : ∀ {j j'} (d : JudgmentDependency j j')
             → context tEqSequent ⟨ d ⟩ ∙ component j ~ component j' ∙ 𝒴⁺⁺ {𝒥 = CategorySort} Hom ⟨ d ⟩
    natural~ Hom-sc (inr (inl refl)) = refl
    natural~ Hom-sc (inr (inr refl)) = refl
    natural~ Hom-tg (inr (inl refl)) = refl
    natural~ Hom-tg (inr (inr refl)) = refl

tSequent⇒tEqSequent : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄ → SequentMorphism tSequent tEqSequent
tSequent⇒tEqSequent =
  record
    { sequentMorphism = record
        { component = component
        ; natural = funExt ∘ natural } }
  where
    component : (j : Judgment)
              → context tSequent ⋊ extensionOrCollapse tSequent ⟨ j ⟩
              → context tEqSequent ⟨ j ⟩
    component Ob (inr refl) = t

    natural : {j₀ j₁ : Judgment} → (d : JudgmentDependency j₀ j₁)
            → context tEqSequent ⟨ d ⟩ ∘ component j₀ ~ component j₁ ∘ context tSequent ⋊ extensionOrCollapse tSequent ⟨ d ⟩
    natural Hom-sc (inl ())
    natural Hom-sc (inr ())
    natural Hom-tg (inl ())
    natural Hom-tg (inr ())

-- Sequent structure

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
                     → Semifunctor (OperationSemicategory ᵒᵖ) (SequentSemicategory CategorySort lzero)
OperationSemifunctor = 
  record
    { onObjects = onObjects
    ; semifunctorial = record
        { mappable = record
            { map = onMorphisms }
        ; preservesComposition = record
            { preserves-composition = preservesComposition } } }
  where
    onObjects : (o : Operation) → Sequent CategorySort lzero
    onObjects Id-intro = idSequent
    onObjects T-intro = tSequent
    onObjects THom-eq = tEqSequent

    onMorphisms : {o₀ o₁ : Operation} → OperationDependency o₁ o₀ → SequentMorphism (onObjects o₀) (onObjects o₁)
    onMorphisms THom-eq-tg = tSequent⇒tEqSequent

    preservesComposition : {o₀ o₁ o₂ : Operation} (d₀ : OperationDependency o₁ o₀) (d₁ : OperationDependency o₂ o₁)
                         → onMorphisms (d₀ ∙ d₁) ＝ onMorphisms d₁ ∙ onMorphisms d₀
    preservesComposition THom-eq-tg ()

