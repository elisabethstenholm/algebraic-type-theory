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
--    sc   lhs
--   <--   <--
-- Ob   Hom   Eq
--   <--   <--
--    tg   rhs
--
-- and the equalities: sc ∘ lhs = sc ∘ rhs and tg ∘ lhs = tg ∘ rhs

data Judgment : Type lzero where
  Ob  : Judgment
  Hom : Judgment
  Eq  : Judgment

data JudgmentDependency : (j j' : Judgment) → Type lzero where
  Hom-sc : JudgmentDependency Hom Ob
  Hom-tg : JudgmentDependency Hom Ob
  Eq-lhs : JudgmentDependency Eq Hom
  Eq-rhs : JudgmentDependency Eq Hom
  Eq-sc  : JudgmentDependency Eq Ob
  Eq-tg  : JudgmentDependency Eq Ob

instance
  composableJudgment : Composable 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Judgment) JudgmentDependency
  Composable.composition composableJudgment Hom-sc ()
  Composable.composition composableJudgment Hom-tg ()
  Composable.composition composableJudgment Eq-lhs Hom-sc = Eq-sc
  Composable.composition composableJudgment Eq-lhs Hom-tg = Eq-tg
  Composable.composition composableJudgment Eq-rhs Hom-sc = Eq-sc
  Composable.composition composableJudgment Eq-rhs Hom-tg = Eq-tg
  Composable.composition composableJudgment Eq-sc ()
  Composable.composition composableJudgment Eq-tg ()

  associativeCompositionJudgment : AssociativeComposition (λ _ _ → lzero) JudgmentDependency (λ _ _ → _＝_)
  AssociativeComposition.⨾-associative associativeCompositionJudgment {f = Hom-sc} {g = ()} {h = h}
  AssociativeComposition.⨾-associative associativeCompositionJudgment {f = Hom-tg} {g = ()} {h = h}
  AssociativeComposition.⨾-associative associativeCompositionJudgment {f = Eq-lhs} {g = Hom-sc} {h = ()}
  AssociativeComposition.⨾-associative associativeCompositionJudgment {f = Eq-lhs} {g = Hom-tg} {h = ()}
  AssociativeComposition.⨾-associative associativeCompositionJudgment {f = Eq-rhs} {g = Hom-sc} {h = ()}
  AssociativeComposition.⨾-associative associativeCompositionJudgment {f = Eq-rhs} {g = Hom-tg} {h = ()}
  AssociativeComposition.⨾-associative associativeCompositionJudgment {f = Eq-sc} {g = ()} {h = h}
  AssociativeComposition.⨾-associative associativeCompositionJudgment {f = Eq-tg} {g = ()} {h = h}

  semicategoricalJudgment : Semicategorical 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Judgment) (λ _ _ → lzero) JudgmentDependency (λ _ _ → _＝_)
  semicategoricalJudgment = record {}

CategorySort : Semicategory lzero lzero
CategorySort = asSemicategory (λ _ → Judgment) JudgmentDependency ★

accessibleOb : Accessible 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Judgment) (λ x y → JudgmentDependency y x) Ob
accessibleOb = Accessible.accessible λ { Ob () ; Hom () ; Eq () }

accessibleHom : Accessible 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Judgment) (λ x y → JudgmentDependency y x) Hom
accessibleHom = Accessible.accessible λ { Ob Hom-sc → accessibleOb ; Ob Hom-tg → accessibleOb ; Hom () ; Eq () }

accessibleEq : Accessible 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Judgment) (λ x y → JudgmentDependency y x) Eq
accessibleEq = Accessible.accessible λ { Ob Eq-sc → accessibleOb ; Ob Eq-tg → accessibleOb ; Hom Eq-lhs → accessibleHom ; Hom Eq-rhs → accessibleHom ; Eq () }

accessible : (x : Judgment) → Accessible 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Judgment) (λ x y → JudgmentDependency y x) x
accessible Ob = accessibleOb
accessible Hom = accessibleHom
accessible Eq = accessibleEq

instance
  wellfoundedCategory : Wellfounded 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Judgment) (λ x y → JudgmentDependency y x)
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
extension idSequent =
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
extension tSequent =
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
extension tEqSequent =
  record
    { judgmentForm = Eq
    ; arguments = record
        { component = component
        ; natural = natural } }
  where
    component : (j : Judgment) → SemiCoYoneda CategorySort Eq ⟨ j ⟩ → context tEqSequent ⟨ j ⟩
    component Ob Eq-sc = x
    component Ob Eq-tg = t
    component Hom Eq-lhs = f
    component Hom Eq-rhs = g

    natural~ : ∀ {j j'} (d : JudgmentDependency j j')
             → context tEqSequent ⟨ d ⟩ ∙ component j ~ component j' ∙ SemiCoYoneda CategorySort Eq ⟨ d ⟩
    natural~ Hom-sc Eq-lhs = refl
    natural~ Hom-sc Eq-rhs = refl
    natural~ Hom-tg Eq-lhs = refl
    natural~ Hom-tg Eq-rhs = refl

    natural : ∀ {j j'} (d : JudgmentDependency j j')
            → context tEqSequent ⟨ d ⟩ ∙ component j ＝ component j' ∙ SemiCoYoneda CategorySort Eq ⟨ d ⟩
    natural = funExt ∘ natural~

tSequent⇒tEqSequent : ⦃ _ : FunExt ⦄ → SequentMorphism tSequent tEqSequent
tSequent⇒tEqSequent =
  record
    { sequentMorphism = record
        { component = component
        ; natural = funExt ∘ natural } }
  where
    component : (j : Judgment)
              → context tSequent ⋊ₑ extension tSequent ⟨ j ⟩
              → context tEqSequent ⟨ j ⟩
    component Ob (inr refl) = t

    natural : {j₀ j₁ : Judgment} → (d : JudgmentDependency j₀ j₁)
            → context tEqSequent ⟨ d ⟩ ∘ component j₀ ~ component j₁ ∘ context tSequent ⋊ₑ extension tSequent ⟨ d ⟩
    natural Hom-sc (inl ())
    natural Hom-sc (inr ())
    natural Hom-tg (inl ())
    natural Hom-tg (inr ())
    natural Eq-lhs (inl ())
    natural Eq-lhs (inr ())
    natural Eq-rhs (inl ())
    natural Eq-rhs (inr ())
    natural Eq-sc (inl ())
    natural Eq-sc (inr ())
    natural Eq-tg (inl ())
    natural Eq-tg (inr ())

-- Sequent structure

data Operation : Type lzero where
  Id-intro : Operation
  T-intro  : Operation
  THom-eq  : Operation

data OperationDependency : (o o' : Operation) → Type lzero where
  THom-eq-tg : OperationDependency THom-eq T-intro

instance
  composableOperation : Composable 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Operation) OperationDependency
  Composable.composition composableOperation THom-eq-tg ()

  associativeCompositionOperation : AssociativeComposition (λ _ _ → lzero) OperationDependency (λ _ _ → _＝_)
  AssociativeComposition.⨾-associative associativeCompositionOperation {f = THom-eq-tg} {g = ()} {h = h}

  semicategoricalOperation : Semicategorical 𝟙 (λ _ → lzero) (λ _ _ → lzero) (λ _ → Operation) (λ _ _ → lzero) OperationDependency (λ _ _ → _＝_)
  semicategoricalOperation = record {}

OperationSemicategory : Semicategory lzero lzero
OperationSemicategory = asSemicategory (λ _ → Operation) OperationDependency ★

OperationSemifunctor : ⦃ _ : FunExt ⦄
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
