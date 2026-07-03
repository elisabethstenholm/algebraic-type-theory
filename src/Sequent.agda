module Sequent where

open import Foundation.Axioms
open import Foundation
import Foundation.Structure.Wild.Semicategory as Semicategory
open Semicategory using (Semicategory)
open Semicategory.Semicategory
import Foundation.Structure.Wild.Semifunctor as Semifunctor
open Semifunctor using (Semifunctor)
import Foundation.Structure.Semifunctorial as Semifunctorial
open import Foundation.HomotopyLevels.Semicategorical
open import Foundation.Structure.Wild.SeminaturalTransformation
open import Foundation.StructuredType
open import Foundation.Structure.Associativity using (∙-associative)
open import Foundation.Structure.Wild.SemiYoneda
open import Foundation.Structure.Wild.TypeSemicategory
open import Foundation.Structure.PreservesComposition
  using (PreservesComposition; preserves-composition)
open import Foundation.Structure.Semifunctorial using (Semifunctorial)
import Foundation.Structure.Wild.SeminaturalTransformation as SeminaturalTransformation
open Foundation.Structure.Wild.SeminaturalTransformation using (natural; _⟹_)
import Foundation.Structure.Natural as Natural
open import Foundation.Structure.Natural using (Natural)

open import DependentSortVocabulary

record Sequent
  {i : Level}
  (𝒥 : Semicategory i i)
  ⦃ _ : FunExt ⦄
  : Type (lsuc i) where
  constructor sequent
  field
    context : Semifunctor 𝒥 (TypeSemicategory i)
    judgmentForm : Semicategory.Ob 𝒥
    arguments : (SemiCoYoneda 𝒥 judgmentForm) ⟹ context

module ExtendedSemiCoYoneda {o a : Level} (𝒞 : Semicategory o a) (c : Ob 𝒞) where

  open Semicategory.Reasoning 𝒞

  onObjects : Ob 𝒞 → Type (o ⊔ a)
  onObjects d = (Hom 𝒞 c d) + (d ＝ c)

  onMorphisms : ∀ {d d'} → Hom 𝒞 d d' → onObjects d → onObjects d'
  onMorphisms f (inl g) = inl (f ∙ g)
  onMorphisms f (inr refl) = inl f

  preservesComposition~ : ∀ {d d' d''} (f : Hom 𝒞 d d') (g : Hom 𝒞 d' d'')
                        → onMorphisms (g ∙ f) ~ onMorphisms g ∘ onMorphisms f
  preservesComposition~ g h (inl f) = ap inl (sym ∙-associative)
  preservesComposition~ g h (inr refl) = refl

  instance
    mappable : Mappable 𝟙 _ _ _ _ _ (λ _ → Ob 𝒞) (λ i → Type i) (Hom 𝒞) (λ A B → A → B) _ onObjects
    mappable = record { map = onMorphisms }

    preservesComposition : ⦃ FunExt ⦄
                         → PreservesComposition _ _ _ _ _ _ (λ _ → Ob 𝒞) (λ i → Type i) _ (Hom 𝒞) (λ A B → A → B) _ onObjects (λ _ _ → _＝_)
    preservesComposition = record { preserves-composition = λ f g → funExt (preservesComposition~ f g) }

    semifunctorial : ⦃ FunExt ⦄
                   → Semifunctorial _ _ _ _ _ _ (λ _ → Ob 𝒞) (λ i → Type i) _ (Hom 𝒞) (λ A B → A → B) _ onObjects (λ _ _ → _＝_)
    semifunctorial = record {}

ExtendedSemiCoYoneda : ⦃ FunExt ⦄
                     → {o a : Level} (𝒞 : Semicategory o a) (c : Ob 𝒞)
                     → Semifunctor 𝒞 (TypeSemicategory (o ⊔ a))
Semifunctor.onObjects (ExtendedSemiCoYoneda 𝒞 c) = ExtendedSemiCoYoneda.onObjects 𝒞 c
Semifunctor.semifunctorial (ExtendedSemiCoYoneda 𝒞 c) = Semifunctorial.atLevel ★
  where
    open Semicategory.Reasoning 𝒞
    open ExtendedSemiCoYoneda 𝒞 c

module ContextExtension ⦃ _ : FunExt ⦄ {i : Level}
  {𝒥 : Semicategory i i} (s : Sequent 𝒥) where

  private
    Γ = Sequent.context s
    J = Sequent.judgmentForm s
    α = Sequent.arguments s

  open Semicategory.Reasoning 𝒥
  open Semifunctor.Reasoning Γ
  open SeminaturalTransformation.Reasoning α

  onObjects : Ob 𝒥 → Type i
  onObjects j = (Γ ⟨ j ⟩) + (j ＝ J)

  onMorphisms : ∀ {j j'} → Hom 𝒥 j j' → onObjects j → onObjects j'
  onMorphisms f (inl x) = inl ((Γ ⟨ f ⟩) x)
  onMorphisms {j' = j'} f (inr refl) = inl ((α ⟨ j' ⟩) f)

  preservesComposition~ : ∀ {j j' j''} (f : Hom 𝒥 j j') (g : Hom 𝒥 j' j'')
                        → onMorphisms (g ∙ f) ~ onMorphisms g ∘ onMorphisms f
  preservesComposition~ f g (inl x) = ap (λ h → inl (h x)) (preserves-composition f g)
    where open Semicategory.Reasoning (TypeSemicategory i)
  preservesComposition~ f g (inr refl) = ap (λ h → inl (h f)) (sym (natural α g))

  instance
    mappable : Mappable 𝟙 𝟙 _ _ _ _ (λ _ → Ob 𝒥) (λ _ → Type i) (Hom 𝒥) (λ A B → A → B) _ onObjects
    mappable = record { map = onMorphisms }

  module _ where
    open Semicategory.Reasoning (TypeSemicategory i)

    instance
      preservesComposition : PreservesComposition _ _ _ _ _ _ (λ _ → Ob 𝒥) (λ _ → Type i) _ (Hom 𝒥) (λ A B → A → B) _ onObjects (λ _ _ → _＝_)
      preservesComposition = record { preserves-composition = λ f g → funExt (preservesComposition~ f g) }

      semifunctorial : Semifunctorial _ _ _ _ _ _ (λ _ → Ob 𝒥) (λ _ → Type i) _ (Hom 𝒥) (λ A B → A → B) _ onObjects (λ _ _ → _＝_)
      semifunctorial = record {}

  extension : Semifunctor 𝒥 (TypeSemicategory i)
  extension = 
    record
      { onObjects = onObjects
      ; semifunctorial = Semifunctorial.atLevel ★ }
    where open Semicategory.Reasoning (TypeSemicategory i)

  ι : (j : Ob 𝒥) → Γ ⟨ j ⟩ → extension ⟨ j ⟩
  ι j = inl

  module _ where
    open Semicategory.Reasoning (TypeSemicategory i)

    instance
      naturalExtension : Natural _ _ _ _ _ _ (λ _ → Ob 𝒥) (λ _ → Type i) _ (Hom 𝒥) (λ A B → A → B) _ _
                           (Γ ⟨_⟩) (extension ⟨_⟩) (λ _ _ → _＝_) ι
      naturalExtension =  record { naturality = identity }

  context→extension : Γ ⟹ extension
  context→extension = 
    record
      { component = ι
      ; natural = Natural.atLevel ★ }
    where open Semicategory.Reasoning (TypeSemicategory i)
