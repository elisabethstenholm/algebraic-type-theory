module Weakening.SequentStructure where

open import Prelude
open import Axioms
open import Homotopy.SetQuotient
open import Structure.Associativity
open import Structure.Composable
open import Structure.Identity
open import Structure.PreservesComposition
open import Structure.Symmetric
open import Homotopy.StructuredType
open import Algebra.Wild.Semi
open Semicategory.Semicategory
open import Algebra.Wild.TruncatedTypeSemicategory
open import Homotopy.Equality
open import Homotopy.Levels
open import Foundation.Sum.Equivalence
open import Structure.Bimappable

open import DependentSortVocabulary
open import Context
open import Context.Morphism
open import Context.Extension
open import Context.ExtensionMorphism
open import Sequent
open import Sequent.Morphism
open import SequentStructure
open import SequentStructure.Equality
open import SequentDependencyStructure
open import SequentDependencyStructure.Equality
open import ContextWithTerms
open import Weakening.Sequent
open import Weakening.Sum
open SequentDependencyStructure.SequentDependencyStructure
open ContextWithTerms.ContextWithTerms


-- =============== Weakening a sequent structure ===============

module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄ {o a : Level} {𝒥 : DependentSortVocabulary o a} where

  weakenSequentStructure : {so sa i : Level}
                          → ContextWithTerms 𝒥 so sa i → SequentStructure 𝒥 so sa i
                          → SequentStructure 𝒥 so sa i
  weakenSequentStructure {so} {sa} {i} c ss =
    record
      { dependency =
          record
            { Ob = depOb
            ; Hom = depHom
            ; semicategorical =
                record
                  { composable =
                      record { composition = λ {A} {B} {C} → depComposition {A} {B} {C} }
                  ; associativeComposition =
                      record { ⨾-associative = λ {A} {B} {C} {D} {f} {g} {h} → depAssociative {A} {B} {C} {D} {f} {g} {h} } } }
      ; dependency-Ob-isSet = depOb-isSet
      ; dependency-Hom-isSet = depHom-isSet
      ; sequent =
          record
            { onObjects = onObjects
            ; semifunctorial =
                record
                  { mappable =
                      record
                        { map = λ {x} {y} → map {x} {y} }
                  ; preservesComposition =
                      record { preserves-composition = λ {A} {B} {C} g h → preserves {C} {B} {A} h g } } } }
    where
      cd = contextWithTerms c
      𝒞 = SequentStructure.dependency (SequentDependencyStructure.sequentStructure cd)
      ℱ = SequentStructure.sequent (SequentDependencyStructure.sequentStructure cd)
      𝒟 = SequentStructure.dependency ss
      𝒢 = SequentStructure.sequent ss

      open Semicategory.Reasoning 𝒞
      open Semicategory.Reasoning (𝒞 ᵒᵖ)
      open Semicategory.Reasoning 𝒟
      open Semicategory.Reasoning (𝒟 ᵒᵖ)
      open Semicategory.Reasoning (hSet-Semicategory sa)
      open Semifunctor.Reasoning (SequentDependencyStructure.dependency cd)

      depOb : Type so
      depOb = Ob 𝒞 + Ob 𝒟

      depHom : depOb → depOb → Type sa
      depHom (inl x) (inl y) = Hom 𝒞 x y
      depHom (inl x) (inr y) = Empty
      depHom (inr x) (inl y) = ⌞ (SequentDependencyStructure.dependency cd ⟨ y ⟩) ⌟
      depHom (inr x) (inr y) = Hom 𝒟 x y

      depComposition : {A B C : depOb} → depHom A B → depHom B C → depHom A C
      depComposition {inl x} {inl y} {inl z} f g = g ∙ f
      depComposition {inl x} {inl y} {inr z} f ()
      depComposition {inl x} {inr y} {C} () g
      depComposition {inr x} {inl y} {inl z} f g = (SequentDependencyStructure.dependency cd ⟨ g ⟩) f
      depComposition {inr x} {inl y} {inr z} f ()
      depComposition {inr x} {inr y} {inl z} f g = g
      depComposition {inr x} {inr y} {inr z} f g = g ∙ f

      depAssociative : {A B C D : depOb} {f : depHom A B} {g : depHom B C} {h : depHom C D}
                     → depComposition {A} {C} {D} (depComposition {A} {B} {C} f g) h
                     ＝ depComposition {A} {B} {D} f (depComposition {B} {C} {D} g h)
      depAssociative {inl w} {inl x} {inl y} {inl z} = ⨾-associative
      depAssociative {inr w} {inl x} {inl y} {inl z} {f} {g} {h} = sym (ap (λ σ → σ f) (preserves-composition g h))
      depAssociative {inr w} {inr x} {inl y} {inl z} = refl
      depAssociative {inr w} {inr x} {inr y} {inl z} = refl
      depAssociative {inr w} {inr x} {inr y} {inr z} = ⨾-associative
      depAssociative {A} {B} {inl y} {inr z} {g = g} {h = ()}
      depAssociative {A} {inl x} {inr y} {D} {g = ()}
      depAssociative {inl w} {inr x} {C} {D} {f = ()}

      opaque
       depOb-isSet : isSet depOb
       depOb-isSet = +-level (SequentStructure.dependency-Ob-isSet (SequentDependencyStructure.sequentStructure cd))
                             (SequentStructure.dependency-Ob-isSet ss)

       depHom-isSet : (A B : depOb) → isSet (depHom A B)
       depHom-isSet (inl x) (inl y) = SequentStructure.dependency-Hom-isSet (SequentDependencyStructure.sequentStructure cd) x y
       depHom-isSet (inl x) (inr y) = 𝟘-isLevel
       depHom-isSet (inr x) (inl y) = level-proof (SequentDependencyStructure.dependency cd ⟨ y ⟩)
       depHom-isSet (inr x) (inr y) = SequentStructure.dependency-Hom-isSet ss x y

      onObjects : depOb → Sequent 𝒥 i
      onObjects (inl x) = ℱ ⟨ x ⟩
      onObjects (inr x) = weakenSequent (head (contextWithTerms c)) (𝒢 ⟨ x ⟩)

      map : {x y : depOb}
          → depHom y x
          → SequentMorphism (onObjects x) (onObjects y)
      map {inl x} {inl y} f = ℱ ⟨ f ⟩
      map {inl x} {inr y} f =
        mkSequentMorphism (→⋊ (onObjects (inr y)) ∙ (inlContext ∙ realiseDependency cd x f))
      map {inr x} {inr y} f = weakenSequentMorphism (head cd) (𝒢 ⟨ f ⟩)

      preserves : {A B C : depOb} (f : depHom A B) (g : depHom B C)
                → map {C} {A} (depComposition {A} {B} {C} f g) ＝ map {B} {A} f ∙ map {C} {B} g
      preserves {inl x} {inl y} {inl z} f g = PreservesComposition.preserves-composition pres _ _
        where
          open Semifunctor.Reasoning ℱ renaming (preservesCompositionₛ to pres)
          open Semicategory.Reasoning (SequentSemicategory 𝒥 i)
      preserves {inl x} {inl y} {inr z} f ()
      preserves {inl x} {inr y} {C} () g
      preserves {inr x} {inl y} {inl z} f g = ap mkSequentMorphism
        (   ap (λ σ → →⋊ s ∙ (inlContext ∙ σ)) (coherenceRealisation cd f g)
         ⨾  ap (→⋊ s ∙_) (∙-associative {f = ℱg} {g = realiseDependency cd y f} {h = inlContext})
         ⨾  ∙-associative {f = ℱg} {g = inlContext ∙ realiseDependency cd y f} {h = →⋊ s})
        where
          s = onObjects (inr x)
          ℱg = SequentMorphism.sequentMorphism (ℱ ⟨ g ⟩)
      preserves {inr x} {inl y} {inr z} f ()
      preserves {inr x} {inr y} {inl z} f g =
        ap mkSequentMorphism
          (eq (record
                 { component≈ = λ j → funExt λ w →
                     sym (weakenSequentMorphism-onAdded (head cd) (𝒢 ⟨ f ⟩) j
                            ((realiseDependency cd z g ⟨ j ⟩) w)) }))
      preserves {inr x} {inr y} {inr z} f g =
           ap (weakenSequentMorphism (head cd)) (PreservesComposition.preserves-composition pres g f)
        ⨾  weakenSequentMorphism-composition (head cd) (𝒢 ⟨ g ⟩) (𝒢 ⟨ f ⟩)
        where
          open Semifunctor.Reasoning 𝒢 renaming (preservesCompositionₛ to pres)
          open Semicategory.Reasoning (SequentSemicategory 𝒥 i)

  infixr 15 _⧺_
  _⧺_ : {so sa i : Level}
      → ContextWithTerms 𝒥 so sa i → SequentStructure 𝒥 so sa i
      → SequentStructure 𝒥 so sa i
  _⧺_ = weakenSequentStructure



-- =============== Collage of two contexts with terms ===============

module _ ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a} where

  infixr 15 _⧺ᶜ_
  _⧺ᶜ_ : ContextWithTerms 𝒥 so sa i → ContextWithTerms 𝒥 so sa i
       → ContextWithTerms 𝒥 so sa i
  c₁ ⧺ᶜ c₀ =
    mkContextWithTerms
      record
        { head = SequentDependencyStructure.head cd₁ + SequentDependencyStructure.head cd₀
        ; sequentStructure = E
        ; dependency = dependencyE
        ; realiseDependency = realiseE
        ; coherenceRealisation = λ
            { {inl w} {inl w'} f g → coherenceE {inl w} {inl w'} f g
            ; {inr x} {inr x'} f g → coherenceE {inr x} {inr x'} f g
            ; {inr x} {inl w} f g → coherenceE {inr x} {inl w} f g
            ; {inl w} {inr x} f () } }
    where
      cd₁ = contextWithTerms c₁
      cd₀ = contextWithTerms c₀
      h₁ = SequentDependencyStructure.head cd₁
      h₀ = SequentDependencyStructure.head cd₀
      ss₀ = SequentDependencyStructure.sequentStructure cd₀
      𝒞₁ = SequentStructure.dependency (SequentDependencyStructure.sequentStructure cd₁)
      ℱ₁ = SequentStructure.sequent (SequentDependencyStructure.sequentStructure cd₁)
      𝒞₀ = SequentStructure.dependency ss₀
      ℱ₀ = SequentStructure.sequent ss₀
      dep₁ = SequentDependencyStructure.dependency cd₁
      dep₀ = SequentDependencyStructure.dependency cd₀
      r₁ = SequentDependencyStructure.realiseDependency cd₁
      r₀ = SequentDependencyStructure.realiseDependency cd₀

      E = c₁ ⧺ ss₀
      𝒟E = SequentStructure.dependency E

      onObjectsD : Ob 𝒟E → Ob (hSet-Semicategory sa)
      onObjectsD (inl w) = dep₁ ⟨ w ⟩
      onObjectsD (inr x) = dep₀ ⟨ x ⟩

      mapD : {x y : Ob 𝒟E} → Hom 𝒟E x y → ⌞ onObjectsD x ⌟ → ⌞ onObjectsD y ⌟
      mapD {inl w} {inl w'} g = dep₁ ⟨ g ⟩
      mapD {inr x} {inr x'} g = dep₀ ⟨ g ⟩
      mapD {inr x} {inl w} g = λ _ → g
      mapD {inl w} {inr x} ()

      dependencyE : Semifunctor 𝒟E (hSet-Semicategory sa)
      dependencyE =
        record
          { onObjects = onObjectsD
          ; semifunctorial = record
              { mappable = record { map = λ {x} {y} → mapD {x} {y} }
              ; preservesComposition = record
                  { preserves-composition = λ
                      { {inl w} {inl w'} {inl w''} f g →
                          Structure.PreservesComposition.Bounded.preserves-composition
                            (Semifunctorial.Bounded.preservesComposition
                               (SemifunctorProjections.semifunctorial dep₁)) f g
                      ; {inr x} {inr x'} {inr x''} f g →
                          Structure.PreservesComposition.Bounded.preserves-composition
                            (Semifunctorial.Bounded.preservesComposition
                               (SemifunctorProjections.semifunctorial dep₀)) f g
                      ; {inr x} {inr x'} {inl w} f g → refl
                      ; {inr x} {inl w} {inl w'} f g → refl
                      ; {inl w} {inr x} {z} () g
                      ; {inl w} {inl w'} {inr x} f ()
                      ; {inr x} {inl w} {inr x'} f () } } } }

      idH₁ : h₁ ⇒ h₁
      idH₁ = identity

      realiseE : (d : Ob 𝒟E) → ⌞ onObjectsD d ⌟
               → ContextMorphism (extendedContext (SequentStructure.sequent E ⟨ d ⟩)) (h₁ + h₀)
      realiseE (inl w) u = inlContext {Γ = h₁} {Δ = h₀} ∙ r₁ w u
      realiseE (inr x) u =
        sumContextMorphism idH₁ (r₀ x u) ∙ distributeExtended h₁ (ℱ₀ ⟨ x ⟩)

      mapSeqE : {d₀ d₁ : Ob 𝒟E} → Hom 𝒟E d₀ d₁
              → SequentMorphism (SequentStructure.sequent E ⟨ d₁ ⟩)
                                (SequentStructure.sequent E ⟨ d₀ ⟩)
      mapSeqE {inl w} {inl w'} g = ℱ₁ ⟨ g ⟩
      mapSeqE {inr x} {inr x'} g = weakenSequentMorphism h₁ (ℱ₀ ⟨ g ⟩)
      mapSeqE {inr x} {inl w} g =
        mkSequentMorphism (→⋊ (weakenSequent h₁ (ℱ₀ ⟨ x ⟩)) ∙ (inlContext ∙ r₁ w g))
      mapSeqE {inl w} {inr x} ()

      coherenceE : {d₀ d₁ : Ob 𝒟E} (f : ⌞ onObjectsD d₀ ⌟) (g : Hom 𝒟E d₀ d₁)
                 → realiseE d₁ (mapD {d₀} {d₁} g f)
                 ＝ realiseE d₀ f ∙ SequentMorphism.sequentMorphism (mapSeqE {d₀} {d₁} g)
      coherenceE {inl w} {inl w'} f g =
           ap (inlContext {Γ = h₁} {Δ = h₀} ∙_) (SequentDependencyStructure.coherenceRealisation cd₁ f g)
        ⨾  ∙-associative {f = SequentMorphism.sequentMorphism (ℱ₁ ⟨ g ⟩)} {g = r₁ w f} {h = inlContext {Γ = h₁} {Δ = h₀}}
      coherenceE {inr x} {inr x'} f g =
        eq (record { component≈ = λ j → funExt (pointwise j) })
        where
          m = SequentMorphism.sequentMorphism (ℱ₀ ⟨ g ⟩)

          stepB : (j : type (Judgment 𝒥)) (v : ⌞ (h₁ + extendedContext (ℱ₀ ⟨ x' ⟩)) ⟨ j ⟩ ⌟)
                → (sumContextMorphism idH₁ (r₀ x' ((dep₀ ⟨ g ⟩) f)) ⟨ j ⟩) v
                  ＝ (sumContextMorphism idH₁ (r₀ x f) ⟨ j ⟩)
                      ((sumContextMorphism idH₁ m ⟨ j ⟩) v)
          stepB j (inl h) = refl
          stepB j (inr u) =
            ap inr (ap (λ γ → (γ ⟨ j ⟩) u) (SequentDependencyStructure.coherenceRealisation cd₀ f g))

          pointwise : (j : type (Judgment 𝒥))
                      (w : ⌞ extendedContext (weakenSequent h₁ (ℱ₀ ⟨ x' ⟩)) ⟨ j ⟩ ⌟)
                    → (realiseE (inr x') ((dep₀ ⟨ g ⟩) f) ⟨ j ⟩) w
                      ＝ ((realiseE (inr x) f
                          ∙ SequentMorphism.sequentMorphism (weakenSequentMorphism h₁ (ℱ₀ ⟨ g ⟩))) ⟨ j ⟩) w
          pointwise j w =
               stepB j ((distributeExtended h₁ (ℱ₀ ⟨ x' ⟩) ⟨ j ⟩) w)
            ⨾  sym (ap (sumContextMorphism idH₁ (r₀ x f) ⟨ j ⟩)
                       (distribute-gather h₁ (ℱ₀ ⟨ x ⟩) j
                          ((sumContextMorphism idH₁ m ⟨ j ⟩)
                             ((distributeExtended h₁ (ℱ₀ ⟨ x' ⟩) ⟨ j ⟩) w))))
      coherenceE {inr x} {inl w} f g =
        eq (record { component≈ = λ j → funExt (pointwise j) })
        where
          crossM : ContextMorphism (extendedContext (ℱ₁ ⟨ w ⟩))
                                   (extendedContext (weakenSequent h₁ (ℱ₀ ⟨ x ⟩)))
          crossM = →⋊ (weakenSequent h₁ (ℱ₀ ⟨ x ⟩)) ∙ (inlContext ∙ r₁ w g)

          pointwise : (j : type (Judgment 𝒥)) (z : ⌞ extendedContext (ℱ₁ ⟨ w ⟩) ⟨ j ⟩ ⌟)
                    → (realiseE (inl w) g ⟨ j ⟩) z
                      ＝ ((realiseE (inr x) f ∙ crossM) ⟨ j ⟩) z
          pointwise j z =
            sym (ap (sumContextMorphism idH₁ (r₀ x f) ⟨ j ⟩)
                    (distributeExtended-onAdded h₁ (ℱ₀ ⟨ x ⟩) j ((r₁ w g ⟨ j ⟩) z)))
      coherenceE {inl w} {inr x} f ()


-- =============== Weakening respects equality of contexts with terms ===============

module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a} where

  ⧺-congruenceˡ :
      {b₀ b₁ : ContextWithTerms 𝒥 so sa i} (X : SequentStructure 𝒥 so sa i)
    → ContextWithTermsEquality b₀ b₁
    → SequentStructureEquality (b₀ ⧺ X) (b₁ ⧺ X)
  ⧺-congruenceˡ {b₀} {b₁} X (mkContextWithTermsEquality w) =
    record
      { dependency≈ = dependency≈'
      ; sequent≈ = sequent≈'
      ; natural≈ = λ
          { {inl u} {inl v} f → wnat f
          ; {inr x} {inr y} f → natural-rr x y f
          ; {inr x} {inl u} g → natural-rl x u g
          ; {inl u} {inr y} () } }
    where
      bd₀ = contextWithTerms b₀
      bd₁ = contextWithTerms b₁
      h₀ = SequentDependencyStructure.head bd₀
      h₁ = SequentDependencyStructure.head bd₁
      ss₀ = SequentDependencyStructure.sequentStructure bd₀
      ss₁ = SequentDependencyStructure.sequentStructure bd₁
      𝒞₀ = SequentStructure.dependency ss₀
      𝒞₁ = SequentStructure.dependency ss₁
      ℱ₀ = SequentStructure.sequent ss₀
      ℱ₁ = SequentStructure.sequent ss₁
      depF₀ = SequentDependencyStructure.dependency bd₀
      depF₁ = SequentDependencyStructure.dependency bd₁
      r₀ = SequentDependencyStructure.realiseDependency bd₀
      r₁ = SequentDependencyStructure.realiseDependency bd₁
      𝒟X = SequentStructure.dependency X
      𝒢X = SequentStructure.sequent X

      wh : ContextEquivalence h₀ h₁
      wh = SequentDependencyStructureEquality.head≈ w

      wss = SequentDependencyStructureEquality.sequentStructure≈ w
      wt = SequentDependencyStructureEquality.terms≈ w
      wtn = SequentDependencyStructureEquality.termsNatural w
      wr = SequentDependencyStructureEquality.realise≈ w

      wd = SequentStructureEquality.dependency≈ wss
      wseq = SequentStructureEquality.sequent≈ wss
      wnat = SequentStructureEquality.natural≈ wss

      objects≈' : Ob (SequentStructure.dependency (b₀ ⧺ X))
                ≃ Ob (SequentStructure.dependency (b₁ ⧺ X))
      objects≈' = bimap (Semicategory.objects≈ wd) ≃-id

      hom≈' : (A B : Ob (SequentStructure.dependency (b₀ ⧺ X)))
            → Hom (SequentStructure.dependency (b₀ ⧺ X)) A B
            ≃ Hom (SequentStructure.dependency (b₁ ⧺ X))
                  (there objects≈' A) (there objects≈' B)
      hom≈' (inl u) (inl v) = Semicategory.hom≈ wd u v
      hom≈' (inr x) (inr y) = ≃-id
      hom≈' (inr x) (inl u) = wt u
      hom≈' (inl u) (inr y) = ≃-id

      dependency≈' : SequentStructure.dependency (b₀ ⧺ X) ≈ SequentStructure.dependency (b₁ ⧺ X)
      dependency≈' =
        record
          { objects≈ = objects≈'
          ; hom≈ = hom≈'
          ; composition≈ = λ
              { (inl u) (inl v) (inl e) f g → Semicategory.composition≈ wd u v e f g
              ; (inr x) (inr y) (inr z) f g → refl
              ; (inr x) (inr y) (inl u) f g → refl
              ; (inr x) (inl u) (inl v) f g → sym (ap (λ h → h f) (wtn g))
              ; (inl u) (inr y) E () g
              ; (inl u) (inl v) (inr y) f ()
              ; (inr x) (inl u) (inr y) f () }
          ; associative≈ = λ A B E F f g h →
              allEqual ⦃ ＝-isLevel ⦃ SequentStructure.dependency-Hom-isSet (b₁ ⧺ X)
                                        (there objects≈' A) (there objects≈' F) ⦄ ⦄ _ _ }

      sequent≈' : (A : Ob (SequentStructure.dependency (b₀ ⧺ X)))
                → SequentEquivalence (SequentStructure.sequent (b₀ ⧺ X) ⟨ A ⟩)
                                     (SequentStructure.sequent (b₁ ⧺ X) ⟨ there objects≈' A ⟩)
      sequent≈' (inl u) = wseq u
      sequent≈' (inr x) = weakenedSequentEquivalence wh sequentEquivalence-identity

      idSM : {l : Level} {s : Sequent 𝒥 l}
           → SequentMorphism.sequentMorphism (toSequentMorphism (sequentEquivalence-identity {s = s}))
             ＝ identity
      idSM {s = s} = eq (toSequentMorphism-identity {s = s})

      unitLᶜ : {l₀ l₁ : Level} {Γ : Context 𝒥 l₀} {Δ : Context 𝒥 l₁} (β : Γ ⇒ Δ)
             → identity ∙ β ＝ β
      unitLᶜ β = eq (record { component≈ = λ j → refl })

      unitRᶜ : {l₀ l₁ : Level} {Γ : Context 𝒥 l₀} {Δ : Context 𝒥 l₁} (β : Γ ⇒ Δ)
             → β ∙ identity ＝ β
      unitRᶜ β = eq (record { component≈ = λ j → refl })

      sumStep : (x : Ob 𝒟X)
              → toSequentMorphism (weakenedSequentEquivalence wh (sequentEquivalence-identity {s = 𝒢X ⟨ x ⟩}))
                ＝ weakenedSequentMorphism (ContextEquivalence.morphism wh)
                    (toSequentMorphism (sequentEquivalence-identity {s = 𝒢X ⟨ x ⟩}))
      sumStep x =
        ap mkSequentMorphism
           (map⋊-sum (ContextEquivalence.morphism wh)
                     (ContextEquivalence.morphism (SequentEquivalence.contextEquivalence
                        (sequentEquivalence-identity {s = 𝒢X ⟨ x ⟩})))
                     (Sequent.extensionOrCollapse (𝒢X ⟨ x ⟩))
                     (Sequent.extensionOrCollapse (𝒢X ⟨ x ⟩))
                     (SequentEquivalence.extensionOrCollapseEquality
                        (sequentEquivalence-identity {s = 𝒢X ⟨ x ⟩})))

      natural-rr : (x y : Ob 𝒟X) (f : Hom 𝒟X x y)
                 → SequentMorphismEquality
                     (toSequentMorphism (sequent≈' (inr x)) ∙ weakenSequentMorphism h₀ (𝒢X ⟨ f ⟩))
                     (weakenSequentMorphism h₁ (𝒢X ⟨ f ⟩) ∙ toSequentMorphism (sequent≈' (inr y)))
      natural-rr x y f =
        observe ⦃ equalitySequentMorphism ⦄
          (begin
            toSequentMorphism (sequent≈' (inr x)) ∙ weakenSequentMorphism h₀ (𝒢X ⟨ f ⟩)
              ⟪ ap (_∙ weakenSequentMorphism h₀ (𝒢X ⟨ f ⟩)) (sumStep x) ⟫
            weakenedSequentMorphism (ContextEquivalence.morphism wh)
              (toSequentMorphism (sequentEquivalence-identity {s = 𝒢X ⟨ x ⟩}))
              ∙ weakenedSequentMorphism identity (𝒢X ⟨ f ⟩)
              ⟪ ap (λ m → weakenedSequentMorphism (ContextEquivalence.morphism wh) m
                          ∙ weakenedSequentMorphism identity (𝒢X ⟨ f ⟩))
                   (ap mkSequentMorphism (idSM {s = 𝒢X ⟨ x ⟩})) ⟫
            weakenedSequentMorphism (ContextEquivalence.morphism wh) (mkSequentMorphism identity)
              ∙ weakenedSequentMorphism identity (𝒢X ⟨ f ⟩)
              ⟪ sym (weakenedSequentMorphism-composition identity (ContextEquivalence.morphism wh)
                       (𝒢X ⟨ f ⟩) (mkSequentMorphism identity)) ⟫
            weakenedSequentMorphism (ContextEquivalence.morphism wh ∙ identity)
              (𝒢X ⟨ f ⟩ ⨾ mkSequentMorphism identity)
              ⟪ ap (λ m → weakenedSequentMorphism m (𝒢X ⟨ f ⟩ ⨾ mkSequentMorphism identity))
                   (unitRᶜ (ContextEquivalence.morphism wh)) ⟫
            weakenedSequentMorphism (ContextEquivalence.morphism wh)
              (𝒢X ⟨ f ⟩ ⨾ mkSequentMorphism identity)
              ⟪ ap (λ m → weakenedSequentMorphism (ContextEquivalence.morphism wh) (mkSequentMorphism m))
                   (unitLᶜ (SequentMorphism.sequentMorphism (𝒢X ⟨ f ⟩))) ⟫
            weakenedSequentMorphism (ContextEquivalence.morphism wh) (𝒢X ⟨ f ⟩)
              ⟪ sym (ap (λ m → weakenedSequentMorphism (ContextEquivalence.morphism wh) (mkSequentMorphism m))
                        (unitRᶜ (SequentMorphism.sequentMorphism (𝒢X ⟨ f ⟩)))) ⟫
            weakenedSequentMorphism (ContextEquivalence.morphism wh)
              (mkSequentMorphism identity ⨾ 𝒢X ⟨ f ⟩)
              ⟪ sym (ap (λ m → weakenedSequentMorphism m (mkSequentMorphism identity ⨾ 𝒢X ⟨ f ⟩))
                        (unitLᶜ (ContextEquivalence.morphism wh))) ⟫
            weakenedSequentMorphism (identity ∙ ContextEquivalence.morphism wh)
              (mkSequentMorphism identity ⨾ 𝒢X ⟨ f ⟩)
              ⟪ weakenedSequentMorphism-composition (ContextEquivalence.morphism wh) identity
                  (mkSequentMorphism identity) (𝒢X ⟨ f ⟩) ⟫
            weakenedSequentMorphism (ContextEquivalence.morphism wh) (mkSequentMorphism identity)
              ⨾ weakenedSequentMorphism identity (𝒢X ⟨ f ⟩)
              ⟪ sym (ap (λ m → weakenedSequentMorphism identity (𝒢X ⟨ f ⟩)
                              ∙ weakenedSequentMorphism (ContextEquivalence.morphism wh) m)
                        (ap mkSequentMorphism (idSM {s = 𝒢X ⟨ y ⟩}))) ⟫
            weakenedSequentMorphism identity (𝒢X ⟨ f ⟩)
              ∙ weakenedSequentMorphism (ContextEquivalence.morphism wh)
                  (toSequentMorphism (sequentEquivalence-identity {s = 𝒢X ⟨ y ⟩}))
              ⟪ sym (ap (weakenSequentMorphism h₁ (𝒢X ⟨ f ⟩) ∙_) (sumStep y)) ⟫
            weakenSequentMorphism h₁ (𝒢X ⟨ f ⟩) ∙ toSequentMorphism (sequent≈' (inr y))  ∎)
      natural-rl : (x : Ob 𝒟X) (u : Ob 𝒞₀) (g : ⌞ (depF₀ ⟨ u ⟩) ⌟)
                 → SequentMorphismEquality
                     (toSequentMorphism (sequent≈' (inr x))
                       ∙ mkSequentMorphism (→⋊ (weakenSequent h₀ (𝒢X ⟨ x ⟩)) ∙ (inlContext ∙ r₀ u g)))
                     (mkSequentMorphism (→⋊ (weakenSequent h₁ (𝒢X ⟨ x ⟩))
                        ∙ (inlContext ∙ r₁ (there (Semicategory.objects≈ wd) u) (there (wt u) g)))
                       ∙ toSequentMorphism (wseq u))
      natural-rl x u g =
        mkSequentMorphismEquality (record { component≈ = λ j → funExt (pw j) })
        where
          pw : (j : type (Judgment 𝒥)) (z : ⌞ extendedContext (ℱ₀ ⟨ u ⟩) ⟨ j ⟩ ⌟)
             → ((SequentMorphism.sequentMorphism (toSequentMorphism (sequent≈' (inr x)))
                 ∙ (→⋊ (weakenSequent h₀ (𝒢X ⟨ x ⟩)) ∙ (inlContext ∙ r₀ u g))) ⟨ j ⟩) z
               ＝ (((→⋊ (weakenSequent h₁ (𝒢X ⟨ x ⟩)) ∙ (inlContext ∙ r₁ (there (Semicategory.objects≈ wd) u) (there (wt u) g)))
                   ∙ SequentMorphism.sequentMorphism (toSequentMorphism (wseq u))) ⟨ j ⟩) z
          pw j z =
               map⋊-sum-onAdded (ContextEquivalence.morphism wh)
                 (ContextEquivalence.morphism (SequentEquivalence.contextEquivalence
                    (sequentEquivalence-identity {s = 𝒢X ⟨ x ⟩})))
                 (Sequent.extensionOrCollapse (𝒢X ⟨ x ⟩))
                 (Sequent.extensionOrCollapse (𝒢X ⟨ x ⟩))
                 (SequentEquivalence.extensionOrCollapseEquality
                    (sequentEquivalence-identity {s = 𝒢X ⟨ x ⟩}))
                 j ((r₀ u g ⟨ j ⟩) z)
            ⨾  ap (λ v → (→⋊ (weakenSequent h₁ (𝒢X ⟨ x ⟩)) ⟨ j ⟩) (inl v))
                  (ap (λ h → h z) (ContextMorphismEquality.component≈ (wr u g) j))


