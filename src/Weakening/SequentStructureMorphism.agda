module Weakening.SequentStructureMorphism where

open import Prelude
open import Axioms
open import Homotopy.SetQuotient.Nominal
open import Syntax.Addable
open import Syntax.Arrowable
open import Structure.Associativity
open import Structure.Composable
open import Structure.Identity
open import Structure.PreservesComposition
open import Structure.Reasoning
open import Structure.Symmetric
open import Homotopy.StructuredType
open import Algebra.Wild.Semicategory
open import Algebra.Wild.Semifunctor
import Structure.Semifunctorial as Semifunctorial
open Semicategory
open import Homotopy.Equality
open import Homotopy.Fibre
open import Homotopy.Levels
open import Foundation.DependentPair.Equivalence
open import Foundation.Sum.Equivalence

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
open import ContextWithTerms
open import Weakening.Sequent
open SequentDependencyStructure.SequentDependencyStructure
open ContextWithTerms.ContextWithTerms
open import SequentDependencyStructure.Equality
open import Weakening.Sum
open import Weakening.Reassociation
open import Weakening.SequentStructure
open import SequentStructureMorphism
open import SequentStructureMorphism.Equality


-- =============== Weakening on sequent structure morphisms ===============

module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a} where

  private
    idCM＝ : {l : Level} {Γ : Context 𝒥 l}
          → _＝_ {A = Γ ⇒ Γ} (identity ∙ identity) identity
    idCM＝ = eq (record { component≈ = λ j → refl })

    idSquare : {l₀ l₁ : Level} {s₀ : Sequent 𝒥 l₀} {s₁ : Sequent 𝒥 l₁}
               (α : SequentMorphism s₀ s₁)
             → toSequentMorphism (sequentEquivalence-identity {s = s₁}) ∙ α
               ＝ α ∙ toSequentMorphism (sequentEquivalence-identity {s = s₀})
    idSquare {s₀ = s₀} {s₁ = s₁} α =
      ap mkSequentMorphism (eq (record { component≈ = λ j → funExt (λ z →
           toSequentMorphism-identity-at {s = s₁} j ((SequentMorphism.sequentMorphism α ⟨ j ⟩) z)
        ⨾  sym (ap (SequentMorphism.sequentMorphism α ⟨ j ⟩)
                   (toSequentMorphism-identity-at {s = s₀} j z))) }))

  infixr 15 _⧺ˢ_
  _⧺ˢ_ : (B : ContextWithTerms 𝒥 so sa i)
       → {X Y : SequentStructure 𝒥 so sa i}
       → SequentStructureMorphism X Y
       → SequentStructureMorphism (B ⧺ X) (B ⧺ Y)
  _⧺ˢ_ B {X} {Y} σ =
    record
      { dependencyMorphism = record
          { onDependencies = onDep
          ; dependenciesEquivalence = depsEq }
      ; sequentEquivalence = seqEq
      ; natural = λ { {inl w} {inl w'} f → natural-ll f
                    ; {inr x} {inr x'} f → natural-rr f
                    ; {inr x} {inl w} f → natural-rl f
                    ; {inl w} {inr x} () } }
    where
      Bd = ContextWithTerms.contextWithTerms B
      H = SequentDependencyStructure.head Bd
      ℱB = SequentStructure.sequent (SequentDependencyStructure.sequentStructure Bd)
      rB = SequentDependencyStructure.realiseDependency Bd
      𝒟X = SequentStructure.dependency X
      𝒟Y = SequentStructure.dependency Y
      𝒢X = SequentStructure.sequent X
      𝒢Y = SequentStructure.sequent Y
      σd = SequentStructureMorphism.dependencyMorphism σ
      Φ = SequentDependencyMorphism.onDependencies σd
      σse = SequentStructureMorphism.sequentEquivalence σ

      𝒟BX = SequentStructure.dependency (B ⧺ X)
      𝒟BY = SequentStructure.dependency (B ⧺ Y)

      onObj : Ob 𝒟BX → Ob 𝒟BY
      onObj (inl w) = inl w
      onObj (inr x) = inr (Φ ⟨ x ⟩)

      mapH : {x y : Ob 𝒟BX} → Hom 𝒟BX x y → Hom 𝒟BY (onObj x) (onObj y)
      mapH {inl w} {inl w'} g = g
      mapH {inr x} {inr x'} g = Φ ⟨ g ⟩
      mapH {inr x} {inl w} g = g
      mapH {inl w} {inr x} ()

      onDep : Semifunctor 𝒟BX 𝒟BY
      onDep =
        record
          { onObjects = onObj
          ; semifunctorial = record
              { mappable = record { map = λ {x} {y} → mapH {x} {y} }
              ; preservesComposition = record
                  { preserves-composition = λ
                      { {inl w} {inl w'} {inl w''} f g → refl
                      ; {inr x} {inr x'} {inr x''} f g →
                          Structure.PreservesComposition.Bounded.preserves-composition
                            (Semifunctorial.Bounded.preservesComposition
                               (Semifunctor.semifunctorial Φ)) f g
                      ; {inr x} {inr x'} {inl w} f g → refl
                      ; {inr x} {inl w} {inl w'} f g → refl
                      ; {inl w} {inr x} {z} () g
                      ; {inl w} {inl w'} {inr x} f ()
                      ; {inr x} {inl w} {inr x'} f () } } } }

      depsEq : (x : Ob 𝒟BX) → isEquivalence (mapDependencies onDep x)
      depsEq (inl w) =
        record
          { section = record { sectionBack = backL ; isSection = sectL }
          ; retraction = record { retractionBack = backL ; isRetraction = retrL } }
        where
          backL : dependenciesOf 𝒟BY (inl w) → dependenciesOf 𝒟BX (inl w)
          backL (inl w' , g) = inl w' , g
          backL (inr y , ())

          sectL : (d : dependenciesOf 𝒟BY (inl w))
                → mapDependencies onDep (inl w) (backL d) ＝ d
          sectL (inl w' , g) = refl
          sectL (inr y , ())

          retrL : (d : dependenciesOf 𝒟BX (inl w))
                → backL (mapDependencies onDep (inl w) d) ＝ d
          retrL (inl w' , g) = refl
          retrL (inr y , ())
      depsEq (inr x) =
        record
          { section = record { sectionBack = backS ; isSection = sectR }
          ; retraction = record { retractionBack = backT ; isRetraction = retrR } }
        where
          σeq = SequentDependencyMorphism.dependenciesEquivalence σd x

          injX : dependenciesOf 𝒟X x → dependenciesOf 𝒟BX (inr x)
          injX (y , f) = inr y , f

          injY : dependenciesOf 𝒟Y (Φ ⟨ x ⟩) → dependenciesOf 𝒟BY (inr (Φ ⟨ x ⟩))
          injY (y , f) = inr y , f

          backS : dependenciesOf 𝒟BY (inr (Φ ⟨ x ⟩)) → dependenciesOf 𝒟BX (inr x)
          backS (inl w , g) = inl w , g
          backS (inr y , f) = injX (sectionBack (section σeq) (y , f))

          backT : dependenciesOf 𝒟BY (inr (Φ ⟨ x ⟩)) → dependenciesOf 𝒟BX (inr x)
          backT (inl w , g) = inl w , g
          backT (inr y , f) = injX (retractionBack (retraction σeq) (y , f))

          sectR : (d : dependenciesOf 𝒟BY (inr (Φ ⟨ x ⟩)))
                → mapDependencies onDep (inr x) (backS d) ＝ d
          sectR (inl w , g) = refl
          sectR (inr y , f) = ap injY (isSection (section σeq) (y , f))

          retrR : (d : dependenciesOf 𝒟BX (inr x))
                → backT (mapDependencies onDep (inr x) d) ＝ d
          retrR (inl w , g) = refl
          retrR (inr y , f) = ap injX (isRetraction (retraction σeq) (y , f))

      idH-equiv : ContextEquivalence H H
      idH-equiv = identity

      seqEq : (x : Ob 𝒟BX)
            → SequentEquivalence (SequentStructure.sequent (B ⧺ X) ⟨ x ⟩)
                                 (SequentStructure.sequent (B ⧺ Y) ⟨ onObj x ⟩)
      seqEq (inl w) = sequentEquivalence-identity
      seqEq (inr x) = weakenedSequentEquivalence idH-equiv (σse x)

      natural-ll : {w w' : Ob (SequentStructure.dependency (SequentDependencyStructure.sequentStructure Bd))}
                   (f : Hom (SequentStructure.dependency (SequentDependencyStructure.sequentStructure Bd)) w w')
                 → toSequentMorphism (sequentEquivalence-identity {s = ℱB ⟨ w ⟩}) ∙ ℱB ⟨ f ⟩
                   ＝ ℱB ⟨ f ⟩ ∙ toSequentMorphism (sequentEquivalence-identity {s = ℱB ⟨ w' ⟩})
      natural-ll f = idSquare (ℱB ⟨ f ⟩)

      sumStep : (x : Ob 𝒟X)
              → toSequentMorphism (seqEq (inr x))
                ＝ weakenedSequentMorphism identity (toSequentMorphism (σse x))
      sumStep x =
        ap mkSequentMorphism
           (map⋊-sum (ContextEquivalence.morphism idH-equiv)
                     (ContextEquivalence.morphism (SequentEquivalence.contextEquivalence (σse x)))
                     (Sequent.extensionOrCollapse (𝒢X ⟨ x ⟩))
                     (Sequent.extensionOrCollapse (𝒢Y ⟨ Φ ⟨ x ⟩ ⟩))
                     (SequentEquivalence.extensionOrCollapseEquality (σse x)))

      natural-rr : {x x' : Ob 𝒟X} (f : Hom 𝒟X x x')
                 → toSequentMorphism (seqEq (inr x)) ∙ weakenSequentMorphism H (𝒢X ⟨ f ⟩)
                   ＝ weakenSequentMorphism H (𝒢Y ⟨ Φ ⟨ f ⟩ ⟩) ∙ toSequentMorphism (seqEq (inr x'))
      natural-rr {x} {x'} f =
           ap (_∙ weakenSequentMorphism H (𝒢X ⟨ f ⟩)) (sumStep x)
        ⨾  sym (weakenedSequentMorphism-composition identity identity (𝒢X ⟨ f ⟩) (toSequentMorphism (σse x)))
        ⨾  ap (λ m → weakenedSequentMorphism m (toSequentMorphism (σse x) ∙ 𝒢X ⟨ f ⟩)) idCM＝
        ⨾  ap (weakenedSequentMorphism identity) (SequentStructureMorphism.natural σ f)
        ⨾  sym (ap (λ m → weakenedSequentMorphism m (𝒢Y ⟨ Φ ⟨ f ⟩ ⟩ ∙ toSequentMorphism (σse x'))) idCM＝)
        ⨾  weakenedSequentMorphism-composition identity identity (toSequentMorphism (σse x')) (𝒢Y ⟨ Φ ⟨ f ⟩ ⟩)
        ⨾  sym (ap (weakenSequentMorphism H (𝒢Y ⟨ Φ ⟨ f ⟩ ⟩) ∙_) (sumStep x'))

      natural-rl : {x : Ob 𝒟X}
                   {w : Ob (SequentStructure.dependency (SequentDependencyStructure.sequentStructure Bd))}
                   (g : ⌞ (SequentDependencyStructure.dependency Bd ⟨ w ⟩) ⌟)
                 → toSequentMorphism (seqEq (inr x))
                     ∙ mkSequentMorphism (→⋊ (weakenSequent H (𝒢X ⟨ x ⟩)) ∙ (inlContext ∙ rB w g))
                   ＝ mkSequentMorphism (→⋊ (weakenSequent H (𝒢Y ⟨ Φ ⟨ x ⟩ ⟩)) ∙ (inlContext ∙ rB w g))
                     ∙ toSequentMorphism (sequentEquivalence-identity {s = ℱB ⟨ w ⟩})
      natural-rl {x} {w} g =
        ap mkSequentMorphism (eq (record { component≈ = λ j → funExt (pw j) }))
        where
          tsm = SequentMorphism.sequentMorphism (toSequentMorphism (seqEq (inr x)))
          idM = SequentMorphism.sequentMorphism
                  (toSequentMorphism (sequentEquivalence-identity {s = ℱB ⟨ w ⟩}))
          rhsM = →⋊ (weakenSequent H (𝒢Y ⟨ Φ ⟨ x ⟩ ⟩)) ∙ (inlContext ∙ rB w g)
          lhsM = tsm ∙ (→⋊ (weakenSequent H (𝒢X ⟨ x ⟩)) ∙ (inlContext ∙ rB w g))

          pw : (j : type (Judgment 𝒥)) (z : ⌞ extendedContext (ℱB ⟨ w ⟩) ⟨ j ⟩ ⌟)
             → (lhsM ⟨ j ⟩) z ＝ ((rhsM ∙ idM) ⟨ j ⟩) z
          pw j z =
               map⋊-sum-onAdded (ContextEquivalence.morphism idH-equiv)
                                (ContextEquivalence.morphism (SequentEquivalence.contextEquivalence (σse x)))
                                (Sequent.extensionOrCollapse (𝒢X ⟨ x ⟩))
                                (Sequent.extensionOrCollapse (𝒢Y ⟨ Φ ⟨ x ⟩ ⟩))
                                (SequentEquivalence.extensionOrCollapseEquality (σse x))
                                j ((rB w g ⟨ j ⟩) z)
            ⨾  sym (ap (rhsM ⟨ j ⟩) (toSequentMorphism-identity-at {s = ℱB ⟨ w ⟩} j z))



-- =============== Reassociation of weakenings ===============

module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a} where

  private
    idSquareᵃ : {l₀ l₁ : Level} {s₀ : Sequent 𝒥 l₀} {s₁ : Sequent 𝒥 l₁}
                (α : SequentMorphism s₀ s₁)
              → toSequentMorphism (sequentEquivalence-identity {s = s₁}) ∙ α
                ＝ α ∙ toSequentMorphism (sequentEquivalence-identity {s = s₀})
    idSquareᵃ {s₀ = s₀} {s₁ = s₁} α =
      ap mkSequentMorphism (eq (record { component≈ = λ j → funExt (λ z →
           toSequentMorphism-identity-at {s = s₁} j ((SequentMorphism.sequentMorphism α ⟨ j ⟩) z)
        ⨾  sym (ap (SequentMorphism.sequentMorphism α ⟨ j ⟩)
                   (toSequentMorphism-identity-at {s = s₀} j z))) }))

    idSquareSME : {l₀ l₁ : Level} {s₀ : Sequent 𝒥 l₀} {s₁ : Sequent 𝒥 l₁}
                  (α : SequentMorphism s₀ s₁)
                → SequentMorphismEquality
                    (toSequentMorphism (sequentEquivalence-identity {s = s₁}) ∙ α)
                    (α ∙ toSequentMorphism (sequentEquivalence-identity {s = s₀}))
    idSquareSME α = observe ⦃ equalitySequentMorphism ⦄ (idSquareᵃ α)

    killIdᵣ : {l₀ l₁ : Level} {s₀ : Sequent 𝒥 l₀} {s₁ : Sequent 𝒥 l₁}
              (α : SequentMorphism s₀ s₁)
            → α ∙ toSequentMorphism (sequentEquivalence-identity {s = s₀}) ＝ α
    killIdᵣ {s₀ = s₀} α =
      ap mkSequentMorphism (eq (record { component≈ = λ j → funExt (λ z →
        ap (SequentMorphism.sequentMorphism α ⟨ j ⟩)
           (toSequentMorphism-identity-at {s = s₀} j z)) }))

  ⧺-assocEquality :
      (b₁ b₀ : ContextWithTerms 𝒥 so sa i) (X : SequentStructure 𝒥 so sa i)
    → SequentStructureEquality ((b₁ ⧺ᶜ b₀) ⧺ X) (b₁ ⧺ (b₀ ⧺ X))
  ⧺-assocEquality b₁ b₀ X =
    record
      { dependency≈ = record
          { objects≈ = assocSum
          ; hom≈ = hom≈'
          ; composition≈ = λ
              { (inl (inl u)) (inl (inl v)) (inl (inl e)) f g → refl
              ; (inl (inr x)) (inl (inr y)) (inl (inr z)) f g → refl
              ; (inr p) (inr q) (inr r) f g → refl
              ; (inl (inr x)) (inl (inr y)) (inl (inl u)) f g → refl
              ; (inl (inr x)) (inl (inl u)) (inl (inl v)) f g → refl
              ; (inr p) (inr q) (inl (inl u)) f g → refl
              ; (inr p) (inr q) (inl (inr x)) f g → refl
              ; (inr p) (inl (inr x)) (inl (inr y)) f g → refl
              ; (inr p) (inl (inr x)) (inl (inl u)) f g → refl
              ; (inr p) (inl (inl u)) (inl (inl v)) f g → refl
              ; (inl (inl u)) (inl (inr x)) E () g
              ; (inl (inl u)) (inl (inl v)) (inl (inr x)) f ()
              ; (inl (inl u)) (inl (inl v)) (inr q) f ()
              ; (inl (inl u)) (inr q) E () g
              ; (inl (inr x)) (inl (inr y)) (inr q) f ()
              ; (inl (inr x)) (inl (inl u)) (inl (inr y)) f ()
              ; (inl (inr x)) (inl (inl u)) (inr q) f ()
              ; (inl (inr x)) (inr q) E () g
              ; (inr p) (inl (inl u)) (inl (inr x)) f ()
              ; (inr p) (inl (inl u)) (inr q) f ()
              ; (inr p) (inl (inr x)) (inr q) f () }
          ; associative≈ = λ A B E F f g h →
              allEqual ⦃ ＝-isLevel ⦃ SequentStructure.dependency-Hom-isSet (b₁ ⧺ (b₀ ⧺ X))
                                        (there assocSum A) (there assocSum F) ⦄ ⦄ _ _ }
      ; sequent≈ = seq≈
      ; natural≈ = λ
          { {inl (inl u)} {inl (inl v)} f → idSquareSME (ℱB₁ ⟨ f ⟩)
          ; {inl (inr x)} {inl (inr y)} f →
              idSquareSME (weakenSequentMorphism h₁ (ℱB₀ ⟨ f ⟩))
          ; {inl (inr x)} {inl (inl u)} g →
              idSquareSME (mkSequentMorphism
                {s₁ = ℱB₁ ⟨ u ⟩} {s₂ = weakenSequent h₁ (ℱB₀ ⟨ x ⟩)}
                (→⋊ (weakenSequent h₁ (ℱB₀ ⟨ x ⟩))
                  ∙ (inlContext ∙ rB₁ u g)))
          ; {inr p} {inr q} f → natural-rr p q f
          ; {inr p} {inl (inl u)} g → natural-r-ll p u g
          ; {inr p} {inl (inr x)} g → natural-r-lr p x g
          ; {inl (inl u)} {inl (inr x)} ()
          ; {inl (inl u)} {inr q} ()
          ; {inl (inr x)} {inr q} () } }
    where
      bd₁ = ContextWithTerms.contextWithTerms b₁
      bd₀ = ContextWithTerms.contextWithTerms b₀
      h₁ = SequentDependencyStructure.head bd₁
      h₀ = SequentDependencyStructure.head bd₀
      ℱB₁ = SequentStructure.sequent (SequentDependencyStructure.sequentStructure bd₁)
      ℱB₀ = SequentStructure.sequent (SequentDependencyStructure.sequentStructure bd₀)
      rB₁ = SequentDependencyStructure.realiseDependency bd₁
      rB₀ = SequentDependencyStructure.realiseDependency bd₀
      𝒟X = SequentStructure.dependency X
      𝒢X = SequentStructure.sequent X

      hom≈' : (A B : Ob (SequentStructure.dependency ((b₁ ⧺ᶜ b₀) ⧺ X)))
            → Hom (SequentStructure.dependency ((b₁ ⧺ᶜ b₀) ⧺ X)) A B
            ≃ Hom (SequentStructure.dependency (b₁ ⧺ (b₀ ⧺ X)))
                  (there assocSum A) (there assocSum B)
      hom≈' (inl (inl u)) (inl (inl v)) = ≃-id
      hom≈' (inl (inr x)) (inl (inr y)) = ≃-id
      hom≈' (inr p) (inr q) = ≃-id
      hom≈' (inl (inr x)) (inl (inl u)) = ≃-id
      hom≈' (inr p) (inl (inl u)) = ≃-id
      hom≈' (inr p) (inl (inr x)) = ≃-id
      hom≈' (inl (inl u)) (inl (inr x)) = ≃-id
      hom≈' (inl (inl u)) (inr q) = ≃-id
      hom≈' (inl (inr x)) (inr q) = ≃-id

      seq≈ : (A : Ob (SequentStructure.dependency ((b₁ ⧺ᶜ b₀) ⧺ X)))
           → SequentEquivalence (SequentStructure.sequent ((b₁ ⧺ᶜ b₀) ⧺ X) ⟨ A ⟩)
                                (SequentStructure.sequent (b₁ ⧺ (b₀ ⧺ X)) ⟨ there assocSum A ⟩)
      seq≈ (inl (inl u)) = sequentEquivalence-identity
      seq≈ (inl (inr x)) = sequentEquivalence-identity
      seq≈ (inr p) = assocWeakenSequentEquivalence h₁ h₀ (𝒢X ⟨ p ⟩)

      natural-rr : (p q : Ob 𝒟X) (f : Hom 𝒟X p q)
                 → SequentMorphismEquality
                     (toSequentMorphism (seq≈ (inr p))
                       ∙ weakenSequentMorphism (h₁ + h₀) (𝒢X ⟨ f ⟩))
                     (weakenSequentMorphism h₁ (weakenSequentMorphism h₀ (𝒢X ⟨ f ⟩))
                       ∙ toSequentMorphism (seq≈ (inr q)))
      natural-rr p q f =
        observe ⦃ equalitySequentMorphism ⦄
          (ap mkSequentMorphism
             (map⋊-assoc-square h₁ h₀
               (Sequent.extensionOrCollapse (𝒢X ⟨ q ⟩))
               (Sequent.extensionOrCollapse (𝒢X ⟨ p ⟩))
               (𝒢X ⟨ f ⟩)))

      natural-r-ll : (p : Ob 𝒟X)
                     (u : Ob (SequentStructure.dependency (SequentDependencyStructure.sequentStructure bd₁)))
                     (g : ⌞ (SequentDependencyStructure.dependency bd₁ ⟨ u ⟩) ⌟)
                   → SequentMorphismEquality
                       (toSequentMorphism (seq≈ (inr p))
                         ∙ mkSequentMorphism
                             {s₁ = ℱB₁ ⟨ u ⟩} {s₂ = weakenSequent (h₁ + h₀) (𝒢X ⟨ p ⟩)}
                             (→⋊ (weakenSequent (h₁ + h₀) (𝒢X ⟨ p ⟩))
                               ∙ (inlContext ∙ (inlContext {Γ = h₁} {Δ = h₀} ∙ rB₁ u g))))
                       (mkSequentMorphism
                           {s₁ = ℱB₁ ⟨ u ⟩}
                           {s₂ = weakenSequent h₁ (weakenSequent h₀ (𝒢X ⟨ p ⟩))}
                           (→⋊ (weakenSequent h₁ (weakenSequent h₀ (𝒢X ⟨ p ⟩)))
                             ∙ (inlContext ∙ rB₁ u g))
                         ∙ toSequentMorphism (sequentEquivalence-identity {s = ℱB₁ ⟨ u ⟩}))
      natural-r-ll p u g =
        observe ⦃ equalitySequentMorphism ⦄
          (   ap mkSequentMorphism
                (eq (record { component≈ = λ j → funExt (λ z →
                    map⋊-→⋊ (ContextEquivalence.morphism
                               (assocSumContextEquivalence {Γ = h₁} {Δ = h₀} {Ψ = Sequent.context (𝒢X ⟨ p ⟩)}))
                            (mapExtensionOrCollapse (inrContext {Γ = h₁ + h₀} {Δ = Sequent.context (𝒢X ⟨ p ⟩)})
                               (Sequent.extensionOrCollapse (𝒢X ⟨ p ⟩)))
                            (mapExtensionOrCollapse (inrContext {Γ = h₁} {Δ = h₀ + Sequent.context (𝒢X ⟨ p ⟩)})
                               (mapExtensionOrCollapse (inrContext {Γ = h₀} {Δ = Sequent.context (𝒢X ⟨ p ⟩)})
                                  (Sequent.extensionOrCollapse (𝒢X ⟨ p ⟩))))
                            (assocEocEquality h₁ h₀ (Sequent.extensionOrCollapse (𝒢X ⟨ p ⟩)))
                            j (inl (inl ((rB₁ u g ⟨ j ⟩) z))) ) }))
           ⨾  sym (killIdᵣ (mkSequentMorphism
                 {s₁ = ℱB₁ ⟨ u ⟩}
                 {s₂ = weakenSequent h₁ (weakenSequent h₀ (𝒢X ⟨ p ⟩))}
                 (→⋊ (weakenSequent h₁ (weakenSequent h₀ (𝒢X ⟨ p ⟩)))
                   ∙ (inlContext ∙ rB₁ u g)))))

      natural-r-lr : (p : Ob 𝒟X)
                     (x : Ob (SequentStructure.dependency (SequentDependencyStructure.sequentStructure bd₀)))
                     (g : ⌞ (SequentDependencyStructure.dependency bd₀ ⟨ x ⟩) ⌟)
                   → SequentMorphismEquality
                       (toSequentMorphism (seq≈ (inr p))
                         ∙ mkSequentMorphism
                             {s₁ = weakenSequent h₁ (ℱB₀ ⟨ x ⟩)}
                             {s₂ = weakenSequent (h₁ + h₀) (𝒢X ⟨ p ⟩)}
                             (→⋊ (weakenSequent (h₁ + h₀) (𝒢X ⟨ p ⟩))
                               ∙ (inlContext
                               ∙ (sumContextMorphism (identityH h₁) (rB₀ x g)
                               ∙ distributeExtended h₁ (ℱB₀ ⟨ x ⟩)))))
                       (weakenSequentMorphism h₁
                           (mkSequentMorphism
                             {s₁ = ℱB₀ ⟨ x ⟩} {s₂ = weakenSequent h₀ (𝒢X ⟨ p ⟩)}
                             (→⋊ (weakenSequent h₀ (𝒢X ⟨ p ⟩))
                             ∙ (inlContext ∙ rB₀ x g)))
                         ∙ toSequentMorphism (sequentEquivalence-identity {s = weakenSequent h₁ (ℱB₀ ⟨ x ⟩)}))
      natural-r-lr p x g =
        observe ⦃ equalitySequentMorphism ⦄
          (   ap mkSequentMorphism
                (map⋊-assoc-cross h₁ h₀ (𝒢X ⟨ p ⟩)
                  (Sequent.extensionOrCollapse (ℱB₀ ⟨ x ⟩)) (rB₀ x g))
           ⨾  sym (killIdᵣ (weakenSequentMorphism h₁
                 (mkSequentMorphism
                   {s₁ = ℱB₀ ⟨ x ⟩} {s₂ = weakenSequent h₀ (𝒢X ⟨ p ⟩)}
                   (→⋊ (weakenSequent h₀ (𝒢X ⟨ p ⟩))
                   ∙ (inlContext ∙ rB₀ x g))))))


-- =============== Associativity of the collage of contexts with terms ===============

module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a} where

  ⧺ᶜ-assocEquality :
      (b₂ b₁ b₀ : ContextWithTerms 𝒥 so sa i)
    → ContextWithTermsEquality ((b₂ ⧺ᶜ b₁) ⧺ᶜ b₀) (b₂ ⧺ᶜ (b₁ ⧺ᶜ b₀))
  ⧺ᶜ-assocEquality b₂ b₁ b₀ =
    record
      { contextWithTerms≈ = record
          { head≈ = assocSumContextEquivalence
          ; sequentStructure≈ = ⧺-assocEquality b₂ b₁ (SequentDependencyStructure.sequentStructure bd₀)
          ; terms≈ = λ { (inl (inl w)) → ≃-id ; (inl (inr x)) → ≃-id ; (inr y) → ≃-id }
          ; termsNatural = λ
              { {inl (inl w)} {inl (inl w')} g → refl
              ; {inl (inr x)} {inl (inr x')} g → refl
              ; {inr y} {inr y'} g → refl
              ; {inl (inr x)} {inl (inl w)} g → refl
              ; {inr y} {inl (inl w)} g → refl
              ; {inr y} {inl (inr x)} g → refl
              ; {inl (inl w)} {inl (inr x)} ()
              ; {inl (inl w)} {inr y} ()
              ; {inl (inr x)} {inr y} () }
          ; realise≈ = λ { (inl (inl w)) u → r-b₂ w u
                         ; (inl (inr x)) u → r-b₁ x u
                         ; (inr y) u → r-b₀ y u } } }
    where
      bd₂ = ContextWithTerms.contextWithTerms b₂
      bd₁ = ContextWithTerms.contextWithTerms b₁
      bd₀ = ContextWithTerms.contextWithTerms b₀
      h₂ = SequentDependencyStructure.head bd₂
      h₁ = SequentDependencyStructure.head bd₁
      h₀ = SequentDependencyStructure.head bd₀
      ℱ₂ = SequentStructure.sequent (SequentDependencyStructure.sequentStructure bd₂)
      ℱ₁ = SequentStructure.sequent (SequentDependencyStructure.sequentStructure bd₁)
      ℱ₀ = SequentStructure.sequent (SequentDependencyStructure.sequentStructure bd₀)
      r₂ = SequentDependencyStructure.realiseDependency bd₂
      r₁ = SequentDependencyStructure.realiseDependency bd₁
      r₀ = SequentDependencyStructure.realiseDependency bd₀

      assocM = ContextEquivalence.morphism (assocSumContextEquivalence {Γ = h₂} {Δ = h₁} {Ψ = h₀})
      idSM₂ = λ w → SequentMorphism.sequentMorphism
                      (toSequentMorphism (sequentEquivalence-identity {s = ℱ₂ ⟨ w ⟩}))
      idSM₁ = λ x → SequentMorphism.sequentMorphism
                      (toSequentMorphism (sequentEquivalence-identity {s = weakenSequent h₂ (ℱ₁ ⟨ x ⟩)}))
      assocSM₀ = λ y → SequentMorphism.sequentMorphism
                         (toSequentMorphism (assocWeakenSequentEquivalence h₂ h₁ (ℱ₀ ⟨ y ⟩)))

      lhs₂ = λ w u → assocM ∙ (inlContext {Γ = h₂ + h₁} {Δ = h₀} ∙ (inlContext {Γ = h₂} {Δ = h₁} ∙ r₂ w u))
      rhs₂ = λ w u → (inlContext {Γ = h₂} {Δ = h₁ + h₀} ∙ r₂ w u) ∙ idSM₂ w
      lhs₁ = λ x u → assocM ∙ (inlContext {Γ = h₂ + h₁} {Δ = h₀}
                     ∙ (sumContextMorphism (identityH h₂) (r₁ x u) ∙ distributeExtended h₂ (ℱ₁ ⟨ x ⟩)))
      rhs₁ = λ x u → (sumContextMorphism (identityH h₂) (inlContext {Γ = h₁} {Δ = h₀} ∙ r₁ x u)
                       ∙ distributeExtended h₂ (ℱ₁ ⟨ x ⟩)) ∙ idSM₁ x
      lhs₀ = λ y u → assocM ∙ (sumContextMorphism (identityH (h₂ + h₁)) (r₀ y u)
                       ∙ distributeExtended (h₂ + h₁) (ℱ₀ ⟨ y ⟩))
      rhs₀ = λ y u → (sumContextMorphism (identityH h₂)
                        (sumContextMorphism (identityH h₁) (r₀ y u) ∙ distributeExtended h₁ (ℱ₀ ⟨ y ⟩))
                       ∙ distributeExtended h₂ (weakenSequent h₁ (ℱ₀ ⟨ y ⟩))) ∙ assocSM₀ y

      r-b₂ : ∀ w u → ContextMorphismEquality (lhs₂ w u) (rhs₂ w u)
      r-b₂ w u =
        record { component≈ = λ j → funExt (λ z →
            sym (ap (λ v → inl ((r₂ w u ⟨ j ⟩) v))
                    (toSequentMorphism-identity-at {s = ℱ₂ ⟨ w ⟩} j z))) }

      r-b₁ : ∀ x u → ContextMorphismEquality (lhs₁ x u) (rhs₁ x u)
      r-b₁ x u =
        record { component≈ = λ j → funExt (λ z →
             helper j ((distributeExtended h₂ (ℱ₁ ⟨ x ⟩) ⟨ j ⟩) z)
          ⨾  sym (ap ((sumContextMorphism (identityH h₂)
                        (inlContext {Γ = h₁} {Δ = h₀} ∙ r₁ x u)
                      ∙ distributeExtended h₂ (ℱ₁ ⟨ x ⟩)) ⟨ j ⟩)
                     (toSequentMorphism-identity-at {s = weakenSequent h₂ (ℱ₁ ⟨ x ⟩)} j z))) }
        where
          helper : (j : type (Judgment 𝒥)) (v : ⌞ (h₂ + extendedContext (ℱ₁ ⟨ x ⟩)) ⟨ j ⟩ ⌟)
                 → (assocM ⟨ j ⟩)
                     (inl ((sumContextMorphism (identityH h₂) (r₁ x u) ⟨ j ⟩) v))
                   ＝ (sumContextMorphism (identityH h₂)
                        (inlContext {Γ = h₁} {Δ = h₀} ∙ r₁ x u) ⟨ j ⟩) v
          helper j (inl h) = refl
          helper j (inr e) = refl

      r-b₀ : ∀ y u → ContextMorphismEquality (lhs₀ y u) (rhs₀ y u)
      r-b₀ y u =
        observe ⦃ equalityContextMorphism ⦄
          (map⋊-assoc-realise h₂ h₁ (Sequent.extensionOrCollapse (ℱ₀ ⟨ y ⟩)) (r₀ y u))


