module SequentDependencyStructure.Equality where

open import Prelude
open import Axioms
open import Algebra.Wild.Semicategory
open import Algebra.Wild.Semifunctor
open Semicategory
open import Algebra.Wild.TruncatedTypeSemicategory
open import Homotopy.Equality
open import Homotopy.Fibre
open import Homotopy.Levels
open import Homotopy.StructuredType
open import Homotopy.SetQuotient.Nominal
open import Structure.Composable
open import Structure.PreservesComposition
open import Structure.Symmetric
open import Foundation.Empty

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

open SequentDependencyStructure.SequentDependencyStructure

-- ============= Equality of sequent dependency structures =============


record SequentDependencyStructureEquality
  ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a t l so sa i : Level} {𝒥 : DependentSortVocabulary o a}
  {A : Type t} {f : A → Context 𝒥 i}
  (A≈ : A → A → Type l)
  (headContext≈ : {x y : A} → A≈ x y → ContextEquivalence (f x) (f y))
  (c₀ c₁ : SequentDependencyStructure 𝒥 so sa i A f)
  : Type (o ⊔ a ⊔ so ⊔ sa ⊔ lsuc i ⊔ l) where
  constructor mkSequentDependencyStructureEquality
  field
    head≈ : A≈ (head c₀) (head c₁)
    sequentStructure≈ : SequentStructureEquality (sequentStructure c₀) (sequentStructure c₁)
    terms≈ : (x : Ob (SequentStructure.dependency (sequentStructure c₀)))
            → ⌞ (dependency c₀ ⟨ x ⟩) ⌟
              ≃ ⌞ (dependency c₁
                    ⟨ there (Semicategory-Equality.objects≈
                                (SequentStructureEquality.dependency≈ sequentStructure≈)) x ⟩) ⌟
    termsNatural :
        {x y : Ob (SequentStructure.dependency (sequentStructure c₀))}
        (g : Hom (SequentStructure.dependency (sequentStructure c₀)) x y)
      → (dependency c₁
            ⟨ there (Semicategory-Equality.hom≈
                        (SequentStructureEquality.dependency≈ sequentStructure≈) x y) g ⟩)
          ∘ there (terms≈ x)
        ＝ there (terms≈ y) ∘ (dependency c₀ ⟨ g ⟩)
    realise≈ :
        (x : Ob (SequentStructure.dependency (sequentStructure c₀)))
        (u : ⌞ (dependency c₀ ⟨ x ⟩) ⌟)
      → ContextMorphismEquality
          (ContextEquivalence.morphism (headContext≈ head≈) ∙ realiseDependency c₀ x u)
          (realiseDependency c₁ _ (there (terms≈ x) u)
            ∙ SequentMorphism.sequentMorphism
                (toSequentMorphism (SequentStructureEquality.sequent≈ sequentStructure≈ x)))
open SequentDependencyStructureEquality


module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a t l so sa i : Level} {𝒥 : DependentSortVocabulary o a}
  {A : Type t} {f : A → Context 𝒥 i}
  (A≈ : A → A → Type l)
  (A-refl≈ : (x : A) → A≈ x x)
  (A-total : (x : A) → Contractible (∑[ y ∶ A ] A≈ x y))
  (headContext≈ : {x y : A} → A≈ x y → ContextEquivalence (f x) (f y))
  (headContext≈-refl : (x : A) (j : type (Judgment 𝒥)) (z : ⌞ (f x) ⟨ j ⟩ ⌟)
                     → (ContextEquivalence.morphism (headContext≈ (A-refl≈ x)) ⟨ j ⟩) z ＝ z)
  where

  identitySequentDependencyStructureEquality :
      (c : SequentDependencyStructure 𝒥 so sa i A f)
    → SequentDependencyStructureEquality A≈ headContext≈ c c
  identitySequentDependencyStructureEquality c =
    record
      { head≈ = A-refl≈ (head c)
      ; sequentStructure≈ = identitySequentStructureEquality (sequentStructure c)
      ; terms≈ = λ x → ≃-id
      ; termsNatural = λ g → refl
      ; realise≈ = λ x u →
          record { component≈ = λ j → funExt (λ z →
               headContext≈-refl (head c) j ((realiseDependency c x u ⟨ j ⟩) z)
            ⨾  sym (ap (realiseDependency c x u ⟨ j ⟩)
                       (toSequentMorphism-identity-at
                          {s = SequentStructure.sequent (sequentStructure c) ⟨ x ⟩} j z))) } }

  private
    realiseAt-Contractible :
        (ss : SequentStructure 𝒥 so sa i)
        (dep₀ : Semifunctor (SequentStructure.dependency ss) (hSet-Semicategory sa))
        (h₀ h₁ : A) (hh : A≈ h₀ h₁)
        (real₀ : (x : Ob (SequentStructure.dependency ss))
                 → ⌞ (dep₀ ⟨ x ⟩) ⌟
                 → ContextMorphism (extendedContext (SequentStructure.sequent ss ⟨ x ⟩)) (f h₀))
        (x : Ob (SequentStructure.dependency ss))
      → Contractible
          (∑[ r ∶ (⌞ (dep₀ ⟨ x ⟩) ⌟
                    → ContextMorphism (extendedContext (SequentStructure.sequent ss ⟨ x ⟩)) (f h₁)) ]
             ((u : ⌞ (dep₀ ⟨ x ⟩) ⌟)
               → ContextMorphismEquality
                   (ContextEquivalence.morphism (headContext≈ hh) ∙ real₀ x u)
                   (r u ∙ SequentMorphism.sequentMorphism
                            (toSequentMorphism
                               (sequentEquivalence-identity
                                  {s = SequentStructure.sequent ss ⟨ x ⟩})))))
    realiseAt-Contractible ss dep₀ h₀ h₁ hh real₀ x =
      Π-witness-Contractible
        (λ u m → ContextMorphismEquality
                   (ContextEquivalence.morphism (headContext≈ hh) ∙ real₀ x u)
                   (m ∙ SequentMorphism.sequentMorphism
                          (toSequentMorphism
                             (sequentEquivalence-identity
                                {s = SequentStructure.sequent ss ⟨ x ⟩}))))
        (λ u → contextArrowFibre-Contractible
                 (SequentMorphism.sequentMorphism
                    (toSequentMorphism
                       (sequentEquivalence-identity {s = SequentStructure.sequent ss ⟨ x ⟩})))
                 (toSequentMorphism-isEquivalence
                    (sequentEquivalence-identity {s = SequentStructure.sequent ss ⟨ x ⟩}))
                 (ContextEquivalence.morphism (headContext≈ hh) ∙ real₀ x u))

    realiseOver-Contractible :
        (ss : SequentStructure 𝒥 so sa i)
        (dep₀ : Semifunctor (SequentStructure.dependency ss) (hSet-Semicategory sa))
        (h₀ h₁ : A) (hh : A≈ h₀ h₁)
        (real₀ : (x : Ob (SequentStructure.dependency ss))
                 → ⌞ (dep₀ ⟨ x ⟩) ⌟
                 → ContextMorphism (extendedContext (SequentStructure.sequent ss ⟨ x ⟩)) (f h₀))
      → Contractible
          (∑[ r ∶ ((x : Ob (SequentStructure.dependency ss))
                    → ⌞ (dep₀ ⟨ x ⟩) ⌟
                    → ContextMorphism (extendedContext (SequentStructure.sequent ss ⟨ x ⟩)) (f h₁)) ]
             ((x : Ob (SequentStructure.dependency ss)) (u : ⌞ (dep₀ ⟨ x ⟩) ⌟)
               → ContextMorphismEquality
                   (ContextEquivalence.morphism (headContext≈ hh) ∙ real₀ x u)
                   (r x u ∙ SequentMorphism.sequentMorphism
                              (toSequentMorphism
                                 (sequentEquivalence-identity
                                    {s = SequentStructure.sequent ss ⟨ x ⟩})))))
    realiseOver-Contractible ss dep₀ h₀ h₁ hh real₀ =
      Π-witness-Contractible
        (λ x r → (u : ⌞ (dep₀ ⟨ x ⟩) ⌟)
               → ContextMorphismEquality
                   (ContextEquivalence.morphism (headContext≈ hh) ∙ real₀ x u)
                   (r u ∙ SequentMorphism.sequentMorphism
                            (toSequentMorphism
                               (sequentEquivalence-identity
                                  {s = SequentStructure.sequent ss ⟨ x ⟩}))))
        (λ x → realiseAt-Contractible ss dep₀ h₀ h₁ hh real₀ x)

    realiseReindexed-Contractible :
        (ss : SequentStructure 𝒥 so sa i)
        (dep₀ dep₁ : Semifunctor (SequentStructure.dependency ss) (hSet-Semicategory sa))
        (te : (x : Ob (SequentStructure.dependency ss))
              → ⌞ (dep₀ ⟨ x ⟩) ⌟ ≃ ⌞ (dep₁ ⟨ x ⟩) ⌟)
        (h₀ h₁ : A) (hh : A≈ h₀ h₁)
        (real₀ : (x : Ob (SequentStructure.dependency ss))
                 → ⌞ (dep₀ ⟨ x ⟩) ⌟
                 → ContextMorphism (extendedContext (SequentStructure.sequent ss ⟨ x ⟩)) (f h₀))
      → Contractible
          (∑[ r ∶ ((x : Ob (SequentStructure.dependency ss))
                    → ⌞ (dep₁ ⟨ x ⟩) ⌟
                    → ContextMorphism (extendedContext (SequentStructure.sequent ss ⟨ x ⟩)) (f h₁)) ]
             ((x : Ob (SequentStructure.dependency ss)) (u : ⌞ (dep₀ ⟨ x ⟩) ⌟)
               → ContextMorphismEquality
                   (ContextEquivalence.morphism (headContext≈ hh) ∙ real₀ x u)
                   (r x (there (te x) u)
                     ∙ SequentMorphism.sequentMorphism
                         (toSequentMorphism
                            (sequentEquivalence-identity
                               {s = SequentStructure.sequent ss ⟨ x ⟩})))))
    realiseReindexed-Contractible ss dep₀ dep₁ te h₀ h₁ hh real₀ =
      ≃-Contractible
        (sym (equiv-∑ (equiv-Π (λ x → precompose-≃ (te x))) (λ r → ≃-id)))
        (realiseOver-Contractible ss dep₀ h₀ h₁ hh real₀)

    CoherenceOf : (ss : SequentStructure 𝒥 so sa i)
                  (dep : Semifunctor (SequentStructure.dependency ss) (hSet-Semicategory sa))
                  (h : A)
                → ((x : Ob (SequentStructure.dependency ss))
                    → ⌞ (dep ⟨ x ⟩) ⌟
                    → ContextMorphism (extendedContext (SequentStructure.sequent ss ⟨ x ⟩)) (f h))
                → Type (o ⊔ a ⊔ so ⊔ sa ⊔ i)
    CoherenceOf ss dep h real =
      (d₀ d₁ : Ob (SequentStructure.dependency ss))
      (u : ⌞ (dep ⟨ d₀ ⟩) ⌟)
      (g : Hom (SequentStructure.dependency ss) d₀ d₁)
      → real d₁ ((dep ⟨ g ⟩) u)
        ＝ real d₀ u ∙ SequentMorphism.sequentMorphism (SequentStructure.sequent ss ⟨ g ⟩)

    coherenceOf-isProposition :
        (ss : SequentStructure 𝒥 so sa i)
        (dep : Semifunctor (SequentStructure.dependency ss) (hSet-Semicategory sa))
        (h : A)
        (real : (x : Ob (SequentStructure.dependency ss))
                → ⌞ (dep ⟨ x ⟩) ⌟
                → ContextMorphism (extendedContext (SequentStructure.sequent ss ⟨ x ⟩)) (f h))
      → isProposition (CoherenceOf ss dep h real)
    coherenceOf-isProposition ss dep h real =
      →-level λ d₀ → →-level λ d₁ → →-level λ u → →-level λ g →
        ＝-isLevel ⦃ contextMorphism-isSet ⦄

    transportedRealise :
        (ss : SequentStructure 𝒥 so sa i)
        (dep : Semifunctor (SequentStructure.dependency ss) (hSet-Semicategory sa))
        (h₀ h₁ : A) (hh : A≈ h₀ h₁)
        (real₀ : (x : Ob (SequentStructure.dependency ss))
                 → ⌞ (dep ⟨ x ⟩) ⌟
                 → ContextMorphism (extendedContext (SequentStructure.sequent ss ⟨ x ⟩)) (f h₀))
        (x : Ob (SequentStructure.dependency ss))
      → ⌞ (dep ⟨ x ⟩) ⌟
      → ContextMorphism (extendedContext (SequentStructure.sequent ss ⟨ x ⟩)) (f h₁)
    transportedRealise ss dep h₀ h₁ hh real₀ x u =
      ContextEquivalence.morphism (headContext≈ hh) ∙ real₀ x u

    transportedCoherence :
        (ss : SequentStructure 𝒥 so sa i)
        (dep : Semifunctor (SequentStructure.dependency ss) (hSet-Semicategory sa))
        (h₀ h₁ : A) (hh : A≈ h₀ h₁)
        (real₀ : (x : Ob (SequentStructure.dependency ss))
                 → ⌞ (dep ⟨ x ⟩) ⌟
                 → ContextMorphism (extendedContext (SequentStructure.sequent ss ⟨ x ⟩)) (f h₀))
      → CoherenceOf ss dep h₀ real₀
      → CoherenceOf ss dep h₁ (transportedRealise ss dep h₀ h₁ hh real₀)
    transportedCoherence ss dep h₀ h₁ hh real₀ coh d₀ d₁ u g =
      eq (record { component≈ = λ j → funExt (λ z →
           ap (λ v → (ContextEquivalence.morphism (headContext≈ hh) ⟨ j ⟩)
                       ((v ⟨ j ⟩) z))
              (coh d₀ d₁ u g)) })

    DepData : (ss : SequentStructure 𝒥 so sa i)
            → Semifunctor (SequentStructure.dependency ss) (hSet-Semicategory sa)
            → Type (so ⊔ lsuc sa)
    DepData ss dep₀ =
      ∑[ dep₁ ∶ Semifunctor (SequentStructure.dependency ss) (hSet-Semicategory sa) ]
        ∑[ te ∶ ((x : Ob (SequentStructure.dependency ss))
                  → ⌞ (dep₀ ⟨ x ⟩) ⌟ ≃ ⌞ (dep₁ ⟨ x ⟩) ⌟) ]
          ({x y : Ob (SequentStructure.dependency ss)}
             (g : Hom (SequentStructure.dependency ss) x y)
           → (dep₁ ⟨ g ⟩) ∘ there (te x) ＝ there (te y) ∘ (dep₀ ⟨ g ⟩))

    RealData : (ss : SequentStructure 𝒥 so sa i)
               (dep₀ : Semifunctor (SequentStructure.dependency ss) (hSet-Semicategory sa))
               (h₀ h₁ : A) (hh : A≈ h₀ h₁)
               (real₀ : (x : Ob (SequentStructure.dependency ss))
                        → ⌞ (dep₀ ⟨ x ⟩) ⌟
                        → ContextMorphism
                            (extendedContext (SequentStructure.sequent ss ⟨ x ⟩)) (f h₀))
             → DepData ss dep₀ → Type (o ⊔ a ⊔ so ⊔ sa ⊔ i)
    RealData ss dep₀ h₀ h₁ hh real₀ D =
      ∑[ r ∶ ((x : Ob (SequentStructure.dependency ss))
               → ⌞ (p₀ D ⟨ x ⟩) ⌟
               → ContextMorphism (extendedContext (SequentStructure.sequent ss ⟨ x ⟩)) (f h₁)) ]
        ((x : Ob (SequentStructure.dependency ss)) (u : ⌞ (dep₀ ⟨ x ⟩) ⌟)
          → ContextMorphismEquality
              (ContextEquivalence.morphism (headContext≈ hh) ∙ real₀ x u)
              (r x (there (p₀ (p₁ D) x) u)
                ∙ SequentMorphism.sequentMorphism
                    (toSequentMorphism
                       (sequentEquivalence-identity
                          {s = SequentStructure.sequent ss ⟨ x ⟩}))))

    baseFibre-Contractible :
        (ss : SequentStructure 𝒥 so sa i)
        (dep₀ : Semifunctor (SequentStructure.dependency ss) (hSet-Semicategory sa))
        (h₀ : A)
        (real₀ : (x : Ob (SequentStructure.dependency ss))
                 → ⌞ (dep₀ ⟨ x ⟩) ⌟
                 → ContextMorphism (extendedContext (SequentStructure.sequent ss ⟨ x ⟩)) (f h₀))
        (coh₀ : CoherenceOf ss dep₀ h₀ real₀)
        (h₁ : A) (hh : A≈ h₀ h₁)
      → Contractible
          (∑[ D ∶ DepData ss dep₀ ]
             ∑[ R ∶ RealData ss dep₀ h₀ h₁ hh real₀ D ]
               CoherenceOf ss (p₀ D) h₁ (p₀ R))
    baseFibre-Contractible ss dep₀ h₀ real₀ coh₀ h₁ hh =
      ∑-Contractible (dependencyTotalSpace-Contractible ss dep₀)
        (λ D → ∑-Contractible
                 (realiseReindexed-Contractible ss dep₀ (p₀ D) (p₀ (p₁ D)) h₀ h₁ hh real₀)
                 (λ R → cohContractible D R))
      where
        centreData : ∑[ D ∶ DepData ss dep₀ ] RealData ss dep₀ h₀ h₁ hh real₀ D
        centreData =
          (dep₀ , (λ x → ≃-id) , (λ g → refl))
          , transportedRealise ss dep₀ h₀ h₁ hh real₀
          , (λ x u → record { component≈ = λ j → funExt (λ z →
               sym (ap (λ v → (ContextEquivalence.morphism (headContext≈ hh) ⟨ j ⟩)
                                ((real₀ x u ⟨ j ⟩) v))
                       (toSequentMorphism-identity-at
                          {s = SequentStructure.sequent ss ⟨ x ⟩} j z))) })

        dataContractible : Contractible (∑[ D ∶ DepData ss dep₀ ] RealData ss dep₀ h₀ h₁ hh real₀ D)
        dataContractible =
          ∑-Contractible (dependencyTotalSpace-Contractible ss dep₀)
            (λ D → realiseReindexed-Contractible ss dep₀ (p₀ D) (p₀ (p₁ D)) h₀ h₁ hh real₀)

        cohContractible : (D : DepData ss dep₀) (R : RealData ss dep₀ h₀ h₁ hh real₀ D)
                        → Contractible (CoherenceOf ss (p₀ D) h₁ (p₀ R))
        cohContractible D R =
          inhabited-proposition→contractible
            ⦃ coherenceOf-isProposition ss (p₀ D) h₁ (p₀ R) ⦄
            (tr (λ w → CoherenceOf ss (p₀ (p₀ w)) h₁ (p₀ (p₁ w)))
                (sym (contraction dataContractible centreData)
                  ⨾ contraction dataContractible (D , R))
                (transportedCoherence ss dep₀ h₀ h₁ hh real₀ coh₀))

    DepDataOver : (ss₀ ss₁ : SequentStructure 𝒥 so sa i)
                  (ssw : SequentStructureEquality ss₀ ss₁)
                → Semifunctor (SequentStructure.dependency ss₀) (hSet-Semicategory sa)
                → Type (so ⊔ lsuc sa)
    DepDataOver ss₀ ss₁ ssw dep₀ =
      ∑[ dep₁ ∶ Semifunctor (SequentStructure.dependency ss₁) (hSet-Semicategory sa) ]
        ∑[ te ∶ ((x : Ob (SequentStructure.dependency ss₀))
                  → ⌞ (dep₀ ⟨ x ⟩) ⌟
                    ≃ ⌞ (dep₁ ⟨ there (Semicategory-Equality.objects≈
                                         (SequentStructureEquality.dependency≈ ssw)) x ⟩) ⌟) ]
          ({x y : Ob (SequentStructure.dependency ss₀)}
             (g : Hom (SequentStructure.dependency ss₀) x y)
           → (dep₁ ⟨ there (Semicategory-Equality.hom≈
                              (SequentStructureEquality.dependency≈ ssw) x y) g ⟩)
               ∘ there (te x)
             ＝ there (te y) ∘ (dep₀ ⟨ g ⟩))

    RealDataOver : (ss₀ ss₁ : SequentStructure 𝒥 so sa i)
                   (ssw : SequentStructureEquality ss₀ ss₁)
                   (dep₀ : Semifunctor (SequentStructure.dependency ss₀) (hSet-Semicategory sa))
                   (h₀ h₁ : A) (hh : A≈ h₀ h₁)
                   (real₀ : (x : Ob (SequentStructure.dependency ss₀))
                            → ⌞ (dep₀ ⟨ x ⟩) ⌟
                            → ContextMorphism
                                (extendedContext (SequentStructure.sequent ss₀ ⟨ x ⟩)) (f h₀))
                 → DepDataOver ss₀ ss₁ ssw dep₀ → Type (o ⊔ a ⊔ so ⊔ sa ⊔ i)
    RealDataOver ss₀ ss₁ ssw dep₀ h₀ h₁ hh real₀ D =
      ∑[ r ∶ ((x : Ob (SequentStructure.dependency ss₁))
               → ⌞ (p₀ D ⟨ x ⟩) ⌟
               → ContextMorphism (extendedContext (SequentStructure.sequent ss₁ ⟨ x ⟩)) (f h₁)) ]
        ((x : Ob (SequentStructure.dependency ss₀)) (u : ⌞ (dep₀ ⟨ x ⟩) ⌟)
          → ContextMorphismEquality
              (ContextEquivalence.morphism (headContext≈ hh) ∙ real₀ x u)
              (r _ (there (p₀ (p₁ D) x) u)
                ∙ SequentMorphism.sequentMorphism
                    (toSequentMorphism (SequentStructureEquality.sequent≈ ssw x))))

    SequentStructureFibre :
        (ss₀ ss₁ : SequentStructure 𝒥 so sa i)
        (ssw : SequentStructureEquality ss₀ ss₁)
        (dep₀ : Semifunctor (SequentStructure.dependency ss₀) (hSet-Semicategory sa))
        (h₀ h₁ : A) (hh : A≈ h₀ h₁)
        (real₀ : (x : Ob (SequentStructure.dependency ss₀))
                 → ⌞ (dep₀ ⟨ x ⟩) ⌟
                 → ContextMorphism
                     (extendedContext (SequentStructure.sequent ss₀ ⟨ x ⟩)) (f h₀))
      → Type (o ⊔ a ⊔ so ⊔ lsuc sa ⊔ i)
    SequentStructureFibre ss₀ ss₁ ssw dep₀ h₀ h₁ hh real₀ =
      ∑[ D ∶ DepDataOver ss₀ ss₁ ssw dep₀ ]
        ∑[ R ∶ RealDataOver ss₀ ss₁ ssw dep₀ h₀ h₁ hh real₀ D ]
          CoherenceOf ss₁ (p₀ D) h₁ (p₀ R)

    fibre-Contractible :
        (ss₀ : SequentStructure 𝒥 so sa i)
        (dep₀ : Semifunctor (SequentStructure.dependency ss₀) (hSet-Semicategory sa))
        (h₀ : A)
        (real₀ : (x : Ob (SequentStructure.dependency ss₀))
                 → ⌞ (dep₀ ⟨ x ⟩) ⌟
                 → ContextMorphism
                     (extendedContext (SequentStructure.sequent ss₀ ⟨ x ⟩)) (f h₀))
        (coh₀ : CoherenceOf ss₀ dep₀ h₀ real₀)
        (h₁ : A) (hh : A≈ h₀ h₁)
        {ss₁ : SequentStructure 𝒥 so sa i}
        (ssw : SequentStructureEquality ss₀ ss₁)
      → Contractible (SequentStructureFibre ss₀ ss₁ ssw dep₀ h₀ h₁ hh real₀)
    fibre-Contractible ss₀ dep₀ h₀ real₀ coh₀ h₁ hh ssw =
      ≈-induction
        (λ ss₁' ssw' →
           Contractible (SequentStructureFibre ss₀ ss₁' ssw' dep₀ h₀ h₁ hh real₀))
        (baseFibre-Contractible ss₀ dep₀ h₀ real₀ coh₀ h₁ hh)
        ssw

  private
    Parts : (c₀ : SequentDependencyStructure 𝒥 so sa i A f) → Type (o ⊔ a ⊔ lsuc so ⊔ lsuc sa ⊔ lsuc i ⊔ t ⊔ l)
    Parts c₀ =
      ∑[ hp ∶ (∑[ h₁ ∶ A ] A≈ (head c₀) h₁) ]
        ∑[ sp ∶ (∑[ ss₁ ∶ SequentStructure 𝒥 so sa i ]
                   SequentStructureEquality (sequentStructure c₀) ss₁) ]
          SequentStructureFibre (sequentStructure c₀) (p₀ sp) (p₁ sp) (dependency c₀)
                                (head c₀) (p₀ hp) (p₁ hp) (realiseDependency c₀)

    toParts : (c₀ : SequentDependencyStructure 𝒥 so sa i A f)
             → (∑[ c₁ ∶ SequentDependencyStructure 𝒥 so sa i A f ]
                  SequentDependencyStructureEquality A≈ headContext≈ c₀ c₁)
             → Parts c₀
    toParts c₀ (mkSequentDependencyStructure h₁ ss₁ dep₁ real₁ coh₁
                 , mkSequentDependencyStructureEquality hh ssw te tn rw) =
      (h₁ , hh) , ((ss₁ , ssw) , ((dep₁ , te , tn) , ((real₁ , rw) , (λ d₀ d₁ u g → coh₁ u g))))

    fromParts : (c₀ : SequentDependencyStructure 𝒥 so sa i A f)
               → Parts c₀
               → ∑[ c₁ ∶ SequentDependencyStructure 𝒥 so sa i A f ]
                   SequentDependencyStructureEquality A≈ headContext≈ c₀ c₁
    fromParts c₀ ((h₁ , hh) , ((ss₁ , ssw) , ((dep₁ , te , tn) , ((real₁ , rw) , coh₁)))) =
      mkSequentDependencyStructure h₁ ss₁ dep₁ real₁ (λ {d₀} {d₁} u g → coh₁ d₀ d₁ u g)
      , mkSequentDependencyStructureEquality hh ssw te tn rw

    roundTrip : (c₀ : SequentDependencyStructure 𝒥 so sa i A f)
              → fromParts c₀ ∘ toParts c₀ ~ id
    roundTrip c₀ (mkSequentDependencyStructure h₁ ss₁ dep₁ real₁ coh₁
                  , mkSequentDependencyStructureEquality hh ssw te tn rw) = refl

  sequentDependencyStructureTotalSpace-Contractible :
      (c₀ : SequentDependencyStructure 𝒥 so sa i A f)
    → Contractible (∑[ c₁ ∶ SequentDependencyStructure 𝒥 so sa i A f ]
                      SequentDependencyStructureEquality A≈ headContext≈ c₀ c₁)
  sequentDependencyStructureTotalSpace-Contractible c₀ =
    retract-Contractible (toParts c₀) (fromParts c₀) (roundTrip c₀)
      (∑-Contractible (A-total (head c₀))
        (λ hp → ∑-Contractible
                  (sequentStructureTotalSpace-Contractible (sequentStructure c₀))
                  (λ sp → fibre-Contractible
                            (sequentStructure c₀) (dependency c₀) (head c₀)
                            (realiseDependency c₀)
                            (λ d₀ d₁ u g → coherenceRealisation c₀ u g)
                            (p₀ hp) (p₁ hp) (p₁ sp))))

instance
  equalitySequentDependencyStructure :
      ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
    → {o a t l so sa i : Level} {𝒥 : DependentSortVocabulary o a}
      {A : Type t} {f : A → Context 𝒥 i}
      {A≈ : A → A → Type l}
      {A-refl≈ : (x : A) → A≈ x x}
      {A-total : (x : A) → Contractible (∑[ y ∶ A ] A≈ x y)}
      {headContext≈ : {x y : A} → A≈ x y → ContextEquivalence (f x) (f y)}
      {headContext≈-refl : (x : A) (j : type (Judgment 𝒥)) (z : ⌞ (f x) ⟨ j ⟩ ⌟)
                         → (ContextEquivalence.morphism
                              (headContext≈ (A-refl≈ x)) ⟨ j ⟩) z ＝ z}
    → Equality 𝟙₀ (λ _ → SequentDependencyStructure 𝒥 so sa i A f)
  equalitySequentDependencyStructure
    {A≈ = A≈} {A-refl≈ = r} {A-total = t} {headContext≈ = h} {headContext≈-refl = hr} =
    record { samey = record { samey = SDSE }
           ; characterisation =
               fundamentalTheorem SDSE
                 (identitySequentDependencyStructureEquality A≈ r t h hr)
                 (sequentDependencyStructureTotalSpace-Contractible A≈ r t h hr) }
    where
      SDSE = SequentDependencyStructureEquality A≈ h

