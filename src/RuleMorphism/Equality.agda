module RuleMorphism.Equality where

open import Prelude
open import Axioms
open import Homotopy.SetQuotient
open import Algebra.Wild.Semi
open import Syntax.Arrowable
open import Homotopy.Equality
open import Homotopy.Levels
open import Homotopy.StructuredType
open import Homotopy.Fibre
open import Foundation.DependentPair.Equivalence
open import Foundation.Identity.Equivalence
open import Structure.Composable
open import Structure.Identity
open import Structure.Symmetric
open import Structure.Associativity
open Semicategory.Semicategory

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
open import Weakening.SequentStructure
open import SequentStructureMorphism
open import SequentStructureMorphism.Equality
open import Rule
open SequentDependencyStructure.SequentDependencyStructure
open ContextWithTerms.ContextWithTerms
open import RuleMorphism
open RuleMorphism.RuleMorphism


-- =============== Equality of rule morphisms from base equivalences ===============

module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a} where

  idSequentStructureEquality : (s : SequentStructure 𝒥 so sa i)
                             → SequentStructureEquality s s
  idSequentStructureEquality s =
    record
      { dependency≈ = record
          { objects≈ = ≃-id
          ; hom≈ = λ A B → ≃-id
          ; composition≈ = λ A B E f g → refl
          ; associative≈ = λ A B E F f g h →
              allEqual ⦃ ＝-isLevel ⦃ SequentStructure.dependency-Hom-isSet s A F ⦄ ⦄ _ _ }
      ; sequent≈ = λ x → sequentEquivalence-identity
      ; natural≈ = λ {x} {y} f → idSquareSMEᴿ (SequentStructure.sequent s ⟨ f ⟩) }
    where
      idSeqMorᵇ : {l : Level} {t : Sequent 𝒥 l}
                → SequentMorphism.sequentMorphism (toSequentMorphism (sequentEquivalence-identity {s = t}))
                  ＝ identity
      idSeqMorᵇ {t = t} = eq (toSequentMorphism-identity {s = t})

      unitLᵇ : {l₀ l₁ : Level} {Γ : Context 𝒥 l₀} {Δ : Context 𝒥 l₁} (β : Γ ⇒ Δ)
             → identity ∙ β ＝ β
      unitLᵇ β = eq (record { component≈ = λ j → refl })

      unitRᵇ : {l₀ l₁ : Level} {Γ : Context 𝒥 l₀} {Δ : Context 𝒥 l₁} (β : Γ ⇒ Δ)
             → β ∙ identity ＝ β
      unitRᵇ β = eq (record { component≈ = λ j → refl })

      idSquareSMEᴿ : {l₀ l₁ : Level} {s₀ : Sequent 𝒥 l₀} {s₁ : Sequent 𝒥 l₁}
                     (α : SequentMorphism s₀ s₁)
                   → SequentMorphismEquality
                       (toSequentMorphism (sequentEquivalence-identity {s = s₁}) ∙ α)
                       (α ∙ toSequentMorphism (sequentEquivalence-identity {s = s₀}))
      idSquareSMEᴿ {s₀ = s₀} {s₁ = s₁} α =
        observe ⦃ equalitySequentMorphism ⦄
          (   ap (λ m → mkSequentMorphism (m ∙ SequentMorphism.sequentMorphism α)) (idSeqMorᵇ {t = s₁})
           ⨾  ap mkSequentMorphism (unitLᵇ (SequentMorphism.sequentMorphism α))
           ⨾  sym (ap mkSequentMorphism (unitRᵇ (SequentMorphism.sequentMorphism α)))
           ⨾  sym (ap (λ m → mkSequentMorphism (SequentMorphism.sequentMorphism α ∙ m)) (idSeqMorᵇ {t = s₀})))

  idContextWithTermsEquality : (b : ContextWithTerms 𝒥 so sa i)
                             → ContextWithTermsEquality b b
  idContextWithTermsEquality b =
    record
      { contextWithTerms≈ = record
          { head≈ = identity
          ; sequentStructure≈ = idSequentStructureEquality (SequentDependencyStructure.sequentStructure bd)
          ; terms≈ = λ x → ≃-id
          ; termsNatural = λ g → refl
          ; realise≈ = λ x u →
              record { component≈ = λ j → funExt (λ z →
                  sym (ap (λ h → (SequentDependencyStructure.realiseDependency bd x u ⟨ j ⟩) (h z))
                          (ContextMorphismEquality.component≈
                             (toSequentMorphism-identity
                                {s = SequentStructure.sequent (SequentDependencyStructure.sequentStructure bd) ⟨ x ⟩}) j))) } } }
    where
      bd = ContextWithTerms.contextWithTerms b

-- =============== Equality of rule morphisms ===============

castSSM : ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
        → {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a}
          {r : Rule 𝒥 so sa i} {b₀ b₁ : ContextWithTerms 𝒥 so sa i}
        → ContextWithTermsEquality b₀ b₁
        → SequentStructureMorphism (b₀ ⧺ ⋊ₛ r) (b₁ ⧺ ⋊ₛ r)
castSSM {r = r} w = equivToSSM (⧺-congruenceˡ (⋊ₛ r) w)

record RuleMorphismEquality
  ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a}
  {r₀ r₁ : Rule 𝒥 so sa i}
  (φ₀ φ₁ : RuleMorphism r₀ r₁)
  : Type (o ⊔ a ⊔ so ⊔ sa ⊔ lsuc i) where
  constructor mkRuleMorphismEquality
  field
    baseContext≈ : ContextWithTermsEquality (baseContext φ₀) (baseContext φ₁)
    ruleMorphism≈ :
      SequentStructureMorphismEquality
        (ruleMorphism φ₀)
        (sequentStructureMorphism-⨾
          {s₀ = baseContext φ₀ ⧺ ⋊ₛ r₀}
          {s₁ = baseContext φ₁ ⧺ ⋊ₛ r₀}
          {s₂ = premises r₁}
          (castSSM {r = r₀} {b₀ = baseContext φ₀} {b₁ = baseContext φ₁}
                   baseContext≈)
          (ruleMorphism φ₁))

module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a}
  {r₀ r₁ : Rule 𝒥 so sa i} where

  private
    T₁ = SequentDependencyStructure.sequentStructure (Rule.rule r₁)

  castIdUnit : {b : ContextWithTerms 𝒥 so sa i}
               (m : SequentStructureMorphism (b ⧺ ⋊ₛ r₀) T₁)
             → SequentStructureMorphismEquality m
                 (sequentStructureMorphism-⨾
                   {s₀ = b ⧺ ⋊ₛ r₀} {s₁ = b ⧺ ⋊ₛ r₀} {s₂ = T₁}
                   (castSSM {r = r₀} {b₀ = b} {b₁ = b}
                            (idContextWithTermsEquality b)) m)
  castIdUnit {b = b} m =
    record
      { dependencyMorphism≈ = record
          { onObjects≈ = λ { (inl w') → refl ; (inr y) → refl }
          ; witness≈ =
              (λ { (inl u) (inl v) f → refl
                 ; (inr x) (inr y) f → refl
                 ; (inr x) (inl u) f → refl
                 ; (inl u) (inr y) () })
            , (λ A B E g h →
                 allEqual ⦃ ＝-isLevel ⦃ SequentStructure.dependency-Hom-isSet T₁ _ _ ⦄ ⦄ _ _) }
      ; sequentEquivalence≈ = seq≈' }
    where
      seq≈' : (x : Ob (SequentStructure.dependency (b ⧺ ⋊ₛ r₀))) → _
      seq≈' (inl w') =
        record { contextEquivalence≈ = record { morphism≈ = record { component≈ = λ j → refl } } }
      seq≈' (inr y) =
        record { contextEquivalence≈ = record { morphism≈ = record { component≈ = λ j → funExt (pt j) } } }
        where
          pt : (j : type (Judgment 𝒥))
               (z : ⌞ Sequent.context (SequentStructure.sequent (b ⧺ ⋊ₛ r₀) ⟨ inr y ⟩) ⟨ j ⟩ ⌟)
             → (ContextEquivalence.morphism
                  (SequentEquivalence.contextEquivalence
                     (SequentStructureMorphism.sequentEquivalence m (inr y))) ⟨ j ⟩) z
               ＝ (ContextEquivalence.morphism
                    (SequentEquivalence.contextEquivalence
                       (SequentStructureMorphism.sequentEquivalence
                          (sequentStructureMorphism-⨾
                            {s₀ = b ⧺ ⋊ₛ r₀} {s₁ = b ⧺ ⋊ₛ r₀} {s₂ = T₁}
                            (castSSM {r = r₀} {b₀ = b} {b₁ = b}
                                     (idContextWithTermsEquality b)) m)
                          (inr y))) ⟨ j ⟩) z
          pt j (inl h) = refl
          pt j (inr v) = refl

  identityRuleMorphismEquality :
      (φ : RuleMorphism r₀ r₁) → RuleMorphismEquality φ φ
  identityRuleMorphismEquality φ =
    record
      { baseContext≈ = idContextWithTermsEquality (baseContext φ)
      ; ruleMorphism≈ = castIdUnit {b = baseContext φ} (ruleMorphism φ) }

  instance
    sameyRuleMorphism : Samey 𝟙₀ (λ _ → RuleMorphism r₀ r₁)
    sameyRuleMorphism = record { samey = RuleMorphismEquality }

  ruleMorphismTotalSpace-Contractible :
      (φ₀ : RuleMorphism r₀ r₁)
    → Contractible (∑[ φ₁ ∶ RuleMorphism r₀ r₁ ] RuleMorphismEquality φ₀ φ₁)
  ruleMorphismTotalSpace-Contractible (mkRuleMorphism b₀ m₀) =
    retract-Contractible toParts fromParts roundTrip
      (∑-Contractible-over
        (inhabited-proposition→contractible
           ⦃ contractible→level ⦃ contractible-type
               (equality-Contractible ⦃ w = equalityContextWithTerms ⦄ b₀) ⦄ ⦄
           (b₀ , idContextWithTermsEquality b₀))
        fibreC)
    where
      F : SequentStructureMorphism (b₀ ⧺ ⋊ₛ r₀) T₁
        → SequentStructureMorphism (b₀ ⧺ ⋊ₛ r₀) T₁
      F m₁ = sequentStructureMorphism-⨾
               {s₀ = b₀ ⧺ ⋊ₛ r₀} {s₁ = b₀ ⧺ ⋊ₛ r₀} {s₂ = T₁}
               (castSSM {r = r₀} {b₀ = b₀} {b₁ = b₀}
                        (idContextWithTermsEquality b₀)) m₁

      F-isEquivalence : isEquivalence F
      F-isEquivalence =
        ~transfer-isEquivalence ≃-id
          (λ m₁ → eq ⦃ equalitySequentStructureMorphism ⦄ (castIdUnit {b = b₀} m₁))

      fibreC : Contractible
                 (∑[ m₁ ∶ SequentStructureMorphism (b₀ ⧺ ⋊ₛ r₀) T₁ ]
                   SequentStructureMorphismEquality m₀ (F m₁))
      fibreC =
        ≃-Contractible (equiv-tot (λ m₁ → observe-≃ ⦃ equalitySequentStructureMorphism ⦄))
          (≃-Contractible (equiv-tot (λ m₁ → sym-≃))
            (≃-Contractible fibre≃∑
              (equivalenceFibresAreContractible (isEquivalence→≃ F-isEquivalence) m₀)))

      Parts : Type (o ⊔ a ⊔ lsuc so ⊔ lsuc sa ⊔ lsuc i)
      Parts = ∑[ w ∶ (∑[ b₁ ∶ ContextWithTerms 𝒥 so sa i ]
                        ContextWithTermsEquality b₀ b₁) ]
                ∑[ m₁ ∶ SequentStructureMorphism ((p₀ w) ⧺ ⋊ₛ r₀) T₁ ]
                  SequentStructureMorphismEquality m₀
                    (sequentStructureMorphism-⨾
                      {s₀ = b₀ ⧺ ⋊ₛ r₀} {s₁ = (p₀ w) ⧺ ⋊ₛ r₀} {s₂ = T₁}
                      (castSSM {r = r₀} {b₀ = b₀} {b₁ = p₀ w} (p₁ w)) m₁)

      toParts : (∑[ φ₁ ∶ RuleMorphism r₀ r₁ ]
                   RuleMorphismEquality (mkRuleMorphism b₀ m₀) φ₁)
              → Parts
      toParts (mkRuleMorphism b₁ m₁ , mkRuleMorphismEquality w S) =
        (b₁ , w) , (m₁ , S)

      fromParts : Parts
                → ∑[ φ₁ ∶ RuleMorphism r₀ r₁ ]
                    RuleMorphismEquality (mkRuleMorphism b₀ m₀) φ₁
      fromParts ((b₁ , w) , (m₁ , S)) =
        mkRuleMorphism b₁ m₁ , mkRuleMorphismEquality w S

      roundTrip : fromParts ∘ toParts ~ id
      roundTrip (mkRuleMorphism b₁ m₁ , mkRuleMorphismEquality w S) = refl

  instance
    equalityRuleMorphism : Equality 𝟙₀ (λ _ → RuleMorphism r₀ r₁)
    equalityRuleMorphism =
      record { characterisation =
                 fundamentalTheorem RuleMorphismEquality
                                    identityRuleMorphismEquality
                                    ruleMorphismTotalSpace-Contractible }


