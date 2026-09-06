module Example.MLTT.Common where

open import Prelude
open import Axioms
open import Homotopy.SetQuotient
open import Homotopy.StructuredType

open import Context
open import Context.Morphism
open import Context.Extension
open import Context.ExtensionMorphism
open import Sequent
open import Sequent.Morphism

open import Example.MLTT.DependentSortVocabulary as MLTT
open MLTT

⇒from𝒴Ty : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
         → {i : Level} (ctx : Context MLTTDSV i) → 𝒴 Ty ⇒ ctx
⇒from𝒴Ty ctx =
  record
    { component = component
    ; natural = funExt ∘ natural~ }
  where
    component : (j : MLTT.Judgment) → ⌞ 𝒴 {𝒥 = MLTTDSV} Ty ⟨ j ⟩ ⌟ → ⌞ ctx ⟨ j ⟩ ⌟
    component j ()

    natural~ : {j₀ j₁ : MLTT.Judgment} (f : MLTT.Dependency j₀ j₁)
            → ctx ⟨ f ⟩ ∘ component j₀ ~ component j₁ ∘ 𝒴 {𝒥 = MLTTDSV} Ty ⟨ f ⟩
    natural~ {Ty} {Ty} () x
    natural~ {Ty} {El} () x
    natural~ {El} {Ty} typeOf ()
    natural~ {El} {El} () x


-- ⊢ X Ty

emptyTySequent : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
               → Sequent MLTTDSV lzero
emptyTySequent =
  record
    { context = emptyContext MLTTDSV lzero
    ; extensionOrCollapse = extend
        (record
          { judgmentForm = Ty
          ; arguments = ⇒from𝒴Ty (emptyContext MLTTDSV lzero) }) }

