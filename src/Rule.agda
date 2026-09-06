module Rule where

open import Prelude
open import Axioms
open import Homotopy.SetQuotient
open import Structure.Associativity
open import Structure.Composable
open import Structure.PreservesComposition
open import Structure.Reasoning
open import Structure.Symmetric
open import Homotopy.StructuredType
open import Algebra.Wild.Semi
open Semicategory.Semicategory
open import Algebra.Wild.TruncatedTypeSemicategory
open import Homotopy.Equality
open import Homotopy.Levels

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
open SequentDependencyStructure.SequentDependencyStructure


record Rule
  ⦃ _ : FunExt ⦄
  ⦃ _ : AllSetQuotients ⦄
  {o a : Level}
  (𝒥 : DependentSortVocabulary o a)
  (so sa i : Level)
  : Type (o ⊔ a ⊔ lsuc so ⊔ lsuc sa ⊔ lsuc i) where
  constructor mkRule
  field
    rule : SequentDependencyStructure 𝒥 so sa i (Sequent 𝒥 i) Sequent.context
open Rule

premises : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
         → {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a}
         → Rule 𝒥 so sa i → SequentStructure 𝒥 so sa i
premises = sequentStructure ∘ rule

ruleWithEmptyPremises : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
                      → {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a}
                      → Sequent 𝒥 i → Rule 𝒥 so sa i
ruleWithEmptyPremises {so = so} {sa = sa} {i = i} {𝒥} s =
  record
    { rule = record
      { head = s
      ; sequentStructure = emptySequentStructure 𝒥 so sa i
      ; dependency = emptySemifunctor (hSet-Semicategory sa) so sa
      ; realiseDependency = λ ()
      ; coherenceRealisation = λ { {()} } } }


module ExtendedSequentStructure ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a}
  (e : Rule 𝒥 so sa i) where

  𝒟 = SequentStructure.dependency (premises e)
  ℱ = SequentStructure.sequent (premises e)

  open Semicategory.Reasoning 𝒟
  open Semicategory.Reasoning (𝒟 ᵒᵖ)
  open Semicategory.Reasoning (hSet-Semicategory sa)
  open Semifunctor.Reasoning (SequentDependencyStructure.dependency (rule e))

  data ob : Type so where
    injOb : Ob 𝒟 → ob
    newOb : ob

  hom' : ob → ob → Type sa
  hom' (injOb x) (injOb y) = Hom 𝒟 x y
  hom' (injOb x) newOb = 𝟘
  hom' newOb (injOb x) = ⌞ (dependency (rule e) ⟨ x ⟩) ⌟
  hom' newOb newOb = 𝟘

  data hom (x y : ob) : Type sa where
    include : hom' x y → hom x y

  composition : {A B C : ob} → hom A B → hom B C → hom A C
  composition {injOb x} {injOb y} {injOb z} (include f) (include g) = include (g ∙ f)
  composition {newOb} {injOb y} {injOb z} (include f) (include g) = include ((SequentDependencyStructure.dependency (rule e) ⟨ g ⟩) f)
  composition {injOb x} {newOb} {injOb z} (include ()) g
  composition {newOb} {newOb} {injOb z} (include ()) g
  composition {A} {injOb y} {newOb} f (include ())
  composition {A} {newOb} {newOb} f (include ())

  instance
    composable : Composable 𝟙 (λ _ → ob) hom
    composable = record { composition = composition }

  associativeComposition : {A B C D : ob} {f : hom A B} {g : hom B C} {h : hom C D}
                         → h ∙ (g ∙ f) ＝ (h ∙ g) ∙ f
  associativeComposition {injOb w} {injOb x} {injOb y} {injOb z} {include f} {include g} {include h} = ap include ∙-associative
  associativeComposition {newOb} {injOb x} {injOb y} {injOb z} {include f} {include g} {include h} = ap (λ σ → include (σ f)) (sym (preserves-composition _ _))
  associativeComposition {A} {injOb y} {injOb x} {newOb} {f} {g} {include ()}
  associativeComposition {A} {injOb y} {newOb} {D} {f} {include ()} {h}
  associativeComposition {injOb x} {newOb} {C} {D} {include ()} {g} {h}
  associativeComposition {newOb} {newOb} {C} {D} {include ()} {g} {h}

  instance
    assoc : AssociativeComposition hom (λ _ _ → _＝_)
    assoc = record { ⨾-associative = associativeComposition }

    semicat : Semicategorical 𝟙 (λ _ → ob) hom (λ _ _ → _＝_)
    semicat = record {}

  opaque
    ob-isSet : isSet ob
    ob-isSet =
      retract-level toSum fromSum retraction~
        (+-level (SequentStructure.dependency-Ob-isSet (premises e)) 𝟙-isLevel)
      where
        toSum : ob → Ob 𝒟 + Unit {so}
        toSum (injOb x) = inl x
        toSum newOb = inr ★

        fromSum : Ob 𝒟 + Unit {so} → ob
        fromSum (inl x) = injOb x
        fromSum (inr ★) = newOb

        retraction~ : fromSum ∘ toSum ~ id
        retraction~ (injOb x) = refl
        retraction~ newOb = refl

  opaque
    hom-isSet : (x y : ob) → isSet (hom x y)
    hom-isSet x y = retract-level (unInclude x y) include (λ { (include f) → refl }) (hom'-isSet x y)
      where
        unInclude : (x y : ob) → hom x y → hom' x y
        unInclude x y (include f) = f

        hom'-isSet : (x y : ob) → isSet (hom' x y)
        hom'-isSet (injOb x) (injOb y) = SequentStructure.dependency-Hom-isSet (premises e) x y
        hom'-isSet (injOb x) newOb = 𝟘-isLevel
        hom'-isSet newOb (injOb y) = level-proof (dependency (rule e) ⟨ y ⟩)
        hom'-isSet newOb newOb = 𝟘-isLevel

  sequentDependency : Semicategory so sa
  sequentDependency = asSemicategory (λ _ → ob) hom ★

  obMap : ob → Sequent 𝒥 i
  obMap (injOb x) = ℱ ⟨ x ⟩
  obMap newOb = head (rule e)

  homMap : {x y : ob} → hom y x → SequentMorphism (obMap x) (obMap y)
  homMap {injOb x} {injOb y} (include f) = ℱ ⟨ f ⟩
  homMap {newOb} {injOb y} (include ())
  homMap {injOb x} {newOb} (include f) = mkSequentMorphism (→⋊ (head (rule e)) ∙ realiseDependency (rule e) x f)
  homMap {newOb} {newOb} (include ())

  preserves : {A B C : ob} (f : hom A B) (g : hom B C)
            → homMap (g ∙ f) ＝ homMap f ∙ homMap g
  preserves {injOb x} {injOb y} {injOb z} (include f) (include g) = PreservesComposition.preserves-composition pres _ _
    where
      open Semifunctor.Reasoning ℱ renaming (preservesCompositionₛ to pres)
      open Semicategory.Reasoning (SequentSemicategory 𝒥 i)
  preserves {newOb} {injOb y} {injOb z} (include f) (include g) = ap mkSequentMorphism
    (begin
      →⋊ (head (rule e)) ∙ realiseDependency (rule e) z ((dependency (rule e) ⟨ g ⟩) f)                   ⟪ ap (→⋊ (head (rule e)) ∙_) (coherenceRealisation (rule e) f g) ⟫
      →⋊ (head (rule e)) ∙ (realiseDependency (rule e) y f ∙ SequentMorphism.sequentMorphism (ℱ ⟨ g ⟩))  ⟪ ∙-associative {g = realiseDependency (rule e) y f} ⟫
      (→⋊ (head (rule e)) ∙ realiseDependency (rule e) y f) ∙ SequentMorphism.sequentMorphism (ℱ ⟨ g ⟩)  ∎)
  preserves {A} {injOb x} {newOb} f (include ())
  preserves {injOb x} {newOb} {C} (include ()) g
  preserves {newOb} {newOb} {C} (include ()) g

  sequent : Semifunctor (sequentDependency ᵒᵖ) (SequentSemicategory 𝒥 i)
  sequent =
    record
      { onObjects = obMap
      ; semifunctorial = record
          { mappable = record { map = homMap }
          ; preservesComposition = record { preserves-composition = flip preserves } } }

  extended : SequentStructure 𝒥 so sa i
  extended =
    record
      { dependency = sequentDependency
      ; dependency-Ob-isSet = ob-isSet
      ; dependency-Hom-isSet = hom-isSet
      ; sequent = sequent }

extendSequentStructure : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
                       → {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a}
                       → Rule 𝒥 so sa i
                       → SequentStructure 𝒥 so sa i
extendSequentStructure e = ExtendedSequentStructure.extended e

infix 20 ⋊ₛ_
⋊ₛ_ : ⦃ _ : FunExt ⦄ ⦃ _ : AllSetQuotients ⦄
    → {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a}
    → Rule 𝒥 so sa i
    → SequentStructure 𝒥 so sa i
⋊ₛ_ = extendSequentStructure


-- =============== Equality of rules ===============

record RuleEquality
  ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a}
  (r₀ r₁ : Rule 𝒥 so sa i)
  : Type (o ⊔ a ⊔ so ⊔ sa ⊔ lsuc i) where
  constructor mkRuleEquality
  field
    rule≈ : SequentDependencyStructureEquality
              SequentEquivalence
              SequentEquivalence.contextEquivalence
              (rule r₀)
              (rule r₁)

module _ ⦃ _ : FunExt ⦄ ⦃ _ : Univalence ⦄ ⦃ _ : AllSetQuotients ⦄
  {o a so sa i : Level} {𝒥 : DependentSortVocabulary o a} where

  instance
    sameyRule : Samey 𝟙₀ (λ _ → Rule 𝒥 so sa i)
    sameyRule = record { samey = RuleEquality }

  private
    ruleTotalSpace-Contractible :
        (r₀ : Rule 𝒥 so sa i)
      → Contractible (∑[ r₁ ∶ Rule 𝒥 so sa i ] RuleEquality r₀ r₁)
    ruleTotalSpace-Contractible r₀ =
      retract-Contractible toData fromData roundTrip
        (sequentDependencyStructureTotalSpace-Contractible
           SequentEquivalence (λ _ → sequentEquivalence-identity)
           sequentTotalSpace-Contractible
           SequentEquivalence.contextEquivalence (λ _ _ _ → refl)
           (rule r₀))
      where
        toData : (∑[ r₁ ∶ Rule 𝒥 so sa i ] RuleEquality r₀ r₁)
               → ∑[ c₁ ∶ SequentDependencyStructure 𝒥 so sa i (Sequent 𝒥 i) Sequent.context ]
                   SequentDependencyStructureEquality SequentEquivalence SequentEquivalence.contextEquivalence (rule r₀) c₁
        toData (mkRule c₁ , mkRuleEquality w) = c₁ , w

        fromData : (∑[ c₁ ∶ SequentDependencyStructure 𝒥 so sa i (Sequent 𝒥 i) Sequent.context ]
                      SequentDependencyStructureEquality SequentEquivalence SequentEquivalence.contextEquivalence (rule r₀) c₁)
                 → ∑[ r₁ ∶ Rule 𝒥 so sa i ] RuleEquality r₀ r₁
        fromData (c₁ , w) = mkRule c₁ , mkRuleEquality w

        roundTrip : fromData ∘ toData ~ id
        roundTrip (mkRule c₁ , mkRuleEquality w) = refl

  instance
    equalityRule : Equality 𝟙₀ (λ _ → Rule 𝒥 so sa i)
    equalityRule =
      record { characterisation =
                 fundamentalTheorem RuleEquality
                   (λ r → record { rule≈ =
                            identitySequentDependencyStructureEquality
                              SequentEquivalence (λ _ → sequentEquivalence-identity)
                              sequentTotalSpace-Contractible
                              SequentEquivalence.contextEquivalence (λ _ _ _ → refl)
                              (rule r) })
                   ruleTotalSpace-Contractible }

