import RelationalRamsey632.Existence.FiniteTypes
import RelationalRamsey632.Existence.Obstructions
import Mathlib.SetTheory.Cardinal.Finite

/-! Exact singleton type counts, with nullary assignment fixed. -/

namespace RelationalRamsey632.Existence

variable (L : Language)

def FixedNullary {X : Type} (θ : L.Rel 0 → Prop) (A : RelStructure L X) : Prop :=
  ∀ (R : L.Rel 0) (t : Fin 0 → X), A.rel R t ↔ θ R

abbrev OrdinarySingletonType (θ : L.Rel 0 → Prop) :=
  {A : RelStructure L Unit // FixedNullary L θ A}

def ordinarySingletonType (θ : L.Rel 0 → Prop) (b : L.PositiveSymbol → Prop) :
    OrdinarySingletonType L θ :=
  ⟨ordinarySingleton L θ b, ordinarySingleton_nullary L θ b⟩

def ordinarySingletonProfile (θ : L.Rel 0 → Prop) (A : OrdinarySingletonType L θ) :
    L.PositiveSymbol → Prop := fun s => A.val.rel s.2 (fun _ => ())

def ordinarySingletonEquiv (θ : L.Rel 0 → Prop) :
    OrdinarySingletonType L θ ≃ (L.PositiveSymbol → Prop) where
  toFun := ordinarySingletonProfile L θ
  invFun := ordinarySingletonType L θ
  left_inv A := by
    apply Subtype.ext
    apply RelStructure.ext_rel
    intro r R t
    by_cases hr : r = 0
    · subst r
      exact (ordinarySingleton_nullary L θ _ R t).trans (A.property R t).symm
    · have ht : t = (fun _ => ()) := funext (fun _ => Subsingleton.elim _ _)
      simp [ordinarySingletonType, ordinarySingleton, ordinarySingletonProfile, hr, ht]
  right_inv b := by
    funext s
    apply propext
    exact ordinarySingleton_positive L θ b s (fun _ => ())

theorem ordinary_singleton_cardinal (θ : L.Rel 0 → Prop) :
    Cardinal.mk (OrdinarySingletonType L θ) = 2 ^ Cardinal.mk L.PositiveSymbol := by
  rw [Cardinal.mk_congr (ordinarySingletonEquiv L θ), Cardinal.mk_arrow]
  simp

theorem singleton_embedding_iff_eq (A B : RelStructure L Unit) :
    Nonempty (RelEmbedding A B) ↔ A = B := by
  constructor
  · rintro ⟨e⟩
    apply RelStructure.ext_rel
    intro r R t
    have ht : e ∘ t = t := funext (fun _ => Subsingleton.elim _ _)
    exact ht ▸ e.map_rel R t
  · rintro rfl
    exact ⟨RelEmbedding.refl A⟩

def injectiveSingleton (θ : L.Rel 0 → Prop) (b : L.Rel 1 → Prop) :
    RelStructure L Unit where
  rel {r} R _ := if hr : r = 0 then θ (hr ▸ R)
    else if hr1 : r = 1 then b (hr1 ▸ R) else False

@[simp] theorem injectiveSingleton_nullary (θ : L.Rel 0 → Prop) (b : L.Rel 1 → Prop)
    (R : L.Rel 0) (t : Fin 0 → Unit) :
    (injectiveSingleton L θ b).rel R t ↔ θ R := by
  simp [injectiveSingleton]

@[simp] theorem injectiveSingleton_unary (θ : L.Rel 0 → Prop) (b : L.Rel 1 → Prop)
    (R : L.Rel 1) (t : Fin 1 → Unit) :
    (injectiveSingleton L θ b).rel R t ↔ b R := by
  simp [injectiveSingleton]

theorem injectiveSingleton_injective (θ : L.Rel 0 → Prop) (b : L.Rel 1 → Prop) :
    (injectiveSingleton L θ b).InjectiveRelations := by
  intro r R t hr ht
  by_cases hr1 : r = 1
  · subst r
    exact fun _ _ _ => Subsingleton.elim _ _
  · simp [injectiveSingleton, Nat.ne_of_gt hr, hr1] at ht

abbrev InjectiveSingletonType (θ : L.Rel 0 → Prop) :=
  {A : RelStructure L Unit // A.InjectiveRelations ∧ FixedNullary L θ A}

def injectiveSingletonType (θ : L.Rel 0 → Prop) (b : L.Rel 1 → Prop) :
    InjectiveSingletonType L θ :=
  ⟨injectiveSingleton L θ b,
    injectiveSingleton_injective L θ b, injectiveSingleton_nullary L θ b⟩

def injectiveSingletonProfile (θ : L.Rel 0 → Prop) (A : InjectiveSingletonType L θ) :
    L.Rel 1 → Prop := fun R => A.val.rel R (fun _ => ())

def injectiveSingletonEquiv (θ : L.Rel 0 → Prop) :
    InjectiveSingletonType L θ ≃ (L.Rel 1 → Prop) where
  toFun := injectiveSingletonProfile L θ
  invFun := injectiveSingletonType L θ
  left_inv A := by
    apply Subtype.ext
    apply RelStructure.ext_rel
    intro r R t
    by_cases hr : r = 0
    · subst r
      exact (injectiveSingleton_nullary L θ _ R t).trans (A.property.2 R t).symm
    · by_cases hr1 : r = 1
      · subst r
        have ht : t = (fun _ => ()) := funext (fun _ => Subsingleton.elim _ _)
        simp [injectiveSingletonType, injectiveSingleton, injectiveSingletonProfile, ht]
      · have hbig : 1 < r := by omega
        have hfalse : ¬ A.val.rel R t := by
          intro ht
          have hle := A.val.injectiveTuple_arity_le A.property.1 R t
            (Nat.pos_of_ne_zero hr) ht
          simp only [Fintype.card_unit] at hle
          omega
        simp [injectiveSingletonType, injectiveSingleton, hr, hr1, hfalse]
  right_inv b := by
    funext R
    apply propext
    exact injectiveSingleton_unary L θ b R (fun _ => ())

theorem injective_singleton_cardinal (θ : L.Rel 0 → Prop) :
    Cardinal.mk (InjectiveSingletonType L θ) = 2 ^ Cardinal.mk (L.Rel 1) := by
  rw [Cardinal.mk_congr (injectiveSingletonEquiv L θ), Cardinal.mk_arrow]
  simp

end RelationalRamsey632.Existence
