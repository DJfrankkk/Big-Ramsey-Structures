import RelationalRamsey632.Model
import RelationalRamsey632.CodingBounds
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! Full relation profiles include every symbol and every orientation of
an injective support. Codes have a distinguished all-false zero value. -/

namespace RelationalRamsey632.Coding

variable (L : Language) [∀ r, Fintype (L.Rel r)]

abbrev UnaryProfile := L.Rel 1 → Bool

noncomputable instance unaryProfileFintype : Fintype (UnaryProfile L) := by
  classical
  unfold UnaryProfile
  infer_instance

theorem unaryProfile_card : Nat.card (UnaryProfile L) = 2 ^ Fintype.card (L.Rel 1) := by
  classical
  let E : UnaryProfile L ≃ (L.Rel 1 × Unit → Bool) := {
    toFun := fun f p => f p.1
    invFun := fun f R => f (R, ())
    left_inv := fun _ => rfl
    right_inv := by
      intro f
      funext p
      cases p with
      | mk R u => cases u; rfl }
  rw [Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_prod, Fintype.card_unit, Nat.mul_one]

abbrev Profile (r : ℕ) := L.Rel (r + 1) → Equiv.Perm (Fin (r + 1)) → Bool

noncomputable instance profileFintype (r : ℕ) : Fintype (Profile L r) := by
  classical
  unfold Profile
  infer_instance

def falseProfile (r : ℕ) : Profile L r := fun _ _ => false

noncomputable def profileSize (r : ℕ) : ℕ := Fintype.card (Profile L r)

theorem profileSize_formula (r : ℕ) :
    profileSize L r = 2 ^ (Fintype.card (L.Rel (r + 1)) * (r + 1).factorial) := by
  classical
  unfold profileSize
  rw [Fintype.card_congr ((Equiv.curry (L.Rel (r + 1))
    (Equiv.Perm (Fin (r + 1))) Bool).symm)]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_prod,
    Fintype.card_perm, Fintype.card_fin]

theorem profileSize_positive (r : ℕ) : 0 < profileSize L r := by
  rw [profileSize_formula]
  exact pow_pos (by omega) _

noncomputable def profileCode (r : ℕ) : Profile L r ≃ Fin (profileSize L r) :=
  let e := Fintype.equivFin (Profile L r)
  e.trans (Equiv.swap (e (falseProfile L r)) ⟨0, profileSize_positive L r⟩)

@[simp] theorem profileCode_false (r : ℕ) :
    profileCode L r (falseProfile L r) = ⟨0, profileSize_positive L r⟩ := by
  exact Equiv.swap_apply_left _ _

@[simp] theorem decode_zero (r : ℕ) :
    (profileCode L r).symm ⟨0, profileSize_positive L r⟩ = falseProfile L r := by
  rw [← profileCode_false]
  exact (profileCode L r).symm_apply_apply _

noncomputable def unaryAt {X : Type} (K : RelStructure L X) (x : X) : UnaryProfile L := by
  classical
  exact fun R => decide (K.rel R (fun _ => x))

noncomputable def profileAt {X : Type} (K : RelStructure L X) (r : ℕ)
    (t : Fin (r + 1) → X) : Profile L r := by
  classical
  exact fun R σ => decide (K.rel R (t ∘ σ))

omit [∀ r, Fintype (L.Rel r)] in
@[simp] theorem unaryAt_true {X : Type} (K : RelStructure L X) (x : X) (R : L.Rel 1) :
    unaryAt L K x R = true ↔ K.rel R (fun _ => x) := by
  simp [unaryAt]

omit [∀ r, Fintype (L.Rel r)] in
@[simp] theorem profileAt_true {X : Type} (K : RelStructure L X) (r : ℕ)
    (t : Fin (r + 1) → X) (R : L.Rel (r + 1)) (σ : Equiv.Perm (Fin (r + 1))) :
    profileAt L K r t R σ = true ↔ K.rel R (t ∘ σ) := by
  simp [profileAt]

noncomputable def decodeProfile (r : ℕ)
    (a : Fin (CodingBounds.alphabetSize (profileSize L) r)) : Profile L r :=
  if h : a.val < profileSize L r then (profileCode L r).symm ⟨a.val, h⟩
  else falseProfile L r

def embedCode (r : ℕ) (hr : 0 < r) (a : Fin (profileSize L r)) :
    Fin (CodingBounds.alphabetSize (profileSize L) r) :=
  ⟨a.val, a.isLt.trans_le (CodingBounds.profile_le_alphabet (profileSize L) (by omega) (by omega))⟩

@[simp] theorem decodeProfile_embedCode (r : ℕ) (hr : 0 < r) (p : Profile L r) :
    decodeProfile L r (embedCode L r hr (profileCode L r p)) = p := by
  simp only [decodeProfile, embedCode, dif_pos (profileCode L r p).isLt]
  exact (profileCode L r).symm_apply_apply p

@[simp] theorem decodeProfile_outside (r : ℕ)
    (a : Fin (CodingBounds.alphabetSize (profileSize L) r))
    (h : profileSize L r ≤ a.val) : decodeProfile L r a = falseProfile L r := by
  simp only [decodeProfile, dif_neg (Nat.not_lt.mpr h)]

end RelationalRamsey632.Coding
