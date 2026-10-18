import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Log
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

/-! The exact finite alphabet capacity in the uniform digit construction.
The profile alphabet sequence can be unbounded; no global finite-language
or bounded-arity assumption is introduced. -/

namespace RelationalRamsey632.CodingBounds

def alphabetSize (b : Nat → Nat) (j : Nat) : Nat :=
  max 2 ((Finset.Icc 1 (2 * j)).sup b)

def blockLength (b : Nat → Nat) (n : Nat) : Nat :=
  (Finset.Icc 1 (2 * n + 2)).sup b

theorem alphabet_at_least_two (b : Nat → Nat) (j : Nat) : 2 ≤ alphabetSize b j :=
  le_max_left _ _

theorem profile_le_alphabet (b : Nat → Nat) {r j : Nat} (hr : 1 ≤ r) (hrj : r ≤ 2 * j) :
    b r ≤ alphabetSize b j :=
  (Finset.le_sup (f := b) (Finset.mem_Icc.mpr ⟨hr, hrj⟩)).trans (le_max_right _ _)

theorem profile_le_blockLength (b : Nat → Nat) {r n : Nat} (hr : 1 ≤ r) (hrn : r ≤ 2 * n + 2) :
    b r ≤ blockLength b n := Finset.le_sup (f := b) (Finset.mem_Icc.mpr ⟨hr, hrn⟩)

theorem blockLength_positive (b : Nat → Nat) (hb : ∀ r, 1 ≤ r → 0 < b r) (n : Nat) :
    0 < blockLength b n :=
  lt_of_lt_of_le (hb 1 le_rfl) (profile_le_blockLength b le_rfl (by omega))

theorem self_le_two_pow (k : Nat) : k ≤ 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    have hpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
    omega

/-- Inequality (1) in the digit-coding proof. Its uniformity in the slice
sort `i` is what permits the single coding to handle every arity. -/
theorem digit_capacity (b : Nat → Nat) (hb : ∀ r, 1 ≤ r → 0 < b r)
    (i n t : Nat) (ht : 1 ≤ t) (htn : t ≤ n + 1) :
    b (i + t) ≤ alphabetSize b (i + 1) ^ blockLength b n := by
  have hbase := alphabet_at_least_two b (i + 1)
  have hblock := blockLength_positive b hb n
  by_cases hlarge : n + 1 ≤ i + 1
  · have hbA : b (i + t) ≤ alphabetSize b (i + 1) :=
      profile_le_alphabet b (by omega) (by omega)
    apply hbA.trans
    exact Nat.le_self_pow (by omega) _
  · have hbK : b (i + t) ≤ blockLength b n :=
      profile_le_blockLength b (by omega) (by omega)
    exact hbK.trans ((self_le_two_pow _).trans (Nat.pow_le_pow_left hbase _))

end RelationalRamsey632.CodingBounds
