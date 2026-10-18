import RelationalRamsey632.CodingBounds
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Algebra.BigOperators.Fin

namespace RelationalRamsey632.Digits

def digit (base position value : Nat) : Nat := value / base ^ position % base

def vector (base length value : Nat) : Fin length → Nat :=
  fun position => digit base position.val value

def decode (base : Nat) : (length : Nat) → (Fin length → Nat) → Nat
  | 0, _ => 0
  | length + 1, v => v 0 + base * decode base length (fun i => v i.succ)

theorem digit_lt (base position value : Nat) (hb : 0 < base) : digit base position value < base :=
  Nat.mod_lt _ hb

theorem digit_zero (base position : Nat) : digit base position 0 = 0 := by simp [digit]

theorem digit_shift (base value position : Nat) :
    digit base position (value / base) = digit base (position + 1) value := by
  unfold digit
  rw [Nat.div_div_eq_div_mul, pow_succ']

theorem decode_vector (base length value : Nat) (hb : 0 < base) (hv : value < base ^ length) :
    decode base length (vector base length value) = value := by
  induction length generalizing value with
  | zero =>
    have hzero : value = 0 := by simp only [pow_zero] at hv; omega
    subst value
    rfl
  | succ length ih =>
    have hdiv : value / base < base ^ length := by
      apply (Nat.div_lt_iff_lt_mul hb).mpr
      simpa only [pow_succ] using hv
    have htail : (fun i : Fin length => vector base (length + 1) value i.succ) =
        vector base length (value / base) := by
      funext i
      exact (digit_shift base value i.val).symm
    change digit base 0 value + base * decode base length
      (fun i => vector base (length + 1) value i.succ) = value
    rw [htail, ih (value / base) hdiv]
    simp only [digit, pow_zero, Nat.div_one]
    exact Nat.mod_add_div value base

/-- The exact finite digit block distinguishes every permitted profile.
This is proved for arbitrary bases and lengths, not just binary examples. -/
theorem vector_injective (base length : Nat) (hb : 0 < base) :
    Set.InjOn (vector base length) {s : Nat | s < base ^ length} := by
  intro s hs t ht heq
  have h := congrArg (decode base length) heq
  rw [decode_vector base length s hb hs, decode_vector base length t hb ht] at h
  exact h

theorem different_digit (base length s t : Nat) (hb : 0 < base)
    (hs : s < base ^ length) (ht : t < base ^ length) (hne : s ≠ t) :
    ∃ position < length, digit base position s ≠ digit base position t := by
  by_contra hnot
  have hvec : vector base length s = vector base length t := by
    funext i
    by_contra hi
    exact hnot ⟨i.val, i.isLt, hi⟩
  exact hne (vector_injective base length hb hs ht hvec)

theorem vector_zero (base length : Nat) : vector base length 0 = fun _ => 0 := by
  funext i
  exact digit_zero base i.val

theorem decode_eq_sum (base length : Nat) (v : Fin length → Nat) :
    decode base length v = ∑ i : Fin length, v i * base ^ i.val := by
  induction length with
  | zero => simp [decode]
  | succ length ih =>
    calc
      decode base (length + 1) v = v 0 + base *
          (∑ i : Fin length, v i.succ * base ^ i.val) := by rw [decode, ih]
      _ = v 0 + ∑ i : Fin length, v i.succ * base ^ (i.val + 1) := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [pow_succ']
        exact Nat.mul_left_comm base (v i.succ) (base ^ i.val)
      _ = ∑ i : Fin (length + 1), v i * base ^ i.val := by
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, pow_zero, Nat.mul_one, Fin.val_succ]

theorem digit_reconstruction (base length value : Nat) (hb : 0 < base)
    (hv : value < base ^ length) :
    value = ∑ i : Fin length, digit base i.val value * base ^ i.val :=
  (decode_vector base length value hb hv).symm.trans
    (decode_eq_sum base length (vector base length value))

end RelationalRamsey632.Digits
