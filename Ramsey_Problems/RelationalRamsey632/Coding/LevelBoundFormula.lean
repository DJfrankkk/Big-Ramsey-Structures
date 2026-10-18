import RelationalRamsey632.Coding.SeparatedClosure
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring

namespace RelationalRamsey632.Coding

theorem levelBound_rational (m : ℕ) :
    (levelBound m : ℚ) = (m : ℚ) +
      (∑ i : Fin m, ((m : ℚ) ^ (2 * (i.val + 1)) + (m : ℚ) ^ (i.val + 1))) / 2 := by
  simp only [levelBound, Nat.cast_add, Nat.cast_sum, Nat.cast_choose_two,
    Nat.cast_pow, Nat.cast_one, add_sub_cancel_right]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.mul_comm 2 (i.val + 1), pow_mul]
  ring

end RelationalRamsey632.Coding
