import RelationalRamsey632.Existence.Obstructions
import Mathlib.Data.Finite.Sum

namespace RelationalRamsey632
namespace Language

def symbolSplit (L : Language) : Sigma L.Rel ≃ (L.Rel 0 ⊕ L.PositiveSymbol) where
  toFun
    | ⟨0, R⟩ => Sum.inl R
    | ⟨n + 1, R⟩ => Sum.inr ⟨⟨n + 1, Nat.zero_lt_succ n⟩, R⟩
  invFun
    | Sum.inl R => ⟨0, R⟩
    | Sum.inr s => ⟨s.1.val, s.2⟩
  left_inv s := by
    rcases s with ⟨n, R⟩
    cases n <;> rfl
  right_inv s := by
    rcases s with R | ⟨⟨n, hn⟩, R⟩
    · rfl
    · cases n with
      | zero => exact False.elim (Nat.lt_irrefl 0 hn)
      | succ n => rfl

theorem finite_symbols_of_finite_positive (L : Language)
    [Finite (L.Rel 0)] [Finite L.PositiveSymbol] : Finite (Sigma L.Rel) :=
  Finite.of_injective (symbolSplit L) (symbolSplit L).injective

theorem countable_positive_symbols (L : Language) (hL : L.FinitePerArity) :
    Countable L.PositiveSymbol := by
  letI : ∀ r : {n : ℕ // 0 < n}, Finite (L.Rel r.val) := fun r => hL r.val
  infer_instance

end Language
end RelationalRamsey632
