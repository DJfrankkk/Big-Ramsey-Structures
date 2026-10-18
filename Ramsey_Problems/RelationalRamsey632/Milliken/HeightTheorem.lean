import RelationalRamsey632.Milliken.HeightPackedStep
import RelationalRamsey632.Milliken.HeightCanonicalFusion
import RelationalRamsey632.Milliken.HeightInduction

/-!
The complete finite-dimensional finite-height vector Milliken theorem.
All HL, frontier canonization, countable fusion, and height induction
premises are supplied by internal proofs.
-/

namespace RelationalRamsey632.Milliken

open Generic3Ramsey.SourceTrees
open Generic3Ramsey.SourceTrees.FiniteLevelTree

theorem milliken_all_heights {I : Type} [Fintype I]
    {α : I → Type} [∀ i, DecidableEq (α i)] {R : ∀ i, α i → α i → Prop}
    (K : Type) [Fintype K] :
    ∀ h : ℕ, ∀ T : ∀ i, FiniteLevelTree (α i) (R i), MillikenHeight T h K := by
  intro h
  induction h with
  | zero => intro T; exact height_zero T K
  | succ h ih =>
    intro T
    by_cases hh : h = 0
    · subst h
      exact height_one T K
    · have hp : 0 < h := Nat.pos_of_ne_zero hh
      apply height_succ_of_factorization T hp ih
      exact heightFactorization_of_canonicalSteps T hp (fun c => canonical_step T c hp)

theorem vector_milliken_height {I : Type} [Fintype I]
    {α : I → Type} [∀ i, DecidableEq (α i)] {R : ∀ i, α i → α i → Prop}
    (T : ∀ i, FiniteLevelTree (α i) (R i)) (h : ℕ) (K : Type) [Fintype K] :
    MillikenHeight T h K := milliken_all_heights K h T

end RelationalRamsey632.Milliken
