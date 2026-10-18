import RelationalRamsey632.CodingBounds
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Fin

/-!
The finite digit-position blocks.  Every original height follows all marker
positions for its finite tails, and there is a single increasing sequence of
original heights serving all relation arities.
-/

namespace RelationalRamsey632.Coding

variable (b : ℕ → ℕ)

abbrev Beta (n : ℕ) := Finset (Fin n) × Fin (CodingBounds.blockLength b n)

def blockCard (n : ℕ) : ℕ := Fintype.card (Beta b n)

theorem blockCard_eq (n : ℕ) :
    blockCard b n = 2 ^ n * CodingBounds.blockLength b n := by
  simp [blockCard, Beta]

def blockStart (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range n, (blockCard b m + 1)

def originalHeight (n : ℕ) : ℕ := blockStart b n + blockCard b n

noncomputable def betaPosition {n : ℕ} (β : Beta b n) : ℕ :=
  blockStart b n + (Fintype.equivFin (Beta b n) β).val

@[simp] theorem blockStart_zero : blockStart b 0 = 0 := by simp [blockStart]

@[simp] theorem blockStart_succ (n : ℕ) :
    blockStart b (n + 1) = blockStart b n + blockCard b n + 1 := by
  simp [blockStart, Finset.sum_range_succ, Nat.add_assoc]

theorem blockStart_strictMono : StrictMono (blockStart b) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [blockStart_succ]
  omega

theorem blockStart_ge (n : ℕ) : n ≤ blockStart b n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [blockStart_succ]
    omega

theorem originalHeight_lt_next (n : ℕ) : originalHeight b n < blockStart b (n + 1) := by
  simp [originalHeight]

theorem originalHeight_strictMono : StrictMono (originalHeight b) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (originalHeight_lt_next b n).trans_le (Nat.le_add_right _ _)

theorem betaPosition_lt_original {n : ℕ} (β : Beta b n) :
    betaPosition b β < originalHeight b n := by
  have h := (Fintype.equivFin (Beta b n) β).isLt
  exact Nat.add_lt_add_left h _

theorem blockStart_le_beta {n : ℕ} (β : Beta b n) : blockStart b n ≤ betaPosition b β :=
  Nat.le_add_right _ _

theorem original_lt_beta_of_lt {m n : ℕ} (hmn : m < n) (β : Beta b n) :
    originalHeight b m < betaPosition b β :=
  (originalHeight_lt_next b m).trans_le
    (((blockStart_strictMono b).monotone (by omega)).trans (blockStart_le_beta b β))

theorem beta_lt_original_of_le {m n : ℕ} (hmn : m ≤ n) (β : Beta b m) :
    betaPosition b β < originalHeight b n :=
  (betaPosition_lt_original b β).trans_le ((originalHeight_strictMono b).monotone hmn)

theorem betaPosition_ne_original {n : ℕ} (β : Beta b n) (m : ℕ) :
    betaPosition b β ≠ originalHeight b m := by
  by_cases hmn : m < n
  · exact (original_lt_beta_of_lt b hmn β).ne'
  · exact (beta_lt_original_of_le b (by omega) β).ne

theorem betaPosition_injective (n : ℕ) :
    Function.Injective (betaPosition b (n := n)) := by
  intro β γ h
  apply (Fintype.equivFin (Beta b n)).injective
  apply Fin.ext
  exact Nat.add_left_cancel h

noncomputable def allBetaPosition (β : Sigma (Beta b)) : ℕ := betaPosition b β.2

theorem allBetaPosition_injective : Function.Injective (allBetaPosition b) := by
  intro β γ h
  have hheight : β.1 = γ.1 := by
    apply Nat.le_antisymm
    · by_contra hnot
      have hlt : γ.1 < β.1 := by omega
      have h1 := betaPosition_lt_original b γ.2
      have h2 := original_lt_beta_of_lt b hlt β.2
      change betaPosition b β.2 = betaPosition b γ.2 at h
      omega
    · by_contra hnot
      have hlt : β.1 < γ.1 := by omega
      have h1 := betaPosition_lt_original b β.2
      have h2 := original_lt_beta_of_lt b hlt γ.2
      change betaPosition b β.2 = betaPosition b γ.2 at h
      omega
  cases β with
  | mk n β =>
    cases γ with
    | mk m γ =>
      dsimp only at hheight
      subst m
      exact congrArg (Sigma.mk n) (betaPosition_injective b n h)

def originalPositions : Set ℕ := Set.range (originalHeight b)
def digitPositions : Set ℕ := (originalPositions b)ᶜ

theorem original_digit_partition :
    originalPositions b ∪ digitPositions b = Set.univ := Set.union_compl_self _

theorem beta_mem_digit {n : ℕ} (β : Beta b n) : betaPosition b β ∈ digitPositions b := by
  rintro ⟨m, hm⟩
  exact betaPosition_ne_original b β m hm.symm

end RelationalRamsey632.Coding
