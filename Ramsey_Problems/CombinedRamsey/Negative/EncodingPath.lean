import CombinedRamsey.Negative.EncodingTables

/-! The guarded three-state path forces exactly one marker, including endpoints. -/

namespace CombinedRamsey.Negative

open Table

def phaseNat (m l : ℕ) : State :=
  if l < m then .zero else if l = m then .one else .two

def phase {k : ℕ} (i : Fin k) (l : Fin (k + 2)) : State :=
  phaseNat (i.val + 1) l.val

theorem phaseNat_one_iff (m l : ℕ) : phaseNat m l = .one ↔ l = m := by
  unfold phaseNat
  split_ifs <;> simp_all
  all_goals omega

theorem phaseNat_zero_iff (m l : ℕ) : phaseNat m l = .zero ↔ l < m := by
  unfold phaseNat
  split_ifs <;> simp_all

theorem phaseNat_two_iff (m l : ℕ) : phaseNat m l = .two ↔ m < l := by
  unfold phaseNat
  split_ifs <;> simp_all <;> omega

theorem phaseNat_transition (m l : ℕ) : Transition (phaseNat m l) (phaseNat m (l+1)) := by
  unfold phaseNat Transition
  split_ifs <;> simp_all <;> omega

theorem transition_from_one {s : State} (h : Transition .one s) : s = .two := by
  rcases h with h | h | h | h <;> simp_all

theorem transition_from_two {s : State} (h : Transition .two s) : s = .two := by
  rcases h with h | h | h | h <;> simp_all

theorem two_tail (s : ℕ → State) (m n : ℕ) (hstart : s m = .two)
    (ht : ∀ l < m+n, Transition (s l) (s (l+1))) : s (m+n) = .two := by
  induction n with
  | zero => simpa using hstart
  | succ n ih =>
    have hp : s (m+n) = .two := ih (fun l hl => ht l (by omega))
    have hn := ht (m+n) (by omega)
    rw [hp] at hn
    simpa [Nat.add_assoc] using transition_from_two hn

theorem automaton_marker (k : ℕ) (s : ℕ → State)
    (hfirst : s 0 = .zero) (hlast : s (k+1) = .two)
    (ht : ∀ l ≤ k, Transition (s l) (s (l+1))) :
    ∃ m, 1 ≤ m ∧ m ≤ k ∧ ∀ l ≤ k+1, s l = phaseNat m l := by
  induction k generalizing s with
  | zero =>
    have h := ht 0 (by omega)
    rw [hfirst, hlast] at h
    simp [Transition] at h
  | succ k ih =>
    have h01 := ht 0 (by omega)
    rw [hfirst] at h01
    have hcases : s 1 = .zero ∨ s 1 = .one := by
      rcases h01 with h | h | h | h <;> simp_all
    rcases hcases with hz | ho
    · obtain ⟨m, hm1, hmk, hm⟩ := ih (fun l => s (l+1)) hz
        (by simpa [Nat.add_assoc] using hlast)
        (fun l hl => by simpa [Nat.add_assoc] using ht (l+1) (by omega))
      refine ⟨m+1, by omega, by omega, ?_⟩
      intro l hl
      rcases l with _ | l
      · simp [hfirst, phaseNat]
      · have h := hm l (by omega)
        simpa [phaseNat, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff] using h
    · refine ⟨1, by omega, by omega, ?_⟩
      intro l hl
      rcases l with _ | l
      · simp [hfirst, phaseNat]
      rcases l with _ | l
      · simpa [phaseNat] using ho
      · have h12 := ht 1 (by omega)
        rw [ho] at h12
        have hs2 : s 2 = .two := by simpa using transition_from_one h12
        have hs := two_tail s 2 l hs2 (fun j hj => ht j (by omega))
        have hp : phaseNat 1 (l+1+1) = .two := by simp [phaseNat]
        rw [hp]
        convert hs using 1
        congr 1
        omega

theorem finite_path_marker {k : ℕ} (s : Fin (k+2) → State)
    (hfirst : s ⟨0, by omega⟩ = .zero)
    (hlast : s ⟨k+1, by omega⟩ = .two)
    (ht : ∀ l : Fin (k+1), Transition (s ⟨l.val, by omega⟩)
      (s ⟨l.val+1, by omega⟩)) :
    ∃ i : Fin k, ∀ l, s l = phase i l := by
  let sn : ℕ → State := fun l => if hl : l < k+2 then s ⟨l, hl⟩ else .zero
  obtain ⟨m, hm1, hmk, hm⟩ := automaton_marker k sn
    (by simpa [sn] using hfirst) (by simpa [sn] using hlast)
    (fun l hl => by
      have hv := ht (⟨l, by omega⟩ : Fin (k+1))
      simpa [sn, show l < k+2 by omega, show l+1 < k+2 by omega] using hv)
  refine ⟨⟨m-1, by omega⟩, ?_⟩
  intro l
  have h := hm l.val (by omega)
  simpa [sn, l.isLt, phase, show m-1+1=m by omega] using h

theorem finite_marker_unique {k : ℕ} {i j : Fin k}
    (h : ∀ l : Fin (k+2), phase i l = phase j l) : i = j := by
  have hm := h ⟨i.val+1, by omega⟩
  have hi : phase i ⟨i.val+1, by omega⟩ = .one := by simp [phase, phaseNat]
  rw [hi] at hm
  have hval := (phaseNat_one_iff (j.val+1) (i.val+1)).mp hm.symm
  exact Fin.ext (by omega)

end CombinedRamsey.Negative
