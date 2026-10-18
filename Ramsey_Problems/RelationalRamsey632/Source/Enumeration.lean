import RelationalRamsey632.Source.Rank
import Mathlib.Data.Finset.Sort

/-! An actual strictly increasing enumeration of a finite level set, continued
past its maximum to supply the total level map used by sampling. -/

namespace RelationalRamsey632.Source

noncomputable def levelEnumeration (L : Finset ℕ) (n : ℕ) : ℕ :=
  if hn : n < L.card then L.orderEmbOfFin rfl ⟨n, hn⟩
  else L.sup id + (n - L.card) + 1

theorem levelEnumeration_initial (L : Finset ℕ) {n : ℕ} (hn : n < L.card) :
    levelEnumeration L n = L.orderEmbOfFin rfl ⟨n, hn⟩ := by
  simp only [levelEnumeration, dif_pos hn]

theorem levelEnumeration_tail (L : Finset ℕ) {n : ℕ} (hn : L.card ≤ n) :
    levelEnumeration L n = L.sup id + (n - L.card) + 1 := by
  simp only [levelEnumeration, dif_neg (Nat.not_lt.mpr hn)]

theorem levelEnumeration_strictMono (L : Finset ℕ) :
    StrictMono (levelEnumeration L) := by
  intro m n hmn
  by_cases hn : n < L.card
  · have hm : m < L.card := hmn.trans hn
    rw [levelEnumeration_initial L hm, levelEnumeration_initial L hn]
    exact (L.orderEmbOfFin rfl).strictMono hmn
  · have hnc : L.card ≤ n := Nat.le_of_not_gt hn
    by_cases hm : m < L.card
    · rw [levelEnumeration_initial L hm, levelEnumeration_tail L hnc]
      have hle : L.orderEmbOfFin rfl ⟨m, hm⟩ ≤ L.sup id :=
        Finset.le_sup (f := id) (L.orderEmbOfFin_mem rfl ⟨m, hm⟩)
      omega
    · have hmc : L.card ≤ m := Nat.le_of_not_gt hm
      rw [levelEnumeration_tail L hmc, levelEnumeration_tail L hnc]
      omega

theorem levelEnumeration_range_contains (L : Finset ℕ) {n : ℕ} (hn : n ∈ L) :
    ∃ k, n = levelEnumeration L k := by
  let k := (L.orderIsoOfFin rfl).symm ⟨n, hn⟩
  refine ⟨k.val, ?_⟩
  rw [levelEnumeration_initial L k.isLt]
  exact congrArg Subtype.val ((L.orderIsoOfFin rfl).apply_symm_apply ⟨n, hn⟩).symm

theorem levelEnumeration_mem_iff (L : Finset ℕ) (k : ℕ) :
    levelEnumeration L k ∈ L ↔ k < L.card := by
  constructor
  · intro h
    by_contra hn
    rw [levelEnumeration_tail L (Nat.le_of_not_gt hn)] at h
    have hle := Finset.le_sup (f := id) h
    dsimp only [id] at hle
    omega
  · intro h
    rw [levelEnumeration_initial L h]
    exact L.orderEmbOfFin_mem rfl ⟨k, h⟩

end RelationalRamsey632.Source
