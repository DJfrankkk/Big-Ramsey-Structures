import RelationalRamsey632.Coding.Precompactness
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Exact finite node counts used in the normal-form upper bound. -/

namespace RelationalRamsey632.Source

open scoped BigOperators

def CoordinateFiber (n r : ℕ) := {s : Coordinate n // s.val.card = r}

noncomputable def coordinateFiberEquiv (n r : ℕ) (hr : 0 < r) :
    CoordinateFiber n r ≃ {s : Finset ℕ // s ∈ (Finset.range n).powersetCard r} where
  toFun s := ⟨s.val.val, Finset.mem_powersetCard.mpr ⟨s.val.property.2, s.property⟩⟩
  invFun s := ⟨⟨s.val, Finset.card_pos.mp (by
      rw [(Finset.mem_powersetCard.mp s.property).2]
      exact hr), (Finset.mem_powersetCard.mp s.property).1⟩,
      (Finset.mem_powersetCard.mp s.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem coordinateFiber_card (n r : ℕ) (hr : 0 < r) :
    Nat.card (CoordinateFiber n r) = n.choose r := by
  rw [Nat.card_congr (coordinateFiberEquiv n r hr), Nat.card_eq_fintype_card,
    Fintype.card_coe, Finset.card_powersetCard, Finset.card_range]

theorem coordinate_rank_bound (n : ℕ) (s : Coordinate n) : s.val.card ∈ Finset.Icc 1 n := by
  exact Finset.mem_Icc.mpr ⟨s.positive_card,
    by simpa using Finset.card_le_card s.property.2⟩

theorem level_card (A : ℕ → Type) [∀ j, Fintype (A j)] (i n : ℕ) :
    Nat.card (Level A i n) =
      ∏ r ∈ Finset.Icc 1 n, (Fintype.card (A (i + r))) ^ n.choose r := by
  classical
  unfold Level
  rw [Nat.card_eq_fintype_card, Fintype.card_pi]
  rw [← Finset.prod_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Coordinate n)))
    (t := Finset.Icc 1 n) (g := fun s => s.val.card)
    (fun s _ => coordinate_rank_bound n s) (fun s => Fintype.card (A (i + s.val.card)))]
  apply Finset.prod_congr rfl
  intro r hr
  have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
  calc
    (∏ s ∈ Finset.univ.filter (fun s : Coordinate n => s.val.card = r),
        Fintype.card (A (i + s.val.card))) =
      ∏ _s ∈ Finset.univ.filter (fun s : Coordinate n => s.val.card = r),
        Fintype.card (A (i + r)) := by
      apply Finset.prod_congr rfl
      intro s hs
      rw [(Finset.mem_filter.mp hs).2]
    _ = (Fintype.card (A (i + r))) ^ n.choose r := by
      rw [Finset.prod_const]
      congr 1
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact coordinateFiber_card n r hrpos

noncomputable def boundedNodesEquiv (A : ℕ → Type) (B : ℕ) :
    BoundedNodes A B ≃ Σ n : Fin B, Level A 0 n.val where
  toFun t := ⟨⟨t.val.height, t.property⟩, t.val.table⟩
  invFun t := ⟨⟨t.fst.val, t.snd⟩, t.fst.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem boundedNodes_card (A : ℕ → Type) [∀ j, Fintype (A j)] (B : ℕ) :
    Nat.card (BoundedNodes A B) =
      ∑ h : Fin B, ∏ r ∈ Finset.Icc 1 h.val,
        Fintype.card (A r) ^ h.val.choose r := by
  rw [Nat.card_congr (boundedNodesEquiv A B), Nat.card_eq_fintype_card, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro h _
  have hh := level_card A 0 h.val
  simpa only [Nat.card_eq_fintype_card, Nat.zero_add] using hh

end RelationalRamsey632.Source
