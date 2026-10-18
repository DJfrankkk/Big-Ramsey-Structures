import RelationalRamsey632.Coding.Blocks
import Mathlib.Data.Finset.Max

/-!
The literal fixed-alphabet marker blocks from the combined article.
Here `colours j` is n_(j+1); the valuation alphabet is exactly n_(j+1)+2.
A marker for a suffix with maximum n and cardinality r has cutoff
max_(d<=n) n_(d+r+1), with no alphabet enlargement or global arity bound.
-/

namespace CombinedRamsey.Positive.Marker

variable (colours : ℕ → ℕ)

abbrev Alphabet (j : ℕ) := Fin (colours j + 2)

instance alphabetNonzero (j : ℕ) : NeZero (colours j + 2) := ⟨by omega⟩

def cutoff (n r : ℕ) : ℕ :=
  (Finset.range (n + 1)).sup (fun d => colours (d + r))

theorem colour_le_cutoff {n r d : ℕ} (hd : d ≤ n) : colours (d + r) ≤ cutoff colours n r :=
  Finset.le_sup (f := fun d => colours (d + r)) (Finset.mem_range.mpr (by omega))

abbrev Block (n : ℕ) := (s : Finset (Fin n)) × Fin (cutoff colours n (s.card + 1))

def blockCard (n : ℕ) : ℕ := Fintype.card (Block colours n)

def blockStart (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range n, (blockCard colours m + 1)

def originalHeight (n : ℕ) : ℕ := blockStart colours n + blockCard colours n

noncomputable def markerPosition {n : ℕ} (b : Block colours n) : ℕ :=
  blockStart colours n + (Fintype.equivFin (Block colours n) b).val

@[simp] theorem blockStart_zero : blockStart colours 0 = 0 := by simp [blockStart]

@[simp] theorem blockStart_succ (n : ℕ) :
    blockStart colours (n + 1) = blockStart colours n + blockCard colours n + 1 := by
  simp [blockStart, Finset.sum_range_succ, Nat.add_assoc]

theorem blockStart_strictMono : StrictMono (blockStart colours) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [blockStart_succ]
  omega

theorem blockStart_ge (n : ℕ) : n ≤ blockStart colours n := by
  induction n with
  | zero => simp
  | succ n ih => rw [blockStart_succ]; omega

theorem originalHeight_lt_next (n : ℕ) :
    originalHeight colours n < blockStart colours (n + 1) := by simp [originalHeight]

theorem originalHeight_strictMono : StrictMono (originalHeight colours) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (originalHeight_lt_next colours n).trans_le (Nat.le_add_right _ _)

theorem markerPosition_lt_original {n : ℕ} (b : Block colours n) :
    markerPosition colours b < originalHeight colours n := by
  exact Nat.add_lt_add_left (Fintype.equivFin (Block colours n) b).isLt _

theorem blockStart_le_marker {n : ℕ} (b : Block colours n) :
    blockStart colours n ≤ markerPosition colours b := Nat.le_add_right _ _

theorem original_lt_marker_of_lt {m n : ℕ} (hmn : m < n) (b : Block colours n) :
    originalHeight colours m < markerPosition colours b :=
  (originalHeight_lt_next colours m).trans_le
    (((blockStart_strictMono colours).monotone (by omega)).trans (blockStart_le_marker colours b))

theorem marker_lt_original_of_le {m n : ℕ} (hmn : m ≤ n) (b : Block colours m) :
    markerPosition colours b < originalHeight colours n :=
  (markerPosition_lt_original colours b).trans_le ((originalHeight_strictMono colours).monotone hmn)

theorem markerPosition_ne_original {n : ℕ} (b : Block colours n) (m : ℕ) :
    markerPosition colours b ≠ originalHeight colours m := by
  by_cases hmn : m < n
  · exact (original_lt_marker_of_lt colours hmn b).ne'
  · exact (marker_lt_original_of_le colours (by omega) b).ne

theorem markerPosition_injective (n : ℕ) :
    Function.Injective (markerPosition colours (n := n)) := by
  intro b c h
  apply (Fintype.equivFin (Block colours n)).injective
  apply Fin.ext
  exact Nat.add_left_cancel h

noncomputable def allMarkerPosition (b : Sigma (Block colours)) : ℕ := markerPosition colours b.2

theorem allMarkerPosition_injective : Function.Injective (allMarkerPosition colours) := by
  intro b c h
  have hheight : b.1 = c.1 := by
    apply Nat.le_antisymm
    · by_contra hnot
      have hlt : c.1 < b.1 := by omega
      have h1 := markerPosition_lt_original colours c.2
      have h2 := original_lt_marker_of_lt colours hlt b.2
      change markerPosition colours b.2 = markerPosition colours c.2 at h
      omega
    · by_contra hnot
      have hlt : b.1 < c.1 := by omega
      have h1 := markerPosition_lt_original colours b.2
      have h2 := original_lt_marker_of_lt colours hlt c.2
      change markerPosition colours b.2 = markerPosition colours c.2 at h
      omega
  cases b with
  | mk n b =>
    cases c with
    | mk m c =>
      dsimp only at hheight
      subst m
      exact congrArg (Sigma.mk n) (markerPosition_injective colours n h)

def originalPositions : Set ℕ := Set.range (originalHeight colours)
def markerPositions : Set ℕ := (originalPositions colours)ᶜ

theorem marker_mem_markerPositions {n : ℕ} (b : Block colours n) :
    markerPosition colours b ∈ markerPositions colours := by
  rintro ⟨m, hm⟩
  exact markerPosition_ne_original colours b m hm.symm

def suffix {n : ℕ} (b : Block colours n) : Finset ℕ := insert n (b.1.image Fin.val)

theorem suffix_nonempty {n : ℕ} (b : Block colours n) : (suffix colours b).Nonempty := by
  simp [suffix]

theorem suffix_le {n : ℕ} (b : Block colours n) {x : ℕ}
    (hx : x ∈ suffix colours b) : x ≤ n := by
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact le_rfl
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Nat.le_of_lt i.isLt

theorem suffix_card {n : ℕ} (b : Block colours n) :
    (suffix colours b).card = b.1.card + 1 := by
  have hn : n ∉ b.1.image Fin.val := by
    intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    have := i.isLt
    omega
  rw [suffix, Finset.card_insert_of_notMem hn, Finset.card_image_of_injective _ Fin.val_injective]

end CombinedRamsey.Positive.Marker
