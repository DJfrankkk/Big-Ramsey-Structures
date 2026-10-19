import RelationalRamsey632.Milliken.DenseSetFromMatrices

namespace RelationalRamsey632.Milliken

open Filter
open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

variable {I : Type} [Fintype I] [DecidableEq I]
    {α : I → Type} [∀ i, DecidableEq (α i)]
    {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))

def FixedColorLevelMatrix {K : Type} (roots : VectorNode T) (k : ℕ)
    (color : K) (c : VectorNode T → K) : Prop :=
  ∃ N, ∃ columns : ∀ i, Finset (T i).TreeNode,
    (∀ i u, u ∈ columns i → (T i).nodeHeight u = N) ∧
    (∀ i, (T i).DenseAbove (roots i) k (columns i)) ∧
    ∀ x ∈ Fintype.piFinset columns, c x = color

theorem fixedColorLevelMatrix_downward {K : Type} (roots : VectorNode T)
    {m n : ℕ} (hmn : m ≤ n) (color : K) (c : VectorNode T → K)
    (h : FixedColorLevelMatrix T roots n color c) : FixedColorLevelMatrix T roots m color c := by
  obtain ⟨N, columns, hheight, hdense, hcolor⟩ := h
  exact ⟨N, columns, hheight,
    fun i => (T i).denseAbove_mono (roots i) hmn (hdense i), hcolor⟩

/-- Finite colors can be fixed once for all density thresholds. The same
free ultrafilter picks the cofinal color; the matrices themselves are the
already constructed genuine synchronized rectangles. -/
theorem fixed_color_dense_sets {K : Type} [Fintype K]
    (c : VectorNode T → K) (d : ℕ) (roots : VectorNode T)
    (hroots : ∀ i, (T i).nodeHeight (roots i) = d)
    (hD : ∀ k, LevelMatrixColor T roots k c) :
    ∃ color : K, ∀ k, FixedColorLevelMatrix T roots k color c := by
  classical
  have hmat : ∀ n, ∃ color : K, FixedColorLevelMatrix T roots (d + n) color c := by
    intro n
    obtain ⟨N, columns, hheight, hdense, hmono⟩ := hD (d + n)
    have hne : ∀ i, (columns i).Nonempty := by
      intro i
      obtain ⟨u, hu, hru⟩ := (T i).extend d (d + n) (Nat.le_add_right _ _)
        (roots i).val (hroots i ▸ (T i).nodeHeight_mem (roots i))
      obtain ⟨v, hv, _⟩ := hdense i u hu hru
      exact ⟨v, hv⟩
    obtain ⟨x0, hx0⟩ := Fintype.piFinset_nonempty.mpr hne
    exact ⟨c x0, N, columns, hheight, hdense, fun x hx => hmono x hx x0 hx0⟩
  choose colors hcolors using hmat
  let U := Ultrafilter.of (atTop : Filter ℕ)
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  have hall : ∀ᶠ n in U, ∃ color : K, colors n = color :=
    Filter.Eventually.of_forall (fun n => ⟨colors n, rfl⟩)
  obtain ⟨color, hcolor⟩ := Ultrafilter.eventually_exists_iff.mp hall
  refine ⟨color, ?_⟩
  intro k
  obtain ⟨n, hncolor, hnk⟩ :=
    (hcolor.and ((eventually_ge_atTop k).filter_mono hU)).exists
  have hh := hcolors n
  rw [hncolor] at hh
  exact fixedColorLevelMatrix_downward T roots (hnk.trans (Nat.le_add_left _ _)) color c hh

end RelationalRamsey632.Milliken
