import RelationalRamsey632.Milliken.VectorMatrices

/-! The full mixed SDHL schema on whole-level restrictions gives a cone
with monochromatic synchronized dense matrices at every density threshold.
This is the internal SDHL-to-DS step of the dimension induction. -/

namespace RelationalRamsey632.Milliken

open Generic3Ramsey.SourceTrees
open Generic3Ramsey.SourceTrees.FiniteLevelTree

variable {I : Type} [Fintype I] [DecidableEq I]
    {α : I → Type} [∀ i, DecidableEq (α i)]
    {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))

def LevelMatrixColor {K : Type} (roots : VectorNode T) (k : ℕ)
    (c : VectorNode T → K) : Prop :=
  ∃ N, ∃ columns : ∀ i, Finset (T i).TreeNode,
    (∀ i u, u ∈ columns i → (T i).nodeHeight u = N) ∧
    (∀ i, (T i).DenseAbove (roots i) k (columns i)) ∧
    Monochromatic c (Fintype.piFinset columns)

theorem levelMatrixColor_downward {K : Type} (roots : VectorNode T)
    {m n : ℕ} (hmn : m ≤ n) (c : VectorNode T → K)
    (h : LevelMatrixColor T roots n c) : LevelMatrixColor T roots m c := by
  obtain ⟨N, columns, hheight, hdense, hmono⟩ := h
  exact ⟨N, columns, hheight, fun i => (T i).denseAbove_mono (roots i) hmn (hdense i), hmono⟩

/-- No level restriction, matrix synchronization, or density strengthening
is postulated inside the proof. Only the mixed Ramsey theorem for each
actual whole-level restricted vector is an explicit input. -/
theorem dense_sets_from_restricted_mixed {K : Type} [Fintype K]
    (hMixed : ∀ (index : ℕ → ℕ) (hm : StrictMono index) (hz : index 0 = 0),
      MixedSDHL (fun i => (T i).restrictLevels index hm hz) K)
    (c : VectorNode T → K) :
    ∃ d, ∃ roots : VectorNode T,
      (∀ i, (T i).nodeHeight (roots i) = d) ∧
        ∀ k, LevelMatrixColor T roots k c := by
  classical
  by_contra hfail
  have hbad : ∀ roots : VectorNode T,
      (∃ d, ∀ i, (T i).nodeHeight (roots i) = d) →
        ∃ k, ¬LevelMatrixColor T roots k c := by
    intro roots ⟨d, hd⟩
    by_contra hb
    apply hfail
    refine ⟨d, roots, hd, ?_⟩
    simpa only [not_exists, not_not] using hb
  let cutoff : VectorNode T → ℕ := fun roots =>
    if hr : ∃ d, ∀ i, (T i).nodeHeight (roots i) = d then Nat.find (hbad roots hr) else 0
  have hcutoff : ∀ roots : VectorNode T,
      (∃ d, ∀ i, (T i).nodeHeight (roots i) = d) →
        ∀ k, cutoff roots ≤ k → ¬LevelMatrixColor T roots k c := by
    intro roots hr k hk hmatrix
    have hbad0 : ¬LevelMatrixColor T roots (cutoff roots) c := by
      dsimp only [cutoff]
      rw [dif_pos hr]
      exact Nat.find_spec (hbad roots hr)
    exact hbad0 (levelMatrixColor_downward T roots hk c hmatrix)
  let index : ℕ → ℕ := fun n => Nat.rec 0
    (fun _ m => max (m + 1) ((vectorBoundedNodes T m).sup cutoff + 1)) n
  have hm : StrictMono index := by
    apply strictMono_nat_of_lt_succ
    intro n
    change index n < max (index n + 1) ((vectorBoundedNodes T (index n)).sup cutoff + 1)
    exact (Nat.lt_succ_self _).trans_le (Nat.le_max_left _ _)
  have hz : index 0 = 0 := rfl
  let T' := fun i => (T i).restrictLevels index hm hz
  let map : ∀ i, (T' i).TreeNode → (T i).TreeNode :=
    fun i => (T i).restrictionNodeMap632 index hm hz
  let mapVector : VectorNode T' → VectorNode T := fun x i => map i (x i)
  obtain ⟨N, D, hheight, hmono⟩ := vector_synchronized_of_mixed T' (hMixed index hm hz)
    (c ∘ mapVector)
  let roots := mapVector D.roots
  have hrheight : ∀ i, (T i).nodeHeight (roots i) = index D.depth := by
    intro i
    exact ((T i).restrictionNodeMap632_height index hm hz (D.roots i)).trans
      (congrArg index (D.root_height i))
  have hroots : roots ∈ vectorBoundedNodes T (index D.depth) := by
    apply Fintype.mem_piFinset.mpr
    intro i
    exact (mem_boundedNodes (T i) _ _).mpr (hrheight i).le
  have hless : cutoff roots < index (D.depth + 1) := by
    have hh := Finset.le_sup (f := cutoff) hroots
    change cutoff roots < max (index D.depth + 1)
      ((vectorBoundedNodes T (index D.depth)).sup cutoff + 1)
    exact (Nat.lt_of_le_of_lt hh (Nat.lt_succ_self _)).trans_le (Nat.le_max_right _ _)
  apply hcutoff roots ⟨index D.depth, hrheight⟩ (index (D.depth + 1)) hless.le
  let columns := fun i => (D.columns i).image (map i)
  refine ⟨index N, columns, ?_, ?_, ?_⟩
  · intro i u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact ((T i).restrictionNodeMap632_height index hm hz v).trans (congrArg index (hheight i v hv))
  · intro i u hu hru
    obtain ⟨v, hv, huv⟩ := D.dense i u hu hru
    exact ⟨map i v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, huv⟩
  · have hs : Fintype.piFinset columns = D.support.image mapVector :=
      Fintype.piFinset_image map D.columns
    intro x hx y hy
    rw [hs] at hx hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact hmono a ha b hb

end RelationalRamsey632.Milliken
