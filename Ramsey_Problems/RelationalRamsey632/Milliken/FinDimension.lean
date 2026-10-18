import RelationalRamsey632.Milliken.HalpernLauchli

namespace RelationalRamsey632.Milliken

open Generic3Ramsey.SourceTrees
open Generic3Ramsey.SourceTrees.FiniteLevelTree

/-- A genuine d-coordinate rectangle times its last-coordinate family
is a genuine (d+1)-coordinate matrix. The coordinate split is bijective,
with no loss of any mixed tuple or any successor cone. -/
theorem mixed_last_to_full {d : ℕ}
    {α : Fin (d + 1) → Type} [∀ i, DecidableEq (α i)]
    {R : ∀ i, α i → α i → Prop}
    (T : ∀ i, FiniteLevelTree (α i) (R i))
    {K : Type} (c : VectorNode T → K)
    (h : MixedLastMatrixColor (fun i : Fin d => T i.castSucc) (T (Fin.last d))
      (fun x y => c (Fin.lastCases y x))) :
    ∃ D : VectorMatrix T, Monochromatic c D.support := by
  classical
  obtain ⟨depth, roots, lastRoot, columns, last, color, hr, hs, hdense, hlast, hcolor⟩ := h
  let fullRoots : VectorNode T := Fin.lastCases lastRoot roots
  let fullColumns : ∀ i, Finset (T i).TreeNode := Fin.lastCases last columns
  have hheight : ∀ i, (T i).nodeHeight (fullRoots i) = depth := by
    intro j
    refine Fin.lastCases ?_ ?_ j
    · simpa only [fullRoots, Fin.lastCases_last] using hs
    · intro i
      simpa only [fullRoots, Fin.lastCases_castSucc] using hr i
  have hD : ∀ i, (T i).DenseAbove (fullRoots i) (depth + 1) (fullColumns i) := by
    intro j
    refine Fin.lastCases ?_ ?_ j
    · simpa only [fullRoots, fullColumns, Fin.lastCases_last] using hlast
    · intro i
      simpa only [fullRoots, fullColumns, Fin.lastCases_castSucc] using hdense i
  let D : VectorMatrix T := ⟨depth, fullRoots, hheight, fullColumns, hD⟩
  have hconstant : ∀ x ∈ D.support, c x = color := by
    intro x hx
    let first := fun i : Fin d => x i.castSucc
    let final := x (Fin.last d)
    have hfirst : first ∈ Fintype.piFinset columns := by
      apply Fintype.mem_piFinset.mpr
      intro i
      have hh := Fintype.mem_piFinset.mp hx i.castSucc
      simpa only [D, fullColumns, Fin.lastCases_castSucc, first] using hh
    have hfinal : final ∈ last := by
      have hh := Fintype.mem_piFinset.mp hx (Fin.last d)
      simpa only [D, fullColumns, Fin.lastCases_last, final] using hh
    have heq : Fin.lastCases final first = x := by
      funext j
      refine Fin.lastCases ?_ ?_ j
      · simp only [Fin.lastCases_last, final]
      · intro i
        simp only [Fin.lastCases_castSucc, first]
    have hh := hcolor first hfirst final hfinal
    change c (Fin.lastCases final first) = color at hh
    rw [heq] at hh
    exact hh
  exact ⟨D, fun x hx y hy => (hconstant x hx).trans (hconstant y hy).symm⟩

end RelationalRamsey632.Milliken
