import RelationalRamsey632.Milliken.SynchronizedTwoTrees
import Mathlib.Data.Fintype.Pi

/-! Actual finite-dimensional Cartesian matrices. The synchronization
implication is proved for every finite dimension and every finite color
set. Its mixed SDHL input is explicit; this file does not assert that
input, nor conflate a dense set of product-tree vertices with a rectangle. -/

namespace RelationalRamsey632.Milliken

open Filter
open Generic3Ramsey.SourceTrees
open Generic3Ramsey.SourceTrees.FiniteLevelTree

variable {I : Type} [Fintype I] [DecidableEq I]
    {α : I → Type} [∀ i, DecidableEq (α i)]
    {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))

abbrev VectorNode := ∀ i, (T i).TreeNode

structure VectorMatrix where
  depth : ℕ
  roots : VectorNode T
  root_height : ∀ i, (T i).nodeHeight (roots i) = depth
  columns : ∀ i, Finset (T i).TreeNode
  dense : ∀ i, (T i).DenseAbove (roots i) (depth + 1) (columns i)

namespace VectorMatrix

variable {T} (D : VectorMatrix T)

def support : Finset (VectorNode T) := Fintype.piFinset D.columns

omit [Fintype I] [DecidableEq I] in
theorem column_nonempty (i : I) : (D.columns i).Nonempty := by
  obtain ⟨u, hu, hru⟩ := (T i).extend D.depth (D.depth + 1) (Nat.le_succ _)
    (D.roots i).val (D.root_height i ▸ (T i).nodeHeight_mem (D.roots i))
  obtain ⟨v, hv, _⟩ := D.dense i u hu hru
  exact ⟨v, hv⟩

theorem support_nonempty : D.support.Nonempty :=
  Fintype.piFinset_nonempty.mpr D.column_nonempty

end VectorMatrix

def MixedSDHL (K : Type) : Prop :=
  ∀ c : VectorNode T → K, ∃ D : VectorMatrix T, Monochromatic c D.support

/-- Actual homogeneous strong subtrees with one shared level map. This
is the SS interface used in the finite-frontier dimension induction. -/
structure HomogeneousStrongVector {K : Type} (c : VectorNode T → K) where
  index : ℕ → ℕ
  index_strictMono : StrictMono index
  frames : ∀ i, (T i).StrongFrame
  frame_index : ∀ i, (frames i).index = index
  color : K
  colored : ∀ n (x : VectorNode T),
    (∀ i, (x i).val ∈ (frames i).nodes n) → c x = color

def StrongSubtreeRamsey (K : Type) : Prop :=
  ∀ c : VectorNode T → K, Nonempty (HomogeneousStrongVector T c)

noncomputable def vectorBoundedNodes (N : ℕ) : Finset (VectorNode T) :=
  Fintype.piFinset (fun i => boundedNodes (T i) N)

theorem vector_finite_matrix_bound {K : Type} [Fintype K] (hMixed : MixedSDHL T K) :
    ∃ N, ∀ c : VectorNode T → K, ∃ D : VectorMatrix T,
      D.support ⊆ vectorBoundedNodes T N ∧ Monochromatic c D.support := by
  have hc : ∀ x : VectorNode T, ∀ᶠ N in atTop, x ∈ vectorBoundedNodes T N := by
    intro x
    have hall : ∀ᶠ N in atTop, ∀ i, (T i).nodeHeight (x i) ≤ N :=
      Filter.eventually_all.mpr (fun i => eventually_ge_atTop ((T i).nodeHeight (x i)))
    apply hall.mono
    intro N hN
    exact Fintype.mem_piFinset.mpr (fun i => (mem_boundedNodes (T i) N (x i)).mpr (hN i))
  obtain ⟨N, hN⟩ := finite_color_compactness
    (fun D : VectorMatrix T => D.support) (fun _ => True) (vectorBoundedNodes T) hc
    (fun c => by obtain ⟨D, hD⟩ := hMixed c; exact ⟨D, trivial, hD⟩)
  exact ⟨N, fun c => by obtain ⟨D, _, hD, hm⟩ := hN c; exact ⟨D, hD, hm⟩⟩

/-- Synchronization in any finite dimension. This is the genuine internal
mixed-to-level SDHL implication, with all rectangular structure retained. -/
theorem vector_synchronized_of_mixed {K : Type} [Fintype K]
    (hMixed : MixedSDHL T K) (c : VectorNode T → K) :
    ∃ N, ∃ D : VectorMatrix T,
      (∀ i u, u ∈ D.columns i → (T i).nodeHeight u = N) ∧ Monochromatic c D.support := by
  classical
  obtain ⟨N, hN⟩ := vector_finite_matrix_bound T hMixed
  let raise : VectorNode T → VectorNode T := fun x i => raiseNode (T i) N (x i)
  obtain ⟨D, hbound, hmono⟩ := hN (c ∘ raise)
  obtain ⟨x0, hx0⟩ := D.support_nonempty
  have hheight : ∀ i u, u ∈ D.columns i → (T i).nodeHeight u ≤ N := by
    intro i u hu
    let x : VectorNode T := Function.update x0 i u
    have hx : x ∈ D.support := by
      apply Fintype.mem_piFinset.mpr
      intro j
      by_cases hj : j = i
      · subst j
        simpa [x] using hu
      · simpa [x, hj] using (Fintype.mem_piFinset.mp hx0 j)
    have hh := Fintype.mem_piFinset.mp (hbound hx) i
    have hh' : u ∈ boundedNodes (T i) N := by simpa [x] using hh
    exact (mem_boundedNodes (T i) N u).mp hh'
  let columns := fun i => (D.columns i).image (raiseNode (T i) N)
  have hdense : ∀ i, (T i).DenseAbove (D.roots i) (D.depth + 1) (columns i) := by
    intro i u hu hru
    obtain ⟨v, hv, huv⟩ := D.dense i u hu hru
    exact ⟨raiseNode (T i) N v, Finset.mem_image.mpr ⟨v, hv, rfl⟩,
      (T i).rel_trans huv (raiseNode_extends (T i) N v (hheight i v hv))⟩
  let D' : VectorMatrix T := ⟨D.depth, D.roots, D.root_height, columns, hdense⟩
  have hs : D'.support = D.support.image raise :=
    Fintype.piFinset_image (fun i => raiseNode (T i) N) D.columns
  refine ⟨N, D', ?_, ?_⟩
  · intro i u hu
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
    exact raiseNode_height (T i) N v
  · intro x hx y hy
    rw [hs] at hx hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact hmono a ha b hb

end RelationalRamsey632.Milliken
