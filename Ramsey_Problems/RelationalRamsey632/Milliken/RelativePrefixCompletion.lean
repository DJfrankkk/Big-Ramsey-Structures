import RelationalRamsey632.Milliken.HeightFrames
import RelationalRamsey632.Milliken.PrefixExtension

/-! Relative strongness and completion of finite cores are derived from
actual ambient successor cones, rather than assumed from set inclusion. -/

namespace RelationalRamsey632.Milliken

open Generic3Ramsey.SourceTrees
open Generic3Ramsey.SourceTrees.FiniteLevelTree

variable {α : Type} [DecidableEq α] {R : α → α → Prop}
    {T : FiniteLevelTree α R} (F G : T.StrongFrame)
    (l : ℕ → ℕ) (hl : StrictMono l) (h : ℕ)
    (hsub : ∀ n, n < h → G.nodes n ⊆ F.nodes (l n))

noncomputable def relativeFinitePrefix : FiniteStrongPrefix F.toTree l h where
  index_strictMono := hl
  nodes := G.nodes
  root := G.root
  nodes_zero := G.nodes_zero
  nodes_subset := hsub
  parent n _ := G.parent n
  successor n hn u hu v hv huv := by
    have huF : u ∈ F.nodes (l n) := hsub n (by omega) hu
    have huT := G.nodes_subset n hu
    have hindex : G.index n = F.index (l n) :=
      T.level_unique _ _ u huT (F.nodes_subset (l n) huF)
    have hgap : G.index n + 1 ≤ F.index (l n + 1) := by
      rw [hindex]
      exact Nat.succ_le_of_lt (F.index_strictMono (Nat.lt_succ_self (l n)))
    have hvT := F.nodes_subset (l n + 1) hv
    obtain ⟨a, ⟨ha, hav⟩, _⟩ :=
      T.ancestor (G.index n + 1) (F.index (l n + 1)) hgap v hvT
    have hua : R u a := T.ancestor_comparable (G.index n) (G.index n + 1)
      (F.index (l n + 1)) (Nat.le_succ _) u a v huT ha hvT huv hav
    obtain ⟨w, ⟨hw, haw⟩, hwuniq⟩ := G.successor n u hu a ha hua
    have hwF : w ∈ F.nodes (l (n + 1)) := hsub (n + 1) hn hw
    have haF : a ∈ T.nodes (F.index (l n) + 1) := hindex ▸ ha
    obtain ⟨b, _, hbuniq⟩ := F.successor (l n) u huF a haF hua
    obtain ⟨v', ⟨hv', hv'w⟩, _⟩ := F.ancestor (l n + 1) (l (n + 1))
      (Nat.succ_le_of_lt (hl (Nat.lt_succ_self n))) w hwF
    have hav' : R a v' := T.ancestor_comparable (G.index n + 1)
      (F.index (l n + 1)) (F.index (l (n + 1))) hgap a v' w ha
      (F.nodes_subset (l n + 1) hv') (F.nodes_subset (l (n + 1)) hwF) haw hv'w
    have hvv' : v' = v := (hbuniq v' ⟨hv', hav'⟩).trans (hbuniq v ⟨hv, hav⟩).symm
    refine ⟨w, ⟨hw, hvv' ▸ hv'w⟩, ?_⟩
    intro z hz
    exact hwuniq z ⟨hz.1, T.rel_trans hav hz.2⟩

theorem relativeFinitePrefix_levels (n : ℕ) :
    (relativeFinitePrefix F G l hl h hsub).nodes n = G.nodes n := rfl

noncomputable def relativeFrameExtension (hh : 0 < h) : F.toTree.StrongFrame :=
  (relativeFinitePrefix F G l hl h hsub).extend hh

theorem relativeFrameExtension_initial (hh : 0 < h) (n : ℕ) (hn : n < h) :
    (relativeFrameExtension F G l hl h hsub hh).nodes n = G.nodes n :=
  FiniteStrongPrefix.extend_initial _ hh n hn

@[simp] theorem relativeFrameExtension_index (hh : 0 < h) :
    (relativeFrameExtension F G l hl h hsub hh).index = l := rfl

section Vector

variable {I : Type} {α : I → Type} [∀ i, DecidableEq (α i)]
    {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))
    (F : SynchronizedFrame T) {h : ℕ} (C : RealizedTreeCore T h)

/-- Every ambient strong finite core lying in F really is a strong finite
core of F. The selected level witness is not lost. -/
theorem realize_relative_core (hh : 0 < h) (hC : RelativeCore T F C) :
    ∃ D : RealizedTreeCore (fun i => (F.frames i).toTree) h, D.val = C.val := by
  classical
  obtain ⟨l, hl, hsub⟩ := hC
  let G := Classical.choose C.property
  have hG : G.core h = C.val := Classical.choose_spec C.property
  have hnodes : ∀ i n, n < h → (G.frames i).nodes n ⊆ (F.frames i).nodes (l n) := by
    intro i n hn
    have heq : (G.frames i).nodes n = C.val i ⟨n, hn⟩ :=
      congrFun (congrFun hG i) ⟨n, hn⟩
    rw [heq]
    exact hsub i ⟨n, hn⟩
  let H : SynchronizedFrame (fun i => (F.frames i).toTree) := {
    index := l
    index_strictMono := hl
    frames i := relativeFrameExtension (F.frames i) (G.frames i) l hl h (hnodes i) hh
    frame_index _ := rfl
  }
  refine ⟨H.realizedCore h, ?_⟩
  funext i n
  change (relativeFrameExtension (F.frames i) (G.frames i) l hl h (hnodes i) hh).nodes n.val =
    C.val i n
  rw [relativeFrameExtension_initial _ _ _ _ _ _ hh n.val n.isLt]
  exact congrFun (congrFun hG i) n

end Vector

end RelationalRamsey632.Milliken
