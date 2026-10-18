import RelationalRamsey632.Source.Successors
import Generic3Ramsey.SourceAbstractTrees

/-! The actual arbitrary-arity valuation coordinates instantiate the
finitely branching tree interface used by the Halpern--Läuchli proofs. -/

namespace RelationalRamsey632.Source

open Generic3Ramsey.SourceTrees

variable {A : ℕ → Type} [∀ j, Fintype (A j)] [∀ j, Nonempty (A j)]

noncomputable instance nodeDecidableEq (i : ℕ) : DecidableEq (Node A i) := Classical.decEq _

noncomputable def finiteNodeLevel (i n : ℕ) : Finset (Node A i) :=
  Finset.univ.image (fun p : Level A i n => (Node.mk n p : Node A i))

omit [∀ j, Nonempty (A j)] in
theorem mem_finiteNodeLevel (i n : ℕ) (t : Node A i) :
    t ∈ finiteNodeLevel i n ↔ t.height = n := by
  classical
  constructor
  · intro ht
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ht
    rfl
  · intro ht
    cases t with
    | mk m t =>
      dsimp only [Node.height] at ht
      subst m
      exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩

omit [∀ j, Fintype (A j)] in
theorem extend_level_table (i n m : ℕ) (hnm : n ≤ m) (p : Level A i n) :
    ∃ q : Level A i m, q.restrict hnm = p := by
  classical
  induction m, hnm using Nat.le_induction with
  | base => exact ⟨p, Level.restrict_refl p⟩
  | succ m hnm ih =>
    obtain ⟨q, hq⟩ := ih
    let a : A (i + 1) := Classical.choice inferInstance
    let v : Level A (i + 1) m := Classical.choice inferInstance
    refine ⟨Level.extend q a v, ?_⟩
    calc
      (Level.extend q a v).restrict (hnm.trans (Nat.le_succ m)) =
          ((Level.extend q a v).restrict (Nat.le_succ m)).restrict hnm := by
        simp only [Level.restrict_restrict]
      _ = p := by rw [Level.extend_restrict, hq]

noncomputable def coordinateTree (i : ℕ) : FiniteLevelTree (Node A i) Node.Prefix where
  nodes := finiteNodeLevel i
  root := Node.root i
  nodes_zero := by
    ext t
    rw [mem_finiteNodeLevel, Finset.mem_singleton]
    constructor
    · exact Node.height_zero_unique t
    · intro ht
      rw [ht]
      rfl
  rel_refl := Node.prefix_refl
  rel_trans := Node.prefix_trans
  rel_antisymm := Node.prefix_antisymm
  level_unique := by
    intro n m t hn hm
    exact ((mem_finiteNodeLevel i n t).mp hn).symm.trans ((mem_finiteNodeLevel i m t).mp hm)
  rel_level := by
    intro n m s t hs ht hst
    have hh := Node.prefix_height_le hst
    rw [(mem_finiteNodeLevel i n s).mp hs, (mem_finiteNodeLevel i m t).mp ht] at hh
    exact hh
  ancestor := by
    intro n m hnm t ht
    have htheight := (mem_finiteNodeLevel i m t).mp ht
    have hnt : n ≤ t.height := htheight ▸ hnm
    refine ⟨t.restrict n hnt, ⟨(mem_finiteNodeLevel i n _).mpr rfl, ⟨hnt, rfl⟩⟩, ?_⟩
    intro s hs
    have hsheight := (mem_finiteNodeLevel i n s).mp hs.1
    obtain ⟨_, hpre⟩ := hs.2
    simpa only [hsheight] using hpre.symm
  extend := by
    intro n m hnm t ht
    have htheight := (mem_finiteNodeLevel i n t).mp ht
    cases t with
    | mk k t =>
      dsimp only [Node.height] at htheight
      subst k
      obtain ⟨q, hq⟩ := extend_level_table i n m hnm t
      refine ⟨Node.mk m q, (mem_finiteNodeLevel i m _).mpr rfl, hnm, ?_⟩
      exact congrArg (fun p => (Node.mk n p : Node A i)) hq

end RelationalRamsey632.Source
