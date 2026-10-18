import Generic3Ramsey.SourceAbstractTrees
import Generic3Ramsey.SourceConeSelection
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Monotone.Basic

/-! Joint finite-frontier choices in the one-coordinate forest fusion.
The common level is selected from one free ultrafilter, so independently
chosen component colors cause no synchronization assumption. -/

namespace Generic3Ramsey.SourceTrees.FiniteLevelTree

open Filter

variable {α I K : Type} [DecidableEq α] [Fintype I] [Fintype K]
variable {R : α → α → Prop} (T : FiniteLevelTree α R)
variable (c : α → K) (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)

def GoodColor (k : K) (u : T.TreeNode) : Prop :=
  ∀ᶠ n in U, ∃ v, v ∈ T.nodes n ∧ R u.val v ∧ c v = k

omit [Fintype I] [Fintype K] in
theorem goodColor_ancestor (k : K) {u v : T.TreeNode}
    (huv : R u.val v.val) (hg : T.GoodColor c U k v) : T.GoodColor c U k u := by
  apply hg.mono
  rintro n ⟨w, hw, hvw, hk⟩
  exact ⟨w, hw, T.rel_trans huv hvw, hk⟩

omit [Fintype I] in
theorem exists_goodColor (hU : (U : Filter ℕ) ≤ atTop) (u : T.TreeNode) : ∃ k, T.GoodColor c U k u := by
  have hall : ∀ᶠ n in U, ∃ k, ∃ v, v ∈ T.nodes n ∧ R u.val v ∧ c v = k := by
    apply ((eventually_ge_atTop (T.nodeHeight u)).filter_mono hU).mono
    intro n hn
    obtain ⟨v, hv, huv⟩ := T.extend (T.nodeHeight u) n hn u.val (T.nodeHeight_mem u)
    exact ⟨c v, v, hv, huv, rfl⟩
  exact Ultrafilter.eventually_exists_iff.mp hall

omit [Fintype I] in
theorem dense_color_cone_above (hU : (U : Filter ℕ) ≤ atTop) (u : T.TreeNode) :
    ∃ v : T.TreeNode, R u.val v.val ∧ ∃ k,
      ∀ w : T.TreeNode, R v.val w.val → T.GoodColor c U k w :=
  finite_cone_selection (fun v w : T.TreeNode => R v.val w.val)
    (fun _ => T.rel_refl _) (fun h₁ h₂ => T.rel_trans h₁ h₂)
    (fun k v => T.GoodColor c U k v)
    (fun k _ _ hp hg => T.goodColor_ancestor c U k hp hg)
    (fun v => T.exists_goodColor c U hU v) u

structure ColorRoots where
  root : I → T.TreeNode
  color : I → K
  good : ∀ i (v : T.TreeNode), R (root i).val v.val → T.GoodColor c U (color i) v

omit [Fintype I] in
theorem colorRoots_above (hU : (U : Filter ℕ) ≤ atTop) (anchors : I → T.TreeNode) :
    ∃ D : T.ColorRoots (I := I) c U, ∀ i, R (anchors i).val (D.root i).val := by
  classical
  have hroots : ∀ i, ∃ v : T.TreeNode, R (anchors i).val v.val ∧ ∃ k,
      ∀ w : T.TreeNode, R v.val w.val → T.GoodColor c U k w :=
    fun i => T.dense_color_cone_above c U hU (anchors i)
  choose roots hanchors colors hgood using hroots
  exact ⟨⟨roots, colors, hgood⟩, hanchors⟩

namespace ColorRoots

omit [Fintype K]
variable {T c U} (D : T.ColorRoots (I := I) c U)

structure Stage where
  index : ℕ
  nodes : I → Finset T.TreeNode
  height : ∀ i u, u ∈ nodes i → T.nodeHeight u = index
  below_root : ∀ i u, u ∈ nodes i → R (D.root i).val u.val
  colored : ∀ i u, u ∈ nodes i → c u.val = D.color i
  nonempty : ∀ i, (nodes i).Nonempty

theorem initial_stage_exists (hU : (U : Filter ℕ) ≤ atTop) (lower : ℕ) :
    ∃ A : D.Stage, lower < A.index ∧ ∀ i, ∃ u, A.nodes i = {u} := by
  classical
  have hall : ∀ᶠ n in U, ∀ i : I,
      ∃ v, v ∈ T.nodes n ∧ R (D.root i).val v ∧ c v = D.color i := by
    exact Filter.eventually_all.mpr (fun i => D.good i (D.root i) (T.rel_refl _))
  obtain ⟨n, hn, hnodes⟩ := (((eventually_gt_atTop lower).filter_mono hU).and hall).exists
  choose f hfmem hfroot hfcolor using hnodes
  let roots : I → T.TreeNode := fun i => ⟨f i, n, hfmem i⟩
  refine ⟨⟨n, fun i => {roots i}, ?_, ?_, ?_, ?_⟩, hn, fun i => ⟨roots i, rfl⟩⟩
  · intro i u hu
    have heq : u = roots i := Finset.mem_singleton.mp hu
    subst u
    exact T.nodeHeight_eq (roots i) n (hfmem i)
  · intro i u hu
    have heq : u = roots i := Finset.mem_singleton.mp hu
    subst u
    exact hfroot i
  · intro i u hu
    have heq : u = roots i := Finset.mem_singleton.mp hu
    subst u
    exact hfcolor i
  · intro i
    exact ⟨roots i, Finset.mem_singleton_self _⟩

namespace Stage

variable {D}
variable (A : D.Stage)

omit [Fintype I] in
noncomputable def children (u : T.TreeNode) : Finset T.TreeNode := by
  classical
  exact (T.levelNodes (A.index + 1)).filter (fun v => R u.val v.val)

omit [Fintype I] in
theorem children_nonempty (i : I) (u : T.TreeNode) (hu : u ∈ A.nodes i) :
    (A.children u).Nonempty := by
  classical
  obtain ⟨v, hv, huv⟩ := T.extend A.index (A.index + 1) (Nat.le_succ _) u.val
    (by rw [← A.height i u hu]; exact T.nodeHeight_mem u)
  let v' : T.TreeNode := ⟨v, A.index + 1, hv⟩
  exact ⟨v', Finset.mem_filter.mpr ⟨(T.mem_levelNodes _ _).mpr hv, huv⟩⟩

structure Next (B : D.Stage) : Prop where
  index_lt : A.index < B.index
  parent : ∀ i w, w ∈ B.nodes i → ∃ u ∈ A.nodes i, ∃ v ∈ A.children u, R v.val w.val
  successor : ∀ i u, u ∈ A.nodes i → ∀ v ∈ A.children u,
    ∃! w : T.TreeNode, w ∈ B.nodes i ∧ R v.val w.val

theorem next_exists (hU : (U : Filter ℕ) ≤ atTop) : ∃ B : D.Stage, A.Next B := by
  classical
  have hcone : ∀ i (u : {u // u ∈ A.nodes i}) (v : {v // v ∈ A.children u.val}),
      ∀ᶠ n in U, ∃ w, w ∈ T.nodes n ∧ R v.val.val w ∧ c w = D.color i := by
    intro i u v
    exact D.good i v.val (T.rel_trans (A.below_root i u.val u.property)
      (Finset.mem_filter.mp v.property).2)
  have hall : ∀ᶠ n in U, ∀ i (u : {u // u ∈ A.nodes i}) (v : {v // v ∈ A.children u.val}),
      ∃ w, w ∈ T.nodes n ∧ R v.val.val w ∧ c w = D.color i := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro u
    exact Filter.eventually_all.mpr (hcone i u)
  obtain ⟨n, hn, hnodes⟩ := (((eventually_gt_atTop A.index).filter_mono hU).and hall).exists
  choose f hfmem hfcone hfcolor using hnodes
  let value := fun i (u : {u // u ∈ A.nodes i}) (v : {v // v ∈ A.children u.val}) =>
    (⟨f i u v, n, hfmem i u v⟩ : T.TreeNode)
  let nodes := fun i => (A.nodes i).attach.biUnion fun u =>
    (A.children u.val).attach.image (value i u)
  have hmem : ∀ i w, w ∈ nodes i →
      ∃ (u : {u // u ∈ A.nodes i}) (v : {v // v ∈ A.children u.val}), value i u v = w := by
    intro i w hw
    obtain ⟨u, _, hw⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨v, _, hvalue⟩ := Finset.mem_image.mp hw
    exact ⟨u, v, hvalue⟩
  have hvalue_mem : ∀ i u v, value i u v ∈ nodes i := by
    intro i u v
    exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_attach _ _,
      Finset.mem_image.mpr ⟨v, Finset.mem_attach _ _, rfl⟩⟩
  let B : D.Stage :=
    ⟨n, nodes, by
      intro i w hw
      obtain ⟨u, v, rfl⟩ := hmem i w hw
      exact T.nodeHeight_eq _ n (hfmem i u v), by
      intro i w hw
      obtain ⟨u, v, rfl⟩ := hmem i w hw
      exact T.rel_trans (T.rel_trans (A.below_root i u.val u.property)
        (Finset.mem_filter.mp v.property).2) (hfcone i u v), by
      intro i w hw
      obtain ⟨u, v, rfl⟩ := hmem i w hw
      exact hfcolor i u v, by
      intro i
      obtain ⟨u, hu⟩ := A.nonempty i
      obtain ⟨v, hv⟩ := A.children_nonempty i u hu
      exact ⟨value i ⟨u, hu⟩ ⟨v, hv⟩, hvalue_mem i ⟨u, hu⟩ ⟨v, hv⟩⟩⟩
  refine ⟨B, hn, ?_, ?_⟩
  · intro i w hw
    obtain ⟨u, v, rfl⟩ := hmem i w hw
    exact ⟨u.val, u.property, v.val, v.property, hfcone i u v⟩
  · intro i u hu v hv
    let u' : {u // u ∈ A.nodes i} := ⟨u, hu⟩
    let v' : {v // v ∈ A.children u} := ⟨v, hv⟩
    refine ⟨value i u' v', ⟨hvalue_mem i u' v', hfcone i u' v'⟩, ?_⟩
    intro w hw
    obtain ⟨p, q, hvalue⟩ := hmem i w hw.1
    have hqw : R q.val.val w.val := hvalue ▸ hfcone i p q
    have hpu : p.val = u := by
      apply Subtype.ext
      apply T.node_eq_of_common_extension A.index n _ _ w.val
      · rw [← A.height i p.val p.property]
        exact T.nodeHeight_mem p.val
      · rw [← A.height i u hu]
        exact T.nodeHeight_mem u
      · exact hw.1 |> fun h => by
          obtain ⟨p₀, q₀, he⟩ := hmem i w h
          exact he ▸ hfmem i p₀ q₀
      · exact T.rel_trans (Finset.mem_filter.mp q.property).2 hqw
      · exact T.rel_trans (Finset.mem_filter.mp hv).2 hw.2
    have hp : p = u' := Subtype.ext hpu
    subst p
    have hqv : q.val = v := by
      apply Subtype.ext
      apply T.node_eq_of_common_extension (A.index + 1) n _ _ w.val
      · exact (T.mem_levelNodes _ _).mp (Finset.mem_filter.mp q.property).1
      · exact (T.mem_levelNodes _ _).mp (Finset.mem_filter.mp hv).1
      · exact hvalue ▸ hfmem i u' q
      · exact hqw
      · exact hw.2
    have hq : q = v' := Subtype.ext hqv
    subst q
    exact hvalue.symm

noncomputable def next (hU : (U : Filter ℕ) ≤ atTop) : D.Stage := Classical.choose (A.next_exists hU)

theorem next_spec (hU : (U : Filter ℕ) ≤ atTop) : A.Next (A.next hU) := Classical.choose_spec (A.next_exists hU)

end Stage

noncomputable def stages (initial : D.Stage) (hU : (U : Filter ℕ) ≤ atTop) : ℕ → D.Stage
  | 0 => initial
  | n + 1 => (stages initial hU n).next hU

theorem stages_index_strictMono (initial : D.Stage) (hU : (U : Filter ℕ) ≤ atTop) :
    StrictMono (fun n => (D.stages initial hU n).index) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact ((D.stages initial hU n).next_spec hU).index_lt

theorem stages_parent (initial : D.Stage) (hU : (U : Filter ℕ) ≤ atTop)
    (n : ℕ) (i : I) (w : T.TreeNode) (hw : w ∈ (D.stages initial hU (n + 1)).nodes i) :
    ∃ u ∈ (D.stages initial hU n).nodes i,
      ∃ v ∈ (D.stages initial hU n).children u, R v.val w.val :=
  ((D.stages initial hU n).next_spec hU).parent i w hw

theorem stages_successor (initial : D.Stage) (hU : (U : Filter ℕ) ≤ atTop)
    (n : ℕ) (i : I) (u : T.TreeNode) (hu : u ∈ (D.stages initial hU n).nodes i)
    (v : T.TreeNode) (hv : v ∈ (D.stages initial hU n).children u) :
    ∃! w : T.TreeNode, w ∈ (D.stages initial hU (n + 1)).nodes i ∧ R v.val w.val :=
  ((D.stages initial hU n).next_spec hU).successor i u hu v hv

end ColorRoots

end Generic3Ramsey.SourceTrees.FiniteLevelTree
