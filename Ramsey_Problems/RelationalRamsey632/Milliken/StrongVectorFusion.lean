import RelationalRamsey632.Milliken.FixedColorDensity

/-! Rectangular frontier fusion. Dense level matrices, with a single fixed
color, construct actual strong frames on one common infinite level set. -/

namespace RelationalRamsey632.Milliken

open Generic3Ramsey.SourceTrees
open Generic3Ramsey.SourceTrees.FiniteLevelTree

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    {α : I → Type} [∀ i, DecidableEq (α i)]
    {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))
    {K : Type} (roots : VectorNode T) (color : K) (c : VectorNode T → K)

structure VectorColorStage where
  index : ℕ
  nodes : ∀ i, Finset (T i).TreeNode
  height : ∀ i u, u ∈ nodes i → (T i).nodeHeight u = index
  below_root : ∀ i u, u ∈ nodes i → R i (roots i).val u.val
  colored : ∀ x ∈ Fintype.piFinset nodes, c x = color
  nonempty : ∀ i, (nodes i).Nonempty

omit [Nonempty I] in
theorem initial_color_stage (d : ℕ)
    (hr : ∀ i, (T i).nodeHeight (roots i) = d)
    (hD : ∀ k, FixedColorLevelMatrix T roots k color c) :
    ∃ A : VectorColorStage T roots color c, ∀ i, ∃ u, A.nodes i = {u} := by
  classical
  obtain ⟨N, columns, hheight, hdense, hcolored⟩ := hD (d + 1)
  have hchoose : ∀ i, ∃ u ∈ columns i, R i (roots i).val u.val := by
    intro i
    obtain ⟨v, hv, hrv⟩ := (T i).extend d (d + 1) (Nat.le_succ _)
      (roots i).val (hr i ▸ (T i).nodeHeight_mem (roots i))
    obtain ⟨u, hu, hvu⟩ := hdense i v hv hrv
    exact ⟨u, hu, (T i).rel_trans hrv hvu⟩
  choose f hfmem hfroot using hchoose
  let A : VectorColorStage T roots color c := {
    index := N
    nodes := fun i => {f i}
    height := fun i u hu => (Finset.mem_singleton.mp hu) ▸ hheight i (f i) (hfmem i)
    below_root := fun i u hu => (Finset.mem_singleton.mp hu) ▸ hfroot i
    colored := by
      intro x hx
      apply hcolored
      apply Fintype.mem_piFinset.mpr
      intro i
      have hh := Finset.mem_singleton.mp (Fintype.mem_piFinset.mp hx i)
      exact hh ▸ hfmem i
    nonempty := fun i => Finset.singleton_nonempty (f i) }
  exact ⟨A, fun i => ⟨f i, rfl⟩⟩

namespace VectorColorStage

variable {T roots color c} (A : VectorColorStage T roots color c)

noncomputable def children (i : I) (u : (T i).TreeNode) : Finset (T i).TreeNode := by
  classical
  exact ((T i).levelNodes (A.index + 1)).filter (fun v => R i u.val v.val)

omit [Nonempty I] in
theorem children_nonempty (i : I) (u : (T i).TreeNode) (hu : u ∈ A.nodes i) :
    (A.children i u).Nonempty := by
  classical
  obtain ⟨v, hv, huv⟩ := (T i).extend A.index (A.index + 1) (Nat.le_succ _) u.val
    (A.height i u hu ▸ (T i).nodeHeight_mem u)
  let v' : (T i).TreeNode := ⟨v, A.index + 1, hv⟩
  exact ⟨v', Finset.mem_filter.mpr ⟨((T i).mem_levelNodes _ _).mpr hv, huv⟩⟩

structure Next (B : VectorColorStage T roots color c) : Prop where
  index_lt : A.index < B.index
  parent : ∀ i w, w ∈ B.nodes i →
    ∃ u ∈ A.nodes i, ∃ v ∈ A.children i u, R i v.val w.val
  successor : ∀ i u, u ∈ A.nodes i → ∀ v ∈ A.children i u,
    ∃! w : (T i).TreeNode, w ∈ B.nodes i ∧ R i v.val w.val

theorem next_exists (hD : ∀ k, FixedColorLevelMatrix T roots k color c) :
    ∃ B : VectorColorStage T roots color c, A.Next B := by
  classical
  obtain ⟨N, columns, hheight, hdense, hcolor⟩ := hD (A.index + 1)
  have hchoose : ∀ i (u : {u // u ∈ A.nodes i}) (v : {v // v ∈ A.children i u.val}),
      ∃ w ∈ columns i, R i v.val.val w.val := by
    intro i u v
    exact hdense i v.val.val
      (((T i).mem_levelNodes _ _).mp (Finset.mem_filter.mp v.property).1)
      ((T i).rel_trans (A.below_root i u.val u.property) (Finset.mem_filter.mp v.property).2)
  choose f hfmem hfcone using hchoose
  let nodes := fun i => (A.nodes i).attach.biUnion fun u =>
    (A.children i u.val).attach.image (f i u)
  have hmem : ∀ i w, w ∈ nodes i →
      ∃ (u : {u // u ∈ A.nodes i}) (v : {v // v ∈ A.children i u.val}), f i u v = w := by
    intro i w hw
    obtain ⟨u, _, hw⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨v, _, heq⟩ := Finset.mem_image.mp hw
    exact ⟨u, v, heq⟩
  have hvalue_mem : ∀ i u v, f i u v ∈ nodes i := by
    intro i u v
    exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_attach _ _,
      Finset.mem_image.mpr ⟨v, Finset.mem_attach _ _, rfl⟩⟩
  have hlt : A.index < N := by
    let i : I := Classical.choice inferInstance
    obtain ⟨u, hu⟩ := A.nonempty i
    obtain ⟨v, hv⟩ := A.children_nonempty i u hu
    let u' : {u // u ∈ A.nodes i} := ⟨u, hu⟩
    let v' : {v // v ∈ A.children i u} := ⟨v, hv⟩
    have hle := (T i).rel_level (A.index + 1) N v.val (f i u' v').val
      (((T i).mem_levelNodes _ _).mp (Finset.mem_filter.mp hv).1)
      (hheight i (f i u' v') (hfmem i u' v') ▸ (T i).nodeHeight_mem (f i u' v'))
      (hfcone i u' v')
    omega
  let B : VectorColorStage T roots color c := {
    index := N
    nodes := nodes
    height := by
      intro i w hw
      obtain ⟨u, v, rfl⟩ := hmem i w hw
      exact hheight i _ (hfmem i u v)
    below_root := by
      intro i w hw
      obtain ⟨u, v, rfl⟩ := hmem i w hw
      exact (T i).rel_trans (A.below_root i u.val u.property)
        ((T i).rel_trans (Finset.mem_filter.mp v.property).2 (hfcone i u v))
    colored := by
      intro x hx
      apply hcolor
      apply Fintype.mem_piFinset.mpr
      intro i
      obtain ⟨u, v, heq⟩ := hmem i (x i) (Fintype.mem_piFinset.mp hx i)
      exact heq ▸ hfmem i u v
    nonempty := by
      intro i
      obtain ⟨u, hu⟩ := A.nonempty i
      obtain ⟨v, hv⟩ := A.children_nonempty i u hu
      exact ⟨f i ⟨u, hu⟩ ⟨v, hv⟩, hvalue_mem i ⟨u, hu⟩ ⟨v, hv⟩⟩ }
  refine ⟨B, hlt, ?_, ?_⟩
  · intro i w hw
    obtain ⟨u, v, rfl⟩ := hmem i w hw
    exact ⟨u.val, u.property, v.val, v.property, hfcone i u v⟩
  · intro i u hu v hv
    let u' : {u // u ∈ A.nodes i} := ⟨u, hu⟩
    let v' : {v // v ∈ A.children i u} := ⟨v, hv⟩
    refine ⟨f i u' v', ⟨hvalue_mem i u' v', hfcone i u' v'⟩, ?_⟩
    intro w hw
    obtain ⟨p, q, hvalue⟩ := hmem i w hw.1
    have hqw : R i q.val.val w.val := hvalue ▸ hfcone i p q
    have hpu : p.val = u := by
      apply Subtype.ext
      apply (T i).node_eq_of_common_extension A.index N _ _ w.val
      · exact A.height i p.val p.property ▸ (T i).nodeHeight_mem p.val
      · exact A.height i u hu ▸ (T i).nodeHeight_mem u
      · exact hvalue ▸ (hheight i _ (hfmem i p q) ▸ (T i).nodeHeight_mem (f i p q))
      · exact (T i).rel_trans (Finset.mem_filter.mp q.property).2 hqw
      · exact (T i).rel_trans (Finset.mem_filter.mp hv).2 hw.2
    have hp : p = u' := Subtype.ext hpu
    subst p
    have hqv : q.val = v := by
      apply Subtype.ext
      apply (T i).node_eq_of_common_extension (A.index + 1) N _ _ w.val
      · exact ((T i).mem_levelNodes _ _).mp (Finset.mem_filter.mp q.property).1
      · exact ((T i).mem_levelNodes _ _).mp (Finset.mem_filter.mp hv).1
      · exact hvalue ▸ (hheight i _ (hfmem i u' q) ▸ (T i).nodeHeight_mem (f i u' q))
      · exact hqw
      · exact hw.2
    have hq : q = v' := Subtype.ext hqv
    subst q
    exact hvalue.symm

noncomputable def next (hD : ∀ k, FixedColorLevelMatrix T roots k color c) :
    VectorColorStage T roots color c := Classical.choose (A.next_exists hD)

theorem next_spec (hD : ∀ k, FixedColorLevelMatrix T roots k color c) :
    A.Next (A.next hD) := Classical.choose_spec (A.next_exists hD)

end VectorColorStage

noncomputable def colorStages (initial : VectorColorStage T roots color c)
    (hD : ∀ k, FixedColorLevelMatrix T roots k color c) : ℕ → VectorColorStage T roots color c
  | 0 => initial
  | n + 1 => (colorStages initial hD n).next hD

theorem strong_vector_from_fixed_density
    (d : ℕ) (hr : ∀ i, (T i).nodeHeight (roots i) = d)
    (hD : ∀ k, FixedColorLevelMatrix T roots k color c) :
    Nonempty (HomogeneousStrongVector T c) := by
  classical
  obtain ⟨initial, hinit⟩ := initial_color_stage T roots color c d hr hD
  choose initialRoots hrootsets using hinit
  let stages := colorStages T roots color c initial hD
  have hstrict : StrictMono (fun n => (stages n).index) := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact ((stages n).next_spec hD).index_lt
  let frames : ∀ i, (T i).StrongFrame := fun i => {
    index := fun n => (stages n).index
    index_strictMono := hstrict
    nodes := fun n => ((stages n).nodes i).image Subtype.val
    root := (initialRoots i).val
    nodes_zero := by
      change (initial.nodes i).image (Subtype.val : (T i).TreeNode → α i) = {(initialRoots i).val}
      rw [hrootsets i]
      exact Finset.image_singleton (Subtype.val : (T i).TreeNode → α i) (initialRoots i)
    nodes_subset := by
      intro n u hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact (stages n).height i v hv ▸ (T i).nodeHeight_mem v
    parent := by
      intro n w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨u, hu, q, hq, hqv⟩ := ((stages n).next_spec hD).parent i v hv
      exact ⟨u.val, Finset.mem_image.mpr ⟨u, hu, rfl⟩,
        (T i).rel_trans (Finset.mem_filter.mp hq).2 hqv⟩
    successor := by
      intro n u hu v hv huv
      obtain ⟨p, hp, hpu⟩ := Finset.mem_image.mp hu
      let v' : (T i).TreeNode := ⟨v, (stages n).index + 1, hv⟩
      have hv' : v' ∈ (stages n).children i p :=
        Finset.mem_filter.mpr ⟨((T i).mem_levelNodes _ _).mpr hv, hpu.symm ▸ huv⟩
      obtain ⟨w, hw, huniq⟩ := ((stages n).next_spec hD).successor i p hp v' hv'
      refine ⟨w.val, ⟨Finset.mem_image.mpr ⟨w, hw.1, rfl⟩, hw.2⟩, ?_⟩
      intro q hq
      obtain ⟨q', hq', heq⟩ := Finset.mem_image.mp hq.1
      have hqq' : R i v'.val q'.val := heq.symm ▸ hq.2
      exact heq.symm.trans (congrArg Subtype.val (huniq q' ⟨hq', hqq'⟩)) }
  refine ⟨⟨(fun n => (stages n).index), hstrict, frames, (fun _ => rfl), color, ?_⟩⟩
  intro n x hx
  apply (stages n).colored x
  apply Fintype.mem_piFinset.mpr
  intro i
  obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp (hx i)
  have hu' : u = x i := Subtype.ext heq
  exact hu' ▸ hu

theorem strong_vector_from_dense_sets [Fintype K]
    (d : ℕ) (hr : ∀ i, (T i).nodeHeight (roots i) = d)
    (hD : ∀ k, LevelMatrixColor T roots k c) : Nonempty (HomogeneousStrongVector T c) := by
  obtain ⟨color, hcolor⟩ := fixed_color_dense_sets T c d roots hr hD
  exact strong_vector_from_fixed_density T roots color c d hr hcolor

noncomputable def frameLevelNodes (i : I) (F : (T i).StrongFrame) (n : ℕ) :
    Finset (T i).TreeNode := by
  classical
  exact (F.nodes n).attach.image (fun u =>
    (⟨u.val, F.index n, F.nodes_subset n u.property⟩ : (T i).TreeNode))

omit [Nonempty I] in
/-- The strong-subtree theorem yields a genuine Cartesian somewhere-dense
matrix, rather than a merely dense subset of a product tree. -/
theorem mixed_from_strong (hSS : StrongSubtreeRamsey T K) : MixedSDHL T K := by
  classical
  intro c
  obtain ⟨S⟩ := hSS c
  let roots : VectorNode T := fun i =>
    ⟨(S.frames i).root, (S.frames i).index 0,
      (S.frames i).nodes_subset 0 (by rw [(S.frames i).nodes_zero]; simp)⟩
  let columns := fun i => frameLevelNodes T i (S.frames i) 1
  have hrootheight : ∀ i, (T i).nodeHeight (roots i) = S.index 0 := by
    intro i
    have hmem : (S.frames i).root ∈ (S.frames i).nodes 0 := by
      rw [(S.frames i).nodes_zero]
      exact Finset.mem_singleton_self _
    have hh := (T i).nodeHeight_eq (roots i) ((S.frames i).index 0)
      ((S.frames i).nodes_subset 0 hmem)
    exact hh.trans (congrFun (S.frame_index i) 0)
  have hdense : ∀ i, (T i).DenseAbove (roots i) (S.index 0 + 1) (columns i) := by
    intro i v hv hrv
    have hv' : v ∈ (T i).nodes ((S.frames i).index 0 + 1) := by
      rw [S.frame_index i]
      exact hv
    obtain ⟨w, hw, _⟩ := (S.frames i).successor 0 (S.frames i).root
      (by rw [(S.frames i).nodes_zero]; simp) v hv' hrv
    let w' : (T i).TreeNode := ⟨w, (S.frames i).index 1, (S.frames i).nodes_subset 1 hw.1⟩
    exact ⟨w', Finset.mem_image.mpr ⟨⟨w, hw.1⟩, Finset.mem_attach _ _, rfl⟩, hw.2⟩
  let D : VectorMatrix T := ⟨S.index 0, roots, hrootheight, columns, hdense⟩
  have hconstant : ∀ x ∈ D.support, c x = S.color := by
    intro x hx
    apply S.colored 1 x
    intro i
    have hi := Fintype.mem_piFinset.mp hx i
    obtain ⟨u, _, heq⟩ := Finset.mem_image.mp hi
    exact (congrArg Subtype.val heq) ▸ u.property
  exact ⟨D, fun x hx y hy => (hconstant x hx).trans (hconstant y hy).symm⟩

end RelationalRamsey632.Milliken
