import RelationalRamsey632.Milliken.StrongVectorFusion
import RelationalRamsey632.Milliken.BranchColorDensity

namespace RelationalRamsey632.Milliken

open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    {α : I → Type} [∀ i, DecidableEq (α i)]
    {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))
    {β : Type} [DecidableEq β] {Q : β → β → Prop} (B : FiniteLevelTree β Q)

noncomputable def vectorHeight (x : VectorNode T) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => (T i).nodeHeight (x i))

omit [DecidableEq I] in
theorem vectorHeight_eq (x : VectorNode T) (n : ℕ)
    (hx : ∀ i, (T i).nodeHeight (x i) = n) : vectorHeight T x = n := by
  unfold vectorHeight
  simp_rw [hx]
  simp

def branchNode (b : Branch B) (n : ℕ) : B.TreeNode := ⟨(b.node n).val, n, (b.node n).property⟩

theorem branchNode_height (b : Branch B) (n : ℕ) : B.nodeHeight (branchNode B b n) = n :=
  B.nodeHeight_eq _ n (b.node n).property

def StableVectorSections {K : Type} (c : VectorNode T → B.TreeNode → K) : Prop :=
  ∀ n m (x y : VectorNode T) (z : B.TreeNode),
    (∀ i, (T i).nodeHeight (x i) = n) →
    (∀ i, (T i).nodeHeight (y i) = m) → n ≤ m →
    (∀ i, R i (x i).val (y i).val) → B.nodeHeight z < n → c x z = c y z

noncomputable def branchColor {K : Type} (c : VectorNode T → B.TreeNode → K)
    (b : Branch B) (x : VectorNode T) : K :=
  c x (branchNode B b (vectorHeight T x - 1))

omit [Nonempty I] in
/-- Coordinatewise refinement keeps a genuine Cartesian product, while
each new tuple extends some tuple of the old product. -/
theorem refine_vector_columns (roots : VectorNode T) (k L : ℕ)
    (old fresh : ∀ i, Finset (T i).TreeNode)
    (hold : ∀ i, (T i).DenseAbove (roots i) k (old i))
    (hbelow : ∀ i u, u ∈ old i → R i (roots i).val u.val)
    (hbound : ∀ i u, u ∈ old i → (T i).nodeHeight u ≤ L)
    (hfresh : ∀ i, (T i).DenseAbove (roots i) L (fresh i)) :
    ∃ columns : ∀ i, Finset (T i).TreeNode,
      (∀ i, columns i ⊆ fresh i) ∧
      (∀ i, (T i).DenseAbove (roots i) k (columns i)) ∧
      (∀ i u, u ∈ columns i → R i (roots i).val u.val) ∧
      ∀ x ∈ Fintype.piFinset columns,
        ∃ y ∈ Fintype.piFinset old, ∀ i, R i (y i).val (x i).val := by
  classical
  have hex : ∀ i, ∃ D : Finset (T i).TreeNode,
      D ⊆ fresh i ∧ (T i).DenseAbove (roots i) k D ∧
      (∀ u ∈ D, R i (roots i).val u.val) ∧
      ∀ v ∈ D, ∃ u ∈ old i, R i u.val v.val :=
    fun i => (T i).refine_dense_family (roots i) k L (old i) (fresh i)
      (hold i) (hbelow i) (hbound i) (hfresh i)
  choose columns hsub hdense hroots hparents using hex
  refine ⟨columns, hsub, hdense, hroots, ?_⟩
  intro x hx
  have hparent : ∀ i, ∃ u ∈ old i, R i u.val (x i).val :=
    fun i => hparents i (x i) (Fintype.mem_piFinset.mp hx i)
  choose y hymem hyrel using hparent
  exact ⟨y, Fintype.mem_piFinset.mpr hymem, hyrel⟩

theorem branch_dense_frontier {K : Type}
    (c : VectorNode T → B.TreeNode → K) (hst : StableVectorSections T B c)
    (d : ℕ) (roots : VectorNode T) (hr : ∀ i, (T i).nodeHeight (roots i) = d)
    (k : ℕ) (hdk : d ≤ k) (color : K) (F : Finset B.TreeNode)
    (hbranches : ∀ v ∈ F, ∃ b : Branch B, b.Through v ∧
      ∀ L, FixedColorLevelMatrix T roots L color (branchColor T B c b)) :
    ∃ N, ∃ columns : ∀ i, Finset (T i).TreeNode, ∃ last : Finset B.TreeNode,
      (∀ i u, u ∈ columns i → (T i).nodeHeight u = N) ∧
      (∀ i, (T i).DenseAbove (roots i) k (columns i)) ∧
      (∀ i u, u ∈ columns i → R i (roots i).val u.val) ∧
      (∀ v ∈ F, ∃ y ∈ last, Q v.val y.val) ∧
      (∀ y ∈ last, B.nodeHeight y < N) ∧
      ∀ x ∈ Fintype.piFinset columns, ∀ y ∈ last, c x y = color := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    let columns := fun i => ((T i).levelNodes k).filter (fun u => R i (roots i).val u.val)
    refine ⟨k, columns, ∅, ?_, ?_, ?_, by simp, by simp, by simp⟩
    · intro i u hu
      exact (T i).nodeHeight_levelNodes k u (Finset.mem_filter.mp hu).1
    · intro i u hu hru
      let u' : (T i).TreeNode := ⟨u, k, hu⟩
      exact ⟨u', Finset.mem_filter.mpr ⟨((T i).mem_levelNodes _ _).mpr hu, hru⟩, (T i).rel_refl u⟩
    · intro i u hu
      exact (Finset.mem_filter.mp hu).2
  | @insert v F _ ih =>
    obtain ⟨Nold, old, last, holdheight, holddense, holdbelow, hcover, hlastheight, holdcolor⟩ :=
      ih (fun u hu => hbranches u (Finset.mem_insert_of_mem hu))
    obtain ⟨b, hb, hDS⟩ := hbranches v (Finset.mem_insert_self v F)
    let L := max (Nold + 1) (max (B.nodeHeight v + 1) k)
    have hNL : Nold < L := (Nat.lt_succ_self _).trans_le (Nat.le_max_left _ _)
    have hvL : B.nodeHeight v + 1 ≤ L := (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
    have hkL : k ≤ L := (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
    obtain ⟨N, fresh, hfheight, hfdense, hfcolor⟩ := hDS L
    have hLN : L ≤ N := by
      let i : I := Classical.choice inferInstance
      obtain ⟨u, hu, hru⟩ := (T i).extend d L (hdk.trans hkL)
        (roots i).val (hr i ▸ (T i).nodeHeight_mem (roots i))
      obtain ⟨w, hw, huw⟩ := hfdense i u hu hru
      exact (T i).rel_level L N u w.val hu (hfheight i w hw ▸ (T i).nodeHeight_mem w) huw
    have holdbound : ∀ i u, u ∈ old i → (T i).nodeHeight u ≤ L :=
      fun i u hu => (holdheight i u hu).le.trans hNL.le
    obtain ⟨columns, hsub, hdense, hbelow, hparents⟩ :=
      refine_vector_columns T roots k L old fresh holddense holdbelow holdbound hfdense
    let y := branchNode B b (N - 1)
    have hyheight : B.nodeHeight y = N - 1 := branchNode_height B b (N - 1)
    have hNpos : 0 < N := (Nat.zero_lt_succ Nold).trans_le ((Nat.le_max_left _ _).trans hLN)
    have hvy : Q v.val y.val := by
      have hvn : B.nodeHeight v ≤ N - 1 := by omega
      exact hb ▸ b.coherent (B.nodeHeight v) (N - 1) hvn
    have hcolumnsheight : ∀ i u, u ∈ columns i → (T i).nodeHeight u = N :=
      fun i u hu => hfheight i u (hsub i hu)
    refine ⟨N, columns, insert y last, hcolumnsheight, hdense, hbelow, ?_, ?_, ?_⟩
    · intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact ⟨y, Finset.mem_insert_self _ _, hvy⟩
      · obtain ⟨z, hz, huz⟩ := hcover u hu
        exact ⟨z, Finset.mem_insert_of_mem hz, huz⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · rw [hyheight]
        omega
      · exact (hlastheight z hz).trans_le (hNL.le.trans hLN)
    · intro x hx z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · have hxFresh : x ∈ Fintype.piFinset fresh :=
          Fintype.mem_piFinset.mpr (fun i => hsub i (Fintype.mem_piFinset.mp hx i))
        have hh := hfcolor x hxFresh
        unfold branchColor at hh
        rw [vectorHeight_eq T x N (fun i => hcolumnsheight i (x i) (Fintype.mem_piFinset.mp hx i))] at hh
        exact hh
      · obtain ⟨xold, hxold, hrel⟩ := hparents x hx
        have hh := hst Nold N xold x z
          (fun i => holdheight i (xold i) (Fintype.mem_piFinset.mp hxold i))
          (fun i => hcolumnsheight i (x i) (Fintype.mem_piFinset.mp hx i))
          (hNL.le.trans hLN) hrel (hlastheight z hz)
        exact hh.symm.trans (holdcolor xold hxold z hz)

/-- The induction hypothesis SS_d on the same d actual coordinate carriers
supplies the branch color's all-threshold dense matrices. -/
theorem branch_dense_cone_from_ss {K : Type} [Fintype K]
    (hSS : ∀ S : ∀ i, FiniteLevelTree (α i) (R i), StrongSubtreeRamsey S K)
    (c : VectorNode T → B.TreeNode → K) :
    ∃ t : B.TreeNode, ∃ d, ∃ roots : VectorNode T,
      (∀ i, (T i).nodeHeight (roots i) = d) ∧
      ∃ color : K, ∀ v : B.TreeNode, Q t.val v.val →
        ∃ b : Branch B, b.Through v ∧
          ∀ L, FixedColorLevelMatrix T roots L color (branchColor T B c b) := by
  classical
  have hbranch : ∀ b : Branch B, ∃ d, ∃ roots : VectorNode T,
      (∀ i, (T i).nodeHeight (roots i) = d) ∧
      ∃ color : K, ∀ L, FixedColorLevelMatrix T roots L color (branchColor T B c b) := by
    intro b
    obtain ⟨d, roots, hr, hD⟩ := dense_sets_from_restricted_mixed T
      (fun index hm hz => mixed_from_strong (fun i => (T i).restrictLevels index hm hz)
        (hSS (fun i => (T i).restrictLevels index hm hz))) (branchColor T B c b)
    obtain ⟨color, hcolor⟩ := fixed_color_dense_sets T (branchColor T B c b) d roots hr hD
    exact ⟨d, roots, hr, color, hcolor⟩
  choose depths branchRoots hroots branchColors hmat using hbranch
  let code := fun b : Branch B => (branchRoots b, branchColors b)
  obtain ⟨t, q, ht⟩ := branch_color_dense B code
  obtain ⟨b0, _, hb0⟩ := ht t (B.rel_refl _)
  have hr0 : branchRoots b0 = q.1 := congrArg Prod.fst hb0
  refine ⟨t, depths b0, q.1, ?_, q.2, ?_⟩
  · intro i
    rw [← hr0]
    exact hroots b0 i
  · intro v hv
    obtain ⟨b, hb, hcode⟩ := ht v hv
    refine ⟨b, hb, ?_⟩
    have hrb : branchRoots b = q.1 := congrArg Prod.fst hcode
    have hcb : branchColors b = q.2 := congrArg Prod.snd hcode
    intro L
    have hh := hmat b L
    rw [hrb, hcb] at hh
    exact hh

/-- The final finite-frontier step of the dimension induction. First and
last roots may be prescribed at different index heights, so a surrounding
strong-frame transport can align their original ambient heights exactly. -/
theorem stable_dimension_matrix {K : Type} [Fintype K]
    (hSS : ∀ S : ∀ i, FiniteLevelTree (α i) (R i), StrongSubtreeRamsey S K)
    (c : VectorNode T → B.TreeNode → K) (hst : StableVectorSections T B c) :
    ∃ d, ∃ roots : VectorNode T, ∃ t : B.TreeNode,
      (∀ i, (T i).nodeHeight (roots i) = d) ∧
      ∀ D E, d ≤ D → B.nodeHeight t ≤ E →
        ∃ firstRoots : VectorNode T, ∃ lastRoot : B.TreeNode,
          ∃ columns : ∀ i, Finset (T i).TreeNode, ∃ last : Finset B.TreeNode, ∃ color : K,
            (∀ i, (T i).nodeHeight (firstRoots i) = D) ∧ B.nodeHeight lastRoot = E ∧
            (∀ i, (T i).DenseAbove (firstRoots i) (D + 1) (columns i)) ∧
            B.DenseAbove lastRoot (E + 1) last ∧
            ∀ x ∈ Fintype.piFinset columns, ∀ y ∈ last, c x y = color := by
  classical
  obtain ⟨t, d, roots, hr, color, hbranches⟩ := branch_dense_cone_from_ss T B hSS c
  refine ⟨d, roots, t, hr, ?_⟩
  intro D E hDd htE
  have hfirst : ∀ i, ∃ u, u ∈ (T i).nodes D ∧ R i (roots i).val u :=
    fun i => (T i).extend d D hDd (roots i).val (hr i ▸ (T i).nodeHeight_mem (roots i))
  choose f hfmem hfrel using hfirst
  let firstRoots : VectorNode T := fun i => ⟨f i, D, hfmem i⟩
  obtain ⟨s, hs, hts⟩ := B.extend (B.nodeHeight t) E htE t.val (B.nodeHeight_mem t)
  let lastRoot : B.TreeNode := ⟨s, E, hs⟩
  let F := (B.levelNodes (E + 1)).filter (fun u => Q s u.val)
  have hF : ∀ v ∈ F, ∃ b : Branch B, b.Through v ∧
      ∀ L, FixedColorLevelMatrix T roots L color (branchColor T B c b) := by
    intro v hv
    exact hbranches v (B.rel_trans hts (Finset.mem_filter.mp hv).2)
  obtain ⟨_, old, last, _, hdense, _, hcover, _, hcolored⟩ :=
    branch_dense_frontier T B c hst d roots hr (D + 1) (hDd.trans (Nat.le_succ D)) color F hF
  let columns := fun i => (old i).filter (fun u => R i (firstRoots i).val u.val)
  refine ⟨firstRoots, lastRoot, columns, last, color, ?_, B.nodeHeight_eq lastRoot E hs, ?_, ?_, ?_⟩
  · intro i
    exact (T i).nodeHeight_eq (firstRoots i) D (hfmem i)
  · intro i u hu hru
    obtain ⟨v, hv, huv⟩ := hdense i u hu ((T i).rel_trans (hfrel i) hru)
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, (T i).rel_trans hru huv⟩, huv⟩
  · intro u hu hsu
    let u' : B.TreeNode := ⟨u, E + 1, hu⟩
    exact hcover u' (Finset.mem_filter.mpr ⟨(B.mem_levelNodes _ _).mpr hu, hsu⟩)
  · intro x hx y hy
    exact hcolored x (Fintype.mem_piFinset.mpr
      (fun i => (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hx i)).1)) y hy

end RelationalRamsey632.Milliken
