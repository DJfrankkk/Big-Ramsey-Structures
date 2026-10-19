import RelationalRamsey632.Milliken.ConeTrees

/-! Graft synchronized strong cone forests above a finite preserved prefix. -/

namespace RelationalRamsey632.Milliken

open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

namespace PrefixForestGraft

variable {α : Type} [DecidableEq α] {R : α → α → Prop}
    (T : FiniteLevelTree α R) (k : ℕ)
    (e : ℕ → ℕ) (he : StrictMono e)
    (F : ∀ a : ConeAnchor T (k + 1), (coneTree T (k + 1) a).StrongFrame)
    (hF : ∀ a, (F a).index = e)

noncomputable def tailNodes (r : ℕ) : Finset α :=
  Finset.univ.biUnion (fun a => (F a).nodes r)

theorem mem_tailNodes (r : ℕ) (v : α) :
    v ∈ tailNodes T k F r ↔ ∃ a, v ∈ (F a).nodes r := by
  classical
  simp only [tailNodes, Finset.mem_biUnion, Finset.mem_univ, true_and]

include hF in
theorem tailNodes_subset (r : ℕ) : tailNodes T k F r ⊆ T.nodes (k + 1 + e r) := by
  intro v hv
  obtain ⟨a, ha⟩ := (mem_tailNodes T k F r v).mp hv
  have hh := (F a).nodes_subset r ha
  rw [hF] at hh
  exact coneTree_nodes_subset T (k + 1) a (e r) hh

theorem tailNode_below (r : ℕ) (a : ConeAnchor T (k + 1)) (v : α)
    (hv : v ∈ (F a).nodes r) : R a.val v := by
  exact coneTree_below T _ a ((F a).index r) v ((F a).nodes_subset r hv)

theorem anchor_eq_of_descendants (r s : ℕ) (a b : ConeAnchor T (k + 1))
    (u v : α) (hu : u ∈ (F a).nodes r) (hv : v ∈ (F b).nodes s)
    (huv : R u v) : a = b := by
  have hav : R a.val v := T.rel_trans (tailNode_below T k F r a u hu) huv
  have hbv := tailNode_below T k F s b v hv
  have hvl := coneTree_nodes_subset T (k + 1) b ((F b).index s)
    ((F b).nodes_subset s hv)
  exact Subtype.ext
    (T.node_eq_of_common_extension _ _ a.val b.val v a.property b.property hvl hav hbv)

def index (n : ℕ) : ℕ := if n ≤ k then n else k + 1 + e (n - k - 1)

noncomputable def nodes (n : ℕ) : Finset α :=
  if n ≤ k then T.nodes n else tailNodes T k F (n - k - 1)

theorem index_initial (n : ℕ) (hn : n ≤ k) : index k e n = n := by
  simp only [index, if_pos hn]

theorem nodes_initial (n : ℕ) (hn : n ≤ k) : nodes T k F n = T.nodes n := by
  simp only [nodes, if_pos hn]

theorem index_tail (r : ℕ) : index k e (k + 1 + r) = k + 1 + e r := by
  simp only [index, if_neg (by omega : ¬ k + 1 + r ≤ k)]
  congr 2
  omega

theorem nodes_tail (r : ℕ) : nodes T k F (k + 1 + r) = tailNodes T k F r := by
  simp only [nodes, if_neg (by omega : ¬ k + 1 + r ≤ k)]
  congr 1
  omega

theorem nodes_firsttail : nodes T k F (k + 1) = tailNodes T k F 0 := by
  simpa only [Nat.add_zero] using nodes_tail T k F 0

include he in
theorem index_strictMono : StrictMono (index k e) := by
  intro n m hnm
  by_cases hn : n ≤ k
  · rw [index_initial k e n hn]
    by_cases hm : m ≤ k
    · rw [index_initial k e m hm]
      exact hnm
    · simp only [index, if_neg hm]
      omega
  · have hm : ¬ m ≤ k := by omega
    simp only [index, if_neg hn, if_neg hm]
    have hnm' : n - k - 1 < m - k - 1 := by omega
    have he' := he hnm'
    omega

include hF in
theorem nodes_subset (n : ℕ) : nodes T k F n ⊆ T.nodes (index k e n) := by
  by_cases hn : n ≤ k
  · rw [nodes_initial T k F n hn, index_initial k e n hn]
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (by omega : k + 1 ≤ n)
    rw [nodes_tail, index_tail]
    exact tailNodes_subset T k e F hF r

theorem parent (n : ℕ) (w : α) (hw : w ∈ nodes T k F (n + 1)) :
    ∃ u ∈ nodes T k F n, R u w := by
  by_cases hn : n < k
  · rw [nodes_initial T k F (n + 1) (by omega)] at hw
    obtain ⟨u, ⟨hu, huw⟩, _⟩ := T.ancestor n (n + 1) (Nat.le_succ n) w hw
    exact ⟨u, by rw [nodes_initial T k F n (by omega)]; exact hu, huw⟩
  · by_cases heq : n = k
    · subst n
      have hw' : w ∈ tailNodes T k F 0 := by
        rwa [nodes_firsttail] at hw
      obtain ⟨a, ha⟩ := (mem_tailNodes T k F 0 w).mp hw'
      obtain ⟨u, ⟨hu, hua⟩, _⟩ :=
        T.ancestor k (k + 1) (Nat.le_succ k) a.val a.property
      exact ⟨u, by rw [nodes_initial T k F k le_rfl]; exact hu,
        T.rel_trans hua (tailNode_below T k F 0 a w ha)⟩
    · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (by omega : k + 1 ≤ n)
      have hnext : k + 1 + r + 1 = k + 1 + (r + 1) := by omega
      rw [hnext, nodes_tail] at hw
      obtain ⟨a, ha⟩ := (mem_tailNodes T k F (r + 1) w).mp hw
      obtain ⟨u, hu, huw⟩ := (F a).parent r w ha
      exact ⟨u, by rw [nodes_tail]; exact (mem_tailNodes T k F r u).mpr ⟨a, hu⟩, huw⟩

include hF in
theorem successor (n : ℕ) (u : α) (hu : u ∈ nodes T k F n)
    (v : α) (hv : v ∈ T.nodes (index k e n + 1)) (huv : R u v) :
    ∃! w, w ∈ nodes T k F (n + 1) ∧ R v w := by
  by_cases hn : n < k
  · rw [index_initial k e n (by omega)] at hv
    refine ⟨v, ⟨?_, T.rel_refl v⟩, ?_⟩
    · rw [nodes_initial T k F (n + 1) (by omega)]
      exact hv
    · intro w hw
      rw [nodes_initial T k F (n + 1) (by omega)] at hw
      exact T.node_eq_of_common_extension _ _ w v w hw.1 hv hw.1 (T.rel_refl w) hw.2
  · by_cases heq : n = k
    · subst n
      rw [index_initial k e k le_rfl] at hv
      let a : ConeAnchor T (k + 1) := ⟨v, hv⟩
      let w := (F a).root
      have hw : w ∈ (F a).nodes 0 := by rw [(F a).nodes_zero]; exact Finset.mem_singleton_self _
      have hvw : R v w := tailNode_below T k F 0 a w hw
      refine ⟨w, ⟨?_, hvw⟩, ?_⟩
      · have hw' : w ∈ tailNodes T k F 0 := (mem_tailNodes T k F 0 w).mpr ⟨a, hw⟩
        rw [nodes_firsttail]
        exact hw'
      · intro z hz
        have hz' : z ∈ tailNodes T k F 0 := by
          rw [← nodes_firsttail]
          exact hz.1
        obtain ⟨b, hb⟩ := (mem_tailNodes T k F 0 z).mp hz'
        have hzb := tailNode_below T k F 0 b z hb
        have hzlevel := tailNodes_subset T k e F hF 0 hz'
        have hab : a = b := Subtype.ext
          (T.node_eq_of_common_extension _ _ v b.val z hv b.property hzlevel hz.2 hzb)
        subst b
        have hez : z = (F a).root := by
          rw [(F a).nodes_zero] at hb
          exact Finset.mem_singleton.mp hb
        exact hez
    · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (by omega : k + 1 ≤ n)
      rw [nodes_tail] at hu
      obtain ⟨a, ha⟩ := (mem_tailNodes T k F r u).mp hu
      rw [index_tail] at hv
      have hav : R a.val v := T.rel_trans (tailNode_below T k F r a u ha) huv
      have hvcone : v ∈ (coneTree T (k + 1) a).nodes ((F a).index r + 1) := by
        rw [hF]
        apply (mem_coneNodes T (k + 1) a (e r + 1) v).mpr
        exact ⟨by simpa only [Nat.add_assoc] using hv, hav⟩
      obtain ⟨w, ⟨hw, hvw⟩, huniq⟩ := (F a).successor r u ha v hvcone huv
      have hnext : k + 1 + r + 1 = k + 1 + (r + 1) := by omega
      refine ⟨w, ⟨?_, hvw⟩, ?_⟩
      · rw [hnext, nodes_tail]
        exact (mem_tailNodes T k F (r + 1) w).mpr ⟨a, hw⟩
      · intro z hz
        rw [hnext, nodes_tail] at hz
        obtain ⟨b, hb⟩ := (mem_tailNodes T k F (r + 1) z).mp hz.1
        have hzb := tailNode_below T k F (r + 1) b z hb
        have haz : R a.val z := T.rel_trans hav hz.2
        have hzlevel := tailNodes_subset T k e F hF (r + 1) hz.1
        have hab : a = b := Subtype.ext
          (T.node_eq_of_common_extension _ _ a.val b.val z a.property b.property hzlevel haz hzb)
        subst b
        exact huniq z ⟨hb, hz.2⟩

noncomputable def frame : T.StrongFrame where
  index := index k e
  index_strictMono := index_strictMono k e he
  nodes := nodes T k F
  root := T.root
  nodes_zero := by rw [nodes_initial T k F 0 (Nat.zero_le k), T.nodes_zero]
  nodes_subset := nodes_subset T k e F hF
  parent := parent T k F
  successor := successor T k e F hF

theorem frame_preserved (n : ℕ) (hn : n ≤ k) :
    (frame T k e he F hF).index n = n ∧ (frame T k e he F hF).nodes n = T.nodes n :=
  ⟨index_initial k e n hn, nodes_initial T k F n hn⟩

end PrefixForestGraft

end RelationalRamsey632.Milliken
