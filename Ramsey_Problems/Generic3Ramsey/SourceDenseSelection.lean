import Generic3Ramsey.SourceStableSections

/-! Finite minimal-coordinate selection in the original HDHL2 argument. -/

namespace Generic3Ramsey.SourceTrees.FiniteLevelTree

variable {α β : Type} [DecidableEq α] [DecidableEq β]
variable {R : α → α → Prop} {Q : β → β → Prop}
variable (S : FiniteLevelTree α R) (T : FiniteLevelTree β Q)

def TauDenseAbove (t : T.TreeNode) (X : Set T.TreeNode) : Prop :=
  ∀ u : T.TreeNode, Q t.val u.val → ∃ y ∈ X, Q u.val y.val

def SomewhereTauDense (X : Set T.TreeNode) : Prop := ∃ t, T.TauDenseAbove t X

def MixedSomewhereMatrix (P : α → β → Prop) : Prop :=
  ∃ (d : ℕ) (r : S.TreeNode) (s : T.TreeNode) (A : Finset S.TreeNode) (B : Finset T.TreeNode),
    S.nodeHeight r = d ∧ T.nodeHeight s = d ∧
    S.DenseAbove r (d + 1) A ∧ T.DenseAbove s (d + 1) B ∧
    ∀ u ∈ A, ∀ v ∈ B, P u.val v.val

omit [DecidableEq β] in
theorem denseAbove_mono (x : S.TreeNode) {m n : ℕ} (hmn : m ≤ n)
    {A : Finset S.TreeNode} (hA : S.DenseAbove x n A) : S.DenseAbove x m A := by
  intro u hu hxu
  obtain ⟨v, hv, huv⟩ := S.extend m n hmn u hu
  obtain ⟨w, hw, hvw⟩ := hA v hv (S.rel_trans hxu huv)
  exact ⟨w, hw, S.rel_trans huv hvw⟩

theorem badCoordinate_mono (P : α → β → Prop) (x : S.TreeNode)
    {m n : ℕ} (hmn : m ≤ n) (y : T.TreeNode)
    (hn : S.BadCoordinate T P x n y) : S.BadCoordinate T P x m y := by
  obtain ⟨A, hA, hneg⟩ := hn
  exact ⟨A, S.denseAbove_mono x hmn hA, hneg⟩

omit [DecidableEq α] in
theorem tauDenseAbove_restrict {t u : T.TreeNode} {X : Set T.TreeNode}
    (hX : T.TauDenseAbove t X) (htu : Q t.val u.val) :
    T.TauDenseAbove u {y | y ∈ X ∧ Q u.val y.val} := by
  intro v huv
  obtain ⟨y, hy, hvy⟩ := hX v (T.rel_trans htu huv)
  exact ⟨y, ⟨hy, T.rel_trans huv hvy⟩, hvy⟩

omit [DecidableEq α] in
theorem not_somewhere_tauDense {X : Set T.TreeNode} (hX : ¬T.SomewhereTauDense X)
    (t : T.TreeNode) : ∃ u : T.TreeNode, Q t.val u.val ∧ ∀ y ∈ X, ¬Q u.val y.val := by
  classical
  have hnot : ¬∀ u : T.TreeNode, Q t.val u.val → ∃ y ∈ X, Q u.val y.val :=
    fun h => hX ⟨t, h⟩
  obtain ⟨u, hu⟩ := not_forall.mp hnot
  obtain ⟨htu, hnone⟩ := Classical.not_imp.mp hu
  refine ⟨u, htu, ?_⟩
  intro y hy huy
  exact hnone ⟨y, hy, huy⟩

/-- The finite-coordinate core of Todorčević's Lemma 3.15, specialized
to two trees. Under section stability and absence of a negative matrix,
one common density threshold works on a somewhere dense second-coordinate
family for every one of the finitely many first-coordinate level nodes. -/
theorem stable_sections_dense_good_family (P : α → β → Prop)
    (hstable : S.StableSections T P)
    (hnegative : ¬S.MixedSomewhereMatrix T (fun u v => ¬P u v))
    (k : ℕ) (K : Finset S.TreeNode) (hK : ∀ x ∈ K, S.nodeHeight x = k)
    (X : Set T.TreeNode) (hX : T.SomewhereTauDense X) :
    ∃ n, T.SomewhereTauDense {y | y ∈ X ∧ ∀ x ∈ K, ¬S.BadCoordinate T P x n y} := by
  classical
  by_contra hfail
  have hfail' : ∀ n, ¬T.SomewhereTauDense
      {y | y ∈ X ∧ ∀ x ∈ K, ¬S.BadCoordinate T P x n y} := by
    simpa only [not_exists] using hfail
  let Covers := fun D : Finset S.TreeNode =>
    ∃ (Y : Set T.TreeNode) (t : T.TreeNode) (n₀ : ℕ),
      Y ⊆ X ∧ T.TauDenseAbove t Y ∧
      ∀ n ≥ n₀, ∀ y ∈ Y, (∃ x ∈ K, S.BadCoordinate T P x n y) →
        ∃ x ∈ D, S.BadCoordinate T P x n y
  have hsome : ∃ n, ∃ D : Finset S.TreeNode, D ⊆ K ∧ D.card = n ∧ Covers D := by
    obtain ⟨t, ht⟩ := hX
    exact ⟨K.card, K, Finset.Subset.refl K, rfl, X, t, 0, Set.Subset.refl X,
      ht, by intro n hn y hy hbad; exact hbad⟩
  obtain ⟨D, hDK, hcard, Y, t, n₀, hYX, hYdense, hcover⟩ := Nat.find_spec hsome
  have hmin : ∀ E : Finset S.TreeNode, E ⊆ K → Covers E → D.card ≤ E.card := by
    intro E hEK hE
    rw [hcard]
    exact Nat.find_min' hsome ⟨E, hEK, rfl, hE⟩
  have hDne : D.Nonempty := by
    obtain ⟨u, htu, havoid⟩ := T.not_somewhere_tauDense (hfail' n₀) t
    obtain ⟨y, hy, huy⟩ := hYdense u htu
    have hnot : ¬∀ x ∈ K, ¬S.BadCoordinate T P x n₀ y := by
      intro hg
      exact havoid y ⟨hYX hy, hg⟩ huy
    have hbad : ∃ x ∈ K, S.BadCoordinate T P x n₀ y := by
      push Not at hnot
      exact hnot
    obtain ⟨x, hx, _⟩ := hcover n₀ le_rfl y hy hbad
    exact ⟨x, hx⟩
  obtain ⟨x, hxD⟩ := hDne
  have hxdense : ∀ n (u : T.TreeNode), Q t.val u.val →
      ∃ y ∈ Y, Q u.val y.val ∧ S.BadCoordinate T P x n y := by
    intro n u htu
    by_contra hnone
    have hav : ∀ y ∈ Y, Q u.val y.val → ¬S.BadCoordinate T P x n y := by
      intro y hy huy hbad
      exact hnone ⟨y, hy, huy, hbad⟩
    have hE : Covers (D.erase x) := by
      refine ⟨{y | y ∈ Y ∧ Q u.val y.val}, u, max n₀ n, ?_,
        T.tauDenseAbove_restrict hYdense htu, ?_⟩
      · intro y hy
        exact hYX hy.1
      · intro j hj y hy hbad
        obtain ⟨z, hz, hzb⟩ := hcover j ((Nat.le_max_left _ _).trans hj) y hy.1 hbad
        have hzx : z ≠ x := by
          intro heq
          subst z
          exact hav y hy.1 hy.2
            (S.badCoordinate_mono T P x ((Nat.le_max_right _ _).trans hj) y hzb)
        exact ⟨z, Finset.mem_erase.mpr ⟨hzx, hz⟩, hzb⟩
    have hle := hmin (D.erase x) (Finset.erase_subset x D |>.trans hDK) hE
    have hlt := Finset.card_erase_lt_of_mem hxD
    omega
  let d := max k (T.nodeHeight t)
  obtain ⟨s, hs, hts⟩ := T.extend (T.nodeHeight t) d (Nat.le_max_right _ _)
    t.val (T.nodeHeight_mem t)
  let s' : T.TreeNode := ⟨s, d, hs⟩
  let F := (T.levelNodes (d + 1)).filter (fun u => Q s u.val)
  have hbadF : ∀ y ∈ F, ∀ n ≥ d + 1,
      ∃ z : T.TreeNode, Q y.val z.val ∧ S.BadCoordinate T P x n z := by
    intro y hy n _
    obtain ⟨z, _, hyz, hzb⟩ := hxdense n y (T.rel_trans hts (Finset.mem_filter.mp hy).2)
    exact ⟨z, hyz, hzb⟩
  obtain ⟨A, B, hA, _, hB, hAB⟩ := S.bad_coordinates_give_rectangle T P hstable x d F hbadF
  have hxk : S.nodeHeight x = k := hK x (hDK hxD)
  obtain ⟨r, hr, hxr⟩ := S.extend k d (Nat.le_max_left _ _) x.val
    (by rw [← hxk]; exact S.nodeHeight_mem x)
  let r' : S.TreeNode := ⟨r, d, hr⟩
  let A' := A.filter (fun u => R r u.val)
  apply hnegative
  refine ⟨d, r', s', A', B, S.nodeHeight_eq r' d hr, T.nodeHeight_eq s' d hs, ?_, ?_, ?_⟩
  · intro u hu hru
    obtain ⟨v, hv, huv⟩ := hA u hu (S.rel_trans hxr hru)
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, S.rel_trans hru huv⟩, huv⟩
  · intro u hu hsu
    let u' : T.TreeNode := ⟨u, d + 1, hu⟩
    exact hB u' (Finset.mem_filter.mpr ⟨(T.mem_levelNodes _ _).mpr hu, hsu⟩)
  · intro u hu v hv
    exact (hAB u (Finset.mem_filter.mp hu).1 v hv).2

end Generic3Ramsey.SourceTrees.FiniteLevelTree
