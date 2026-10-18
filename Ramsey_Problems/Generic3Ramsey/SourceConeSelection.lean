import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Insert

/-! A finite elimination lemma used in the ultrafilter proof of the
single-coordinate Halpern–Läuchli theorem. -/

namespace Generic3Ramsey.SourceTrees

/-- If finitely many hereditary properties cover every point, one property
holds on a full cone above some extension of any given point. -/
theorem finite_cone_selection {V K : Type} [Fintype K]
    (R : V → V → Prop) (href : ∀ v, R v v)
    (htrans : ∀ {u v w}, R u v → R v w → R u w)
    (P : K → V → Prop)
    (hhered : ∀ k u v, R u v → P k v → P k u)
    (hcover : ∀ u, ∃ k, P k u) (u : V) :
    ∃ v, R u v ∧ ∃ k, ∀ w, R v w → P k w := by
  classical
  have hselect : ∀ s : Finset K,
      (∃ v, R u v ∧ ∃ k, ∀ w, R v w → P k w) ∨
        ∃ v, R u v ∧ ∀ k ∈ s, ∀ w, R v w → ¬P k w := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact Or.inr ⟨u, href u, by simp⟩
    | @insert k s _ ih =>
        rcases ih with h | ⟨v, huv, hv⟩
        · exact Or.inl h
        · by_cases hdense : ∀ w, R v w → P k w
          · exact Or.inl ⟨v, huv, k, hdense⟩
          · obtain ⟨w, hw⟩ := not_forall.mp hdense
            have hw' : R v w ∧ ¬P k w := Classical.not_imp.mp hw
            refine Or.inr ⟨w, htrans huv hw'.1, ?_⟩
            intro j hj z hwz
            rcases Finset.mem_insert.mp hj with hjk | hj
            · subst j
              intro hp
              exact hw'.2 (hhered k w z hwz hp)
            · exact hv j hj z (htrans hw'.1 hwz)
  rcases hselect Finset.univ with h | ⟨v, _, hnone⟩
  · exact h
  · obtain ⟨k, hk⟩ := hcover v
    exact (hnone k (Finset.mem_univ k) v (href v) hk).elim

end Generic3Ramsey.SourceTrees
