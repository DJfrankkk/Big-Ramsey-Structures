import CombinedRamsey.Negative.PersistenceAgeIndivisibility
import CombinedRamsey.Negative.PersistenceConclusion

namespace CombinedRamsey.Negative

open RelationalRamsey632

variable {L : Language}

/-- The persistent-colouring theorem with one-type age indivisibility
internally discharged from the actual homogeneous free-amalgamation age. -/
theorem persistent_colours_of_incomparable_realized_types
    (K : RelStructure L ℕ) (δ : RelStructure L (Fin 1))
    (hh : FiniteEmbeddingHomogeneous K) (hfree : AgeSharedFree K)
    (hfamilies : ∀ q, ∃ (size : Fin (q + 1) → ℕ)
      (type : ∀ i, RelStructure L (Fin (size i) ⊕ Unit))
      (original : ∀ i, Boundary size type K i),
      (∀ i, (Realizations (type i) K (original i)).Nonempty) ∧
      (∀ i, (type i).pullback (fun _ : Fin 1 => Sum.inr ()) = δ) ∧
      (∀ i j, i ≠ j → ∃ (n : ℕ) (a : RelStructure L (Fin n)),
        InAgeOn K (Realizations (type i) K (original i)) a ∧
        ¬ InAgeOn K (Realizations (type j) K (original j)) a)) :
    PersistentVertexColourings K δ := by
  apply persistent_vertex_colourings_of_incomparable_ages K δ hh
  intro q
  obtain ⟨size, type, original, hreal, hδ, hincomp⟩ := hfamilies q
  exact ⟨size, type, original, hreal, hδ,
    fun i => realization_age_indivisible K hh hfree (type i) (original i) (hreal i), hincomp⟩

end CombinedRamsey.Negative
