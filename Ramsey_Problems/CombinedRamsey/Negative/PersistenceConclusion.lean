import CombinedRamsey.Negative.PersistenceColouring
import CombinedRamsey.Negative.VertexDegrees

namespace CombinedRamsey.Negative

open RelationalRamsey632 RelationalRamsey632.Transfer

variable {L : Language}

theorem realization_hasPointType {n : ℕ}
    {t : RelStructure L (Fin n ⊕ Unit)} {K : RelStructure L ℕ}
    {b : RelEmbedding (t.pullback Sum.inl) K}
    {δ : RelStructure L (Fin 1)}
    (hδ : t.pullback (fun _ : Fin 1 => Sum.inr ()) = δ)
    {x : ℕ} (hx : x ∈ Realizations t K b) : HasPointType K δ x := by
  obtain ⟨e, _, hs⟩ := hx
  have he := congrArg (fun z => z.pullback (fun _ : Fin 1 => Sum.inr ())) e.pullback_eq
  change K.pullback (fun _ : Fin 1 => e (Sum.inr ())) =
    t.pullback (fun _ : Fin 1 => Sum.inr ()) at he
  rw [hs, hδ] at he
  exact he

/-- Arbitrarily large finite families of incomparable actual realization
ages yield colourings of the fixed singleton type with every colour in every
actual copy. Families may depend on the number of colours; K and δ remain fixed. -/
theorem persistent_vertex_colourings_of_incomparable_ages
    (K : RelStructure L ℕ) (δ : RelStructure L (Fin 1))
    (hh : FiniteEmbeddingHomogeneous K)
    (hfamilies : ∀ q, ∃ (size : Fin (q + 1) → ℕ)
      (type : ∀ i, RelStructure L (Fin (size i) ⊕ Unit))
      (original : ∀ i, Boundary size type K i),
      (∀ i, (Realizations (type i) K (original i)).Nonempty) ∧
      (∀ i, (type i).pullback (fun _ : Fin 1 => Sum.inr ()) = δ) ∧
      (∀ i, AgeIndivisibleOn K (Realizations (type i) K (original i))) ∧
      (∀ i j, i ≠ j → ∃ (n : ℕ) (a : RelStructure L (Fin n)),
        InAgeOn K (Realizations (type i) K (original i)) a ∧
        ¬ InAgeOn K (Realizations (type j) K (original j)) a)) :
    PersistentVertexColourings K δ := by
  intro q
  obtain ⟨size, type, original, hreal, hδ, hind, hincomp⟩ := hfamilies q
  obtain ⟨χ, hχ⟩ := persistent_realization_ages size type K original hh hind hincomp
  refine ⟨χ, ?_⟩
  intro f i
  obtain ⟨z, hz⟩ := hreal i
  have hpoint := realization_hasPointType (hδ i) hz
  have hd : InAgeOn K (Realizations (type i) K (original i)) δ :=
    ⟨singletonEmbedding z hpoint, fun _ => hz⟩
  obtain ⟨e, he⟩ := (hχ f i 1 δ).mp hd
  obtain ⟨x, hx, hxe⟩ := (he 0).1
  refine ⟨x, realization_hasPointType (hδ i) hx, ?_⟩
  exact hxe ▸ (he 0).2

end CombinedRamsey.Negative
