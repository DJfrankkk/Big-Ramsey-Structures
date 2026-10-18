import CombinedRamsey.Negative.PersistenceWeights

namespace CombinedRamsey.Negative

open RelationalRamsey632

variable {L : Language} {q : ℕ} (size : Fin (q + 1) → ℕ)
    (type : ∀ i, RelStructure L (Fin (size i) ⊕ Unit))
    (K : RelStructure L ℕ)

private theorem candidateWeight_exists {x : ℕ}
    (h : Nonempty (Candidates size type K x)) :
    ∃ w : ℕ, ∃ b : Candidates size type K x, boundaryWeight b.val.2 = w := by
  obtain ⟨b⟩ := h
  exact ⟨boundaryWeight b.val.2, b, rfl⟩

noncomputable def minimumCandidate {x : ℕ}
    (h : Nonempty (Candidates size type K x)) : Candidates size type K x := by
  classical
  exact Classical.choose (Nat.find_spec (candidateWeight_exists size type K h))

theorem minimumCandidate_weight_le {x : ℕ}
    (h : Nonempty (Candidates size type K x)) (b : Candidates size type K x) :
    boundaryWeight (minimumCandidate size type K h).val.2 ≤ boundaryWeight b.val.2 := by
  classical
  change boundaryWeight
    (Classical.choose (Nat.find_spec (candidateWeight_exists size type K h))).val.2 ≤ _
  rw [Classical.choose_spec (Nat.find_spec (candidateWeight_exists size type K h))]
  exact Nat.find_min' _ ⟨b, rfl⟩

noncomputable def persistenceColour (x : ℕ) : Fin (q + 1) := by
  classical
  exact if h : Nonempty (Candidates size type K x) then
    (minimumCandidate size type K h).val.1 else 0

theorem persistenceColour_at_candidate {x : ℕ} (b : Candidates size type K x) :
    persistenceColour size type K x =
      (minimumCandidate size type K (⟨b⟩ : Nonempty (Candidates size type K x))).val.1 := by
  classical
  unfold persistenceColour
  rw [dif_pos ⟨b⟩]

theorem realization_image_mem {n : ℕ} (t : RelStructure L (Fin n ⊕ Unit))
    (b : RelEmbedding (t.pullback Sum.inl) K) (f : RelEmbedding K K)
    {x : ℕ} (hx : x ∈ f '' Realizations t K b) :
    x ∈ Realizations t K (f.comp b) := by
  obtain ⟨y, ⟨e, he, hy⟩, rfl⟩ := hx
  refine ⟨f.comp e, ?_, ?_⟩
  · intro a
    exact congrArg f (he a)
  · exact congrArg f hy

/-- Proposition `neg:persistence`, with actual finite pointed types, full
embeddings, and actual induced ages. The only structural hypotheses are
finite homogeneity and the separately proved one-type age indivisibility. -/
theorem persistent_realization_ages
    (original : ∀ i, Boundary size type K i)
    (hh : FiniteEmbeddingHomogeneous K)
    (hind : ∀ i, AgeIndivisibleOn K (Realizations (type i) K (original i)))
    (hincomp : ∀ i j, i ≠ j → ∃ (n : ℕ) (a : RelStructure L (Fin n)),
      InAgeOn K (Realizations (type i) K (original i)) a ∧
      ¬ InAgeOn K (Realizations (type j) K (original j)) a) :
    ∃ χ : ℕ → Fin (q + 1), ∀ (f : RelEmbedding K K) i,
      SameAgeOn K (Realizations (type i) K (original i)) K
        ((f '' Realizations (type i) K (original i)) ∩ {x | χ x = i}) := by
  classical
  refine ⟨persistenceColour size type K, ?_⟩
  intro f i
  let b : Boundary size type K i := f.comp (original i)
  let C := Competing size type K i (boundaryWeight b)
  letI : Fintype C := Fintype.ofFinite C
  let enum : Fin (Fintype.card C) ≃ C := (Fintype.equivFin C).symm
  let Q : Fin (Fintype.card C) → Set ℕ := fun a =>
    Realizations (type (enum a).val.1) K (enum a).val.2
  apply persistent_age_of_finite_competitors (hind i) f (persistenceColour size type K) i Q
  · intro a
    have hne : i ≠ (enum a).val.1 := Ne.symm (enum a).property.1
    obtain ⟨n, d, hd, hn⟩ := hincomp i (enum a).val.1 hne
    refine ⟨n, d, hd, ?_⟩
    have hage := realizations_transport hh (type (enum a).val.1)
      (original (enum a).val.1) (enum a).val.2
    exact fun h => hn ((hage n d).mpr h)
  · intro x hx hnone
    have hb : x ∈ Realizations (type i) K b := realization_image_mem K (type i) (original i) f hx
    let candidate : Candidates size type K x := ⟨⟨i, b⟩, hb⟩
    let chosen := minimumCandidate size type K (⟨candidate⟩ : Nonempty (Candidates size type K x))
    rw [persistenceColour_at_candidate size type K candidate]
    change chosen.val.1 = i
    by_contra hne
    have hwle := minimumCandidate_weight_le size type K ⟨candidate⟩ candidate
    have hwne : boundaryWeight chosen.val.2 ≠ boundaryWeight b := by
      intro heq
      exact hne (equal_weight_index size type K hh hincomp chosen candidate heq)
    have hwlt : boundaryWeight chosen.val.2 < boundaryWeight b := lt_of_le_of_ne hwle hwne
    let competitor : C := ⟨chosen.val, hne, hwlt⟩
    have ha : x ∈ Q (enum.symm competitor) := by
      change x ∈ Realizations (type (enum (enum.symm competitor)).val.1) K
        (enum (enum.symm competitor)).val.2
      rw [enum.apply_symm_apply]
      exact chosen.property
    exact hnone ⟨enum.symm competitor, ha⟩

end CombinedRamsey.Negative
