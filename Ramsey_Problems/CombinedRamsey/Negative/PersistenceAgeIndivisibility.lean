import CombinedRamsey.Negative.PersistenceNatTransport
import CombinedRamsey.Negative.FreePosition

namespace CombinedRamsey.Negative

open RelationalRamsey632

variable {L : Language} {X : Type}

/-- All three parts of `neg:age-indivisibility`, for an actual realized
one-point type. The transitive linked realization set, its full linked
free amalgamation, its countably infinite presentation, and forgetting links
are proved internally in the imported construction. -/
theorem realization_age_indivisible [Countable X] (K : RelStructure L X)
    (hh : FiniteEmbeddingHomogeneous K) (hfree : AgeSharedFree K)
    {n : ℕ} (t : RelStructure L (Fin n ⊕ Unit))
    (b : RelEmbedding (t.pullback Sum.inl) K)
    (hreal : (Realizations t K b).Nonempty) :
    AgeIndivisibleOn K (Realizations t K b) := by
  classical
  let M := linkedModel t K b
  obtain ⟨e⟩ := linked_vertices_nat_equiv hh hfree hreal
  have hhh : FiniteEmbeddingHomogeneous M := linked_finite_homogeneous t K b hh
  have hshared : AgeSharedFree M := linked_age_shared_free hh hfree
  have hNhh := finite_homogeneous_nat_transport M e hhh
  have hNshared := age_shared_nat_transport M e hshared
  have hNfree := ageFree_of_sharedFree (M.pullback e) hNshared
  have hNposition := freePosition_of_homogeneous_shared_free (M.pullback e) hNhh hNshared
  have hNsingle := linked_singletons_nat_transport t K b e
  have hNind := transitive_free_age_indivisible (M.pullback e) hNhh hNfree hNposition hNsingle
  have hMind := ageIndivisible_of_sameAge hNind (sameAgeOn_nat_transport M e)
  have hbase := ageIndivisible_reduct (originalLinkInclusion L (Fin n)) M hMind
  exact ageIndivisible_of_sameAge hbase (sameAgeOn_linked_reduct t K b)

theorem same_age_realization_age_indivisible [Countable X]
    (K : RelStructure L X) (hh : FiniteEmbeddingHomogeneous K) (hfree : AgeSharedFree K)
    {n : ℕ} (t : RelStructure L (Fin n ⊕ Unit))
    (b : RelEmbedding (t.pullback Sum.inl) K)
    (hreal : (Realizations t K b).Nonempty)
    {Y : Type} (N : RelStructure L Y) (Q : Set Y)
    (hage : SameAgeOn K (Realizations t K b) N Q) : AgeIndivisibleOn N Q :=
  ageIndivisible_of_sameAge (realization_age_indivisible K hh hfree t b hreal) hage

end CombinedRamsey.Negative
