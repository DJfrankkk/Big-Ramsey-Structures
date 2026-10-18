import RelationalRamsey632.Transfer.CopyDegrees

/-! Empty degrees and invariance under an actual base isomorphism. -/

namespace RelationalRamsey632.Transfer

variable {L : Language} {A B X : Type}

theorem embedding_degree_positive {a : RelStructure L A} {K : RelStructure L X}
    (ha : Nonempty (RelEmbedding a K)) {t : ℕ} (ht : EmbeddingDegreeBound a K t) :
    1 ≤ t := by
  classical
  obtain ⟨g, colors, hcard, hcolors⟩ := ht Unit (fun _ => ())
  exact (Finset.one_le_card.mpr ⟨(), hcolors (Classical.choice ha)⟩).trans hcard

theorem copy_degree_positive {a : RelStructure L A} {K : RelStructure L X}
    (ha : Nonempty (RelEmbedding a K)) {t : ℕ} (ht : CopyDegreeBound a K t) :
    1 ≤ t := by
  classical
  obtain ⟨g, colors, hcard, hcolors⟩ := ht Unit (fun _ => ())
  exact (Finset.one_le_card.mpr ⟨(), hcolors (copyOf (Classical.choice ha))⟩).trans hcard

theorem empty_embedding_degree [IsEmpty A] (a : RelStructure L A) (K : RelStructure L X)
    (ha : Nonempty (RelEmbedding a K)) : ExactEmbeddingDegree a K 1 := by
  classical
  let e := Classical.choice ha
  constructor
  · intro D _ c
    refine ⟨RelEmbedding.refl K, {c e}, by simp, ?_⟩
    intro f
    have hf : f = e := RelEmbedding.ext (fun x => isEmptyElim x)
    simpa only [RelEmbedding.refl_comp, hf] using Finset.mem_singleton_self (c e)
  · exact fun _ ht => embedding_degree_positive ha ht

theorem empty_copy_degree [IsEmpty A] (a : RelStructure L A) (K : RelStructure L X)
    (ha : Nonempty (RelEmbedding a K)) : ExactCopyDegree a K 1 :=
  ⟨copy_degree_bound_of_embedding_bound (empty_embedding_degree a K ha).1,
    fun _ ht => copy_degree_positive ha ht⟩

theorem exact_degree_one_of_source (a : RelStructure L A) (K : RelStructure L X)
    (ha : Nonempty (RelEmbedding a K)) (hR : SourceDegreeOne K a) :
    ExactEmbeddingDegree a K 1 := by
  classical
  let e := Classical.choice ha
  constructor
  · intro D _ c
    obtain ⟨g, hg⟩ := hR D c
    refine ⟨g, {c (g.comp e)}, by simp, ?_⟩
    intro f
    rw [hg f e]
    exact Finset.mem_singleton_self _
  · exact fun _ ht => embedding_degree_positive ha ht

theorem embedding_degree_bound_relabel {a : RelStructure L A} {b : RelStructure L B}
    {K : RelStructure L X} (u : RelEmbedding a b) (hu : Function.Surjective u)
    {t : ℕ} (ht : EmbeddingDegreeBound a K t) : EmbeddingDegreeBound b K t := by
  classical
  let v := inverseEmbedding u hu
  intro D _ c
  obtain ⟨g, colors, hcard, hcolors⟩ := ht D (fun e => c (e.comp v))
  refine ⟨g, colors, hcard, ?_⟩
  intro e
  have he : ((g.comp (e.comp u)).comp v) = g.comp e := by
    apply RelEmbedding.ext
    intro x
    exact congrArg (fun y => g (e y)) (inverseEmbedding_right u hu x)
  simpa only [he] using hcolors (e.comp u)

theorem embedding_degree_bound_iff_relabel {a : RelStructure L A} {b : RelStructure L B}
    {K : RelStructure L X} (u : RelEmbedding a b) (hu : Function.Surjective u) (t : ℕ) :
    EmbeddingDegreeBound a K t ↔ EmbeddingDegreeBound b K t := by
  constructor
  · exact embedding_degree_bound_relabel u hu
  · exact embedding_degree_bound_relabel (inverseEmbedding u hu)
      (fun x => ⟨u x, inverseEmbedding_left u hu x⟩)

theorem exact_embedding_degree_iff_relabel {a : RelStructure L A} {b : RelStructure L B}
    {K : RelStructure L X} (u : RelEmbedding a b) (hu : Function.Surjective u) (t : ℕ) :
    ExactEmbeddingDegree a K t ↔ ExactEmbeddingDegree b K t := by
  simp only [ExactEmbeddingDegree, embedding_degree_bound_iff_relabel u hu]

end RelationalRamsey632.Transfer
