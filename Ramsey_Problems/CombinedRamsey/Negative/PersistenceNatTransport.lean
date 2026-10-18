import CombinedRamsey.Negative.PersistenceLinkedInfinite

namespace CombinedRamsey.Negative

open RelationalRamsey632

variable {L : Language} {X : Type}

def equivEmbedding (K : RelStructure L X) (e : ℕ ≃ X) : RelEmbedding (K.pullback e) K :=
  RelEmbedding.pullback K e e.injective

def equivInverseEmbedding (K : RelStructure L X) (e : ℕ ≃ X) : RelEmbedding K (K.pullback e) where
  toFun := e.symm
  injective := e.symm.injective
  map_rel R t := by
    change K.rel R t ↔ K.rel R (e ∘ e.symm ∘ t)
    have he : e ∘ e.symm ∘ t = t := by funext i; exact e.apply_symm_apply (t i)
    rw [he]

theorem finite_homogeneous_nat_transport (K : RelStructure L X) (e : ℕ ≃ X)
    (hh : FiniteEmbeddingHomogeneous K) : FiniteEmbeddingHomogeneous (K.pullback e) := by
  intro F _ a u v
  obtain ⟨g, hg⟩ := hh F a ((equivEmbedding K e).comp u) ((equivEmbedding K e).comp v)
  refine ⟨(equivInverseEmbedding K e).comp (g.comp (equivEmbedding K e)), ?_⟩
  intro x
  change e.symm (g (e (u x))) = v x
  have hx : g (e (u x)) = e (v x) := hg x
  rw [hx, e.symm_apply_apply]

theorem age_shared_nat_transport (K : RelStructure L X) (e : ℕ ≃ X)
    (hfree : AgeSharedFree K) : AgeSharedFree (K.pullback e) := by
  intro B Y Z _ _ _ ML MR hbase hL hR
  obtain ⟨u⟩ := hL
  obtain ⟨v⟩ := hR
  obtain ⟨w⟩ := hfree B Y Z ML MR hbase
    ⟨(equivEmbedding K e).comp u⟩ ⟨(equivEmbedding K e).comp v⟩
  exact ⟨(equivInverseEmbedding K e).comp w⟩

theorem sameAgeOn_nat_transport (K : RelStructure L X) (e : ℕ ≃ X) :
    SameAgeOn (K.pullback e) Set.univ K Set.univ := by
  intro n a
  constructor
  · rintro ⟨u, _⟩
    exact ⟨(equivEmbedding K e).comp u, fun _ => Set.mem_univ _⟩
  · rintro ⟨u, _⟩
    exact ⟨(equivInverseEmbedding K e).comp u, fun _ => Set.mem_univ _⟩

theorem linked_singletons_nat_transport {n : ℕ}
    (t : RelStructure L (Fin n ⊕ Unit)) (K : RelStructure L X)
    (b : RelEmbedding (t.pullback Sum.inl) K) (e : ℕ ≃ LinkedVertices t K b) :
    TransitiveSingletons ((linkedModel t K b).pullback e) := by
  intro x y
  exact linked_singleton_types t K b (e x) (e y)

theorem sameAgeOn_linked_reduct {n : ℕ}
    (t : RelStructure L (Fin n ⊕ Unit)) (K : RelStructure L X)
    (b : RelEmbedding (t.pullback Sum.inl) K) :
    SameAgeOn ((linkedModel t K b).reduct (originalLinkInclusion L (Fin n))) Set.univ
      K (Realizations t K b) := by
  rw [linked_original_reduct]
  intro m a
  constructor
  · rintro ⟨u, _⟩
    exact ⟨{
      toFun := linkedValue ∘ u
      injective := (Subtype.val_injective.comp Subtype.val_injective).comp u.injective
      map_rel := fun R v => u.map_rel R v }, fun z => (u z).property⟩
  · rintro ⟨u, hu⟩
    let v : Fin m → LinkedVertices t K b := fun z =>
      ⟨⟨u z, realizes_outside_boundary (hu z)⟩, hu z⟩
    exact ⟨{
      toFun := v
      injective := fun x y h => u.injective (congrArg linkedValue h)
      map_rel := fun R v => u.map_rel R v }, fun _ => Set.mem_univ _⟩

end CombinedRamsey.Negative
