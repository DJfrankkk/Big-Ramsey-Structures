import CombinedRamsey.Negative.PersistenceTypes

namespace CombinedRamsey.Negative

open RelationalRamsey632

variable {L : Language}

noncomputable def boundaryWeight {n : ℕ}
    {t : RelStructure L (Fin n ⊕ Unit)} {K : RelStructure L ℕ}
    (b : RelEmbedding (t.pullback Sum.inl) K) : ℕ :=
  ∑ x ∈ Finset.univ.image b, 2 ^ x

theorem boundaryWeight_eq_range {n m : ℕ}
    {t : RelStructure L (Fin n ⊕ Unit)} {s : RelStructure L (Fin m ⊕ Unit)}
    {K : RelStructure L ℕ}
    {b : RelEmbedding (t.pullback Sum.inl) K}
    {c : RelEmbedding (s.pullback Sum.inl) K}
    (hw : boundaryWeight b = boundaryWeight c) : Set.range b = Set.range c := by
  classical
  have hs : Finset.univ.image b = Finset.univ.image c := binaryWeight_injective hw
  ext x
  have hb : x ∈ Set.range b ↔ x ∈ Finset.univ.image b := by simp
  have hc : x ∈ Set.range c ↔ x ∈ Finset.univ.image c := by simp
  rw [hb, hc, hs]

theorem boundary_value_lt_weight {n : ℕ}
    {t : RelStructure L (Fin n ⊕ Unit)} {K : RelStructure L ℕ}
    (b : RelEmbedding (t.pullback Sum.inl) K) (a : Fin n) :
    b a < boundaryWeight b := by
  classical
  exact Finset.lt_geomSum_of_mem (by omega)
    (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)

instance finite_bounded_boundaries {n : ℕ}
    (t : RelStructure L (Fin n ⊕ Unit)) (K : RelStructure L ℕ) (w : ℕ) :
    Finite {b : RelEmbedding (t.pullback Sum.inl) K | boundaryWeight b < w} := by
  let f : {b : RelEmbedding (t.pullback Sum.inl) K | boundaryWeight b < w} →
      (Fin n → Fin w) := fun b a => ⟨b.val a, (boundary_value_lt_weight b.val a).trans b.property⟩
  apply Finite.of_injective f
  intro b c heq
  apply Subtype.ext
  apply RelationalRamsey632.RelEmbedding.ext
  intro a
  exact congrArg Fin.val (congrFun heq a)

variable {q : ℕ} (size : Fin (q + 1) → ℕ)
    (type : ∀ i, RelStructure L (Fin (size i) ⊕ Unit))
    (K : RelStructure L ℕ)

abbrev Boundary (i : Fin (q + 1)) := RelEmbedding ((type i).pullback Sum.inl) K

def Candidates (x : ℕ) :=
  {b : (Σ i, Boundary size type K i) | x ∈ Realizations (type b.1) K b.2}

def Competing (i : Fin (q + 1)) (w : ℕ) :=
  {b : (Σ j, Boundary size type K j) | b.1 ≠ i ∧ boundaryWeight b.2 < w}

instance competing_finite (i : Fin (q + 1)) (w : ℕ) :
    Finite (Competing size type K i w) := by
  let f : Competing size type K i w →
      (Σ j, {b : Boundary size type K j | boundaryWeight b < w}) :=
    fun b => ⟨b.val.1, b.val.2, b.property.2⟩
  apply Finite.of_injective f
  intro b c h
  apply Subtype.ext
  exact congrArg (fun a : (Σ j, {b : Boundary size type K j | boundaryWeight b < w}) =>
    (⟨a.1, a.2.val⟩ : Σ j, Boundary size type K j)) h

/-- If two minimum-weight witnesses share their new vertex, their boundary
sets coincide and their full realization sets coincide. -/
theorem equal_weight_realizations {x : ℕ} (b c : Candidates size type K x)
    (hweight : boundaryWeight b.val.2 = boundaryWeight c.val.2) :
    Realizations (type b.val.1) K b.val.2 =
      Realizations (type c.val.1) K c.val.2 :=
  realizations_eq_of_same_boundary_and_common (boundaryWeight_eq_range hweight)
    b.property c.property

/-- Actual incomparable ages force the index of a weight-minimizing witness
to be unique. Different labelings of the same boundary cause no tie. -/
theorem equal_weight_index {original : ∀ i, Boundary size type K i}
    (hh : FiniteEmbeddingHomogeneous K)
    (hincomp : ∀ i j, i ≠ j → ∃ (n : ℕ) (a : RelStructure L (Fin n)),
      InAgeOn K (Realizations (type i) K (original i)) a ∧
      ¬ InAgeOn K (Realizations (type j) K (original j)) a)
    {x : ℕ} (b c : Candidates size type K x)
    (hweight : boundaryWeight b.val.2 = boundaryWeight c.val.2) :
    b.val.1 = c.val.1 := by
  by_contra hne
  obtain ⟨n, a, ha, hn⟩ := hincomp b.val.1 c.val.1 hne
  have hb := realizations_transport hh (type b.val.1) (original b.val.1) b.val.2
  have hc := realizations_transport hh (type c.val.1) (original c.val.1) c.val.2
  have heq := equal_weight_realizations size type K b c hweight
  apply hn
  apply (hc n a).mpr
  rw [← heq]
  exact (hb n a).mp ha

end CombinedRamsey.Negative
