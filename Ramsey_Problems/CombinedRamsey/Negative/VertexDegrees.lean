import CombinedRamsey.Negative.PersistenceTypes
import RelationalRamsey632.Transfer.CopyDegrees

/-! Infinite embedding and actual finite-subset copy degrees, and the
obstruction to precompact singleton degree-one expansions. -/

namespace CombinedRamsey.Negative

open RelationalRamsey632 RelationalRamsey632.Transfer

variable {L S : Language} {X A : Type}

def HasPointType (K : RelStructure L X) (δ : RelStructure L (Fin 1)) (x : X) : Prop :=
  K.pullback (fun _ : Fin 1 => x) = δ

def PersistentVertexColourings (K : RelStructure L X)
    (δ : RelStructure L (Fin 1)) : Prop :=
  ∀ r, ∃ χ : X → Fin (r + 1), ∀ (f : RelEmbedding K K) i,
    ∃ x, HasPointType K δ x ∧ χ (f x) = i

theorem hasPointType_embedding {a : RelStructure L A} {K : RelStructure L X}
    (e : RelEmbedding a K) (δ : RelStructure L (Fin 1)) (x : A) :
    HasPointType a δ x ↔ HasPointType K δ (e x) := by
  have he : K.pullback (fun _ : Fin 1 => e x) = a.pullback (fun _ : Fin 1 => x) :=
    congrArg (fun z => z.pullback (fun _ : Fin 1 => x)) e.pullback_eq
  unfold HasPointType
  rw [he]

def singletonEmbedding {K : RelStructure L X} {δ : RelStructure L (Fin 1)}
    (x : X) (hx : HasPointType K δ x) : RelEmbedding δ K where
  toFun := fun _ => x
  injective := fun _ _ _ => Subsingleton.elim _ _
  map_rel R t := by
    change δ.rel R t ↔ K.rel R ((fun _ : Fin 1 => x) ∘ t)
    rw [← hx]
    rfl

/-- Finite homogeneity supplies an embedding of every finite age member
through every vertex of the prescribed singleton type. -/
theorem vertex_extension {K : RelStructure L X} (hh : FiniteEmbeddingHomogeneous K)
    {a : RelStructure L A} [Finite A] (ha : Nonempty (RelEmbedding a K))
    {δ : RelStructure L (Fin 1)} (v : A) (hv : HasPointType a δ v)
    (x : X) (hx : HasPointType K δ x) :
    ∃ e : RelEmbedding a K, e v = x := by
  obtain ⟨u⟩ := ha
  let p := singletonEmbedding (u v) ((hasPointType_embedding u δ v).mp hv)
  let q := singletonEmbedding x hx
  obtain ⟨g, hg⟩ := hh (Fin 1) δ p q
  exact ⟨g.comp u, hg 0⟩

theorem no_finite_embedding_degree {K : RelStructure L X}
    {δ : RelStructure L (Fin 1)} (hp : PersistentVertexColourings K δ)
    (hh : FiniteEmbeddingHomogeneous K)
    {a : RelStructure L A} [Finite A] (ha : Nonempty (RelEmbedding a K))
    (v : A) (hv : HasPointType a δ v) :
    ∀ t, ¬ EmbeddingDegreeBound a K t := by
  intro t hbound
  obtain ⟨χ, hχ⟩ := hp t
  have hs : ∀ f : RelEmbedding K K,
      Function.Surjective (fun e : RelEmbedding a K => χ ((f.comp e) v)) := by
    intro f i
    obtain ⟨x, hx, hi⟩ := hχ f i
    obtain ⟨e, he⟩ := vertex_extension hh ha v hv x hx
    exact ⟨e, by simpa only [RelEmbedding.comp_apply, he] using hi⟩
  have ht := RamseyCommon.Palette.unavoidable_degree_lowerBound
    (fun (f : RelEmbedding K K) (e : RelEmbedding a K) => f.comp e)
    (fun e => χ (e v)) hs hbound
  simp only [Fintype.card_fin] at ht
  omega

noncomputable def pointTypeVertices [Fintype A] (a : RelStructure L A)
    (δ : RelStructure L (Fin 1)) : Finset A := by
  classical
  exact Finset.univ.filter (HasPointType a δ)

noncomputable def vertexColourSet [Fintype A] {a : RelStructure L A}
    {K : RelStructure L X} (δ : RelStructure L (Fin 1))
    {C : Type} [DecidableEq C] (χ : X → C) (e : RelEmbedding a K) : Finset C := by
  classical
  exact (Finset.univ.filter (HasPointType a δ)).image (χ ∘ e)

theorem vertexColourSet_card_le [Fintype A] {a : RelStructure L A}
    {K : RelStructure L X} (δ : RelStructure L (Fin 1))
    {C : Type} [DecidableEq C] (χ : X → C) (e : RelEmbedding a K) :
    (vertexColourSet δ χ e).card ≤
      (pointTypeVertices a δ).card := by
  classical
  exact Finset.card_image_le

theorem vertexColourSet_eq_of_same_range [Fintype A] {a : RelStructure L A}
    {K : RelStructure L X} (δ : RelStructure L (Fin 1))
    {C : Type} [DecidableEq C] (χ : X → C) (e f : RelEmbedding a K)
    (hr : Set.range e = Set.range f) : vertexColourSet δ χ e = vertexColourSet δ χ f := by
  classical
  suffices ∀ (e f : RelEmbedding a K), Set.range e ⊆ Set.range f →
      vertexColourSet δ χ e ⊆ vertexColourSet δ χ f by
    exact Finset.Subset.antisymm (this e f hr.subset) (this f e hr.symm.subset)
  intro e f hr c hc
  obtain ⟨x, hx, hcol⟩ := Finset.mem_image.mp hc
  obtain ⟨y, hy⟩ := hr (Set.mem_range_self x)
  have htype : HasPointType a δ y :=
    (hasPointType_embedding f δ y).mpr (hy ▸ (hasPointType_embedding e δ x).mp
      (Finset.mem_filter.mp hx).2)
  exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, htype⟩,
    by simpa only [Function.comp_apply, hy] using hcol⟩

noncomputable def vertexCopyColour [Fintype A] {a : RelStructure L A}
    {K : RelStructure L X} (δ : RelStructure L (Fin 1))
    {C : Type} [DecidableEq C] (χ : X → C) (F : Copies a K) : Finset C :=
  vertexColourSet δ χ (copyWitness F)

theorem vertexCopyColour_copyOf [Fintype A] {a : RelStructure L A}
    {K : RelStructure L X} (δ : RelStructure L (Fin 1))
    {C : Type} [DecidableEq C] (χ : X → C) (e : RelEmbedding a K) :
    vertexCopyColour δ χ (copyOf e) = vertexColourSet δ χ e :=
  vertexColourSet_eq_of_same_range δ χ _ _ (copyWitness_range (copyOf e))

/-- The paper's exact `q ≤ k t` counting step uses actual copies, with `k`
the number of vertices of singleton type δ in A. -/
theorem copy_degree_colour_count [Fintype A] {a : RelStructure L A}
    {K : RelStructure L X} {δ : RelStructure L (Fin 1)}
    (hh : FiniteEmbeddingHomogeneous K) (ha : Nonempty (RelEmbedding a K))
    (v : A) (hv : HasPointType a δ v) {r t : ℕ}
    (χ : X → Fin (r + 1))
    (hχ : ∀ (f : RelEmbedding K K) i, ∃ x, HasPointType K δ x ∧ χ (f x) = i)
    (hbound : CopyDegreeBound a K t) :
    r + 1 ≤ (pointTypeVertices a δ).card * t := by
  classical
  obtain ⟨g, colors, hcard, hcolors⟩ := hbound (Finset (Fin (r + 1))) (vertexCopyColour δ χ)
  let used : Finset (Finset (Fin (r + 1))) :=
    colors.filter (fun s => ∃ F : Copies a K, vertexCopyColour δ χ (copyMap g F) = s)
  have hused : used.card ≤ t := (Finset.card_filter_le colors _).trans hcard
  have hsmall : ∀ s ∈ used, s.card ≤ (pointTypeVertices a δ).card := by
    intro s hs
    obtain ⟨F, rfl⟩ := (Finset.mem_filter.mp hs).2
    exact vertexColourSet_card_le δ χ (copyWitness (copyMap g F))
  have hcover : (Finset.univ : Finset (Fin (r + 1))) ⊆ used.biUnion id := by
    intro i _
    obtain ⟨x, hx, hi⟩ := hχ g i
    obtain ⟨e, he⟩ := vertex_extension hh ha v hv x hx
    let s := vertexCopyColour δ χ (copyMap g (copyOf e))
    have hs : s ∈ used := Finset.mem_filter.mpr
      ⟨hcolors (copyOf e), ⟨copyOf e, rfl⟩⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨s, hs, ?_⟩
    change i ∈ vertexCopyColour δ χ (copyMap g (copyOf e))
    rw [copyMap_of, vertexCopyColour_copyOf]
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩,
      by simpa only [Function.comp_apply, RelEmbedding.comp_apply, he] using hi⟩
  calc
    r + 1 = (Finset.univ : Finset (Fin (r + 1))).card := (Fintype.card_fin _).symm
    _ ≤ (used.biUnion id).card := Finset.card_le_card hcover
    _ ≤ ∑ s ∈ used, s.card := Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ used, (pointTypeVertices a δ).card := Finset.sum_le_sum hsmall
    _ = (pointTypeVertices a δ).card * used.card := by simp [Nat.mul_comm]
    _ ≤ (pointTypeVertices a δ).card * t := Nat.mul_le_mul_left _ hused

theorem no_finite_copy_degree {K : RelStructure L X}
    {δ : RelStructure L (Fin 1)} (hp : PersistentVertexColourings K δ)
    (hh : FiniteEmbeddingHomogeneous K)
    {a : RelStructure L A} [Finite A] (ha : Nonempty (RelEmbedding a K))
    (v : A) (hv : HasPointType a δ v) : ∀ t, ¬ CopyDegreeBound a K t := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  intro t hbound
  let k := (pointTypeVertices a δ).card
  obtain ⟨χ, hχ⟩ := hp (k * t)
  have h := copy_degree_colour_count hh ha v hv χ hχ hbound
  change k * t + 1 ≤ k * t at h
  omega

theorem no_precompact_singleton_degree_one_expansion {K : RelStructure L X}
    {δ : RelStructure L (Fin 1)} (hp : PersistentVertexColourings K δ)
    (hh : FiniteEmbeddingHomogeneous K) (ha : Nonempty (RelEmbedding δ K))
    (ι : LanguageInclusion L S) (Z : RelStructure S X) (hZ : Z.reduct ι = K)
    (hfin : (RelStructure.palette δ K Z).Finite)
    (hR : ∀ p ∈ RelStructure.palette δ K Z, SourceDegreeOne Z p) : False := by
  have hid : Approximate K K id := by
    intro F _ a _ e
    exact ⟨e.injective, fun _ R t => e.map_rel R t⟩
  have hbound := source_degree_bound ι hZ hid (RelationalRamsey632.RelEmbedding.refl K) ha hfin hR
  have hself : HasPointType δ δ (0 : Fin 1) := by
    have heq : (fun _ : Fin 1 => (0 : Fin 1)) = id := by
      funext x
      exact Subsingleton.elim _ _
    rw [HasPointType, heq]
    rfl
  exact no_finite_embedding_degree hp hh ha 0 hself _ hbound

end CombinedRamsey.Negative

