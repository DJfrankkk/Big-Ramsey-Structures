import RelationalRamsey632.Transfer.Source
import Generic3Ramsey.Palette

namespace RelationalRamsey632.Transfer

open RelStructure

variable {L S : Language} {X M A : Type}

/-- Reducing an expanded embedding, while transporting the two reduct
equalities, preserves its underlying function exactly. -/
def toBaseEmbedding (ι : LanguageInclusion L S)
    {a : RelStructure L A} {p : RelStructure S A}
    {B : RelStructure L M} {N : RelStructure S M}
    (ha : p.reduct ι = a) (hN : N.reduct ι = B)
    (u : RelEmbedding p N) : RelEmbedding a B where
  toFun := u
  injective := u.injective
  map_rel {r} R t := by
    have h := u.map_rel (ι.relMap r R) t
    change (p.reduct ι).rel R t ↔ (N.reduct ι).rel R (u ∘ t) at h
    simpa [ha, hN] using h

theorem palette_reduct (ι : LanguageInclusion L S)
    {a : RelStructure L A} {K : RelStructure L X} {Z : RelStructure S X}
    (hZ : Z.reduct ι = K) {p : RelStructure S A}
    (hp : p ∈ palette a K Z) : p.reduct ι = a := by
  obtain ⟨e, rfl⟩ := hp
  rw [reduct_pullback, hZ]
  exact e.pullback_eq

/-- The source-canonization conclusion obtained from the paper's source
degree-one premise. The finite palette consists of complete actual tables. -/
theorem source_canonization (ι : LanguageInclusion L S)
    {a : RelStructure L A} [Finite A]
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (hN : N.reduct ι = B) {ψ : M → X} (hψ : Approximate K B ψ)
    (i : RelEmbedding K B) (ha : Nonempty (RelEmbedding a K))
    (hfin : (palette a K (N.pullback i)).Finite)
    (hR : ∀ p ∈ palette a K (N.pullback i), SourceDegreeOne N p)
    (D : Type) [Fintype D] (c : RelEmbedding a K → D) :
    ∃ g : RelEmbedding K K,
      ∃ d : palette a K (N.pullback i) → D,
        ∀ e : RelEmbedding a K,
          c (g.comp e) = d ⟨(N.pullback i).pullback e, ⟨e, rfl⟩⟩ := by
  classical
  let Z := N.pullback i
  have hZ : Z.reduct ι = K := by
    rw [reduct_pullback, hN]
    exact i.pullback_eq
  let P := palette a K Z
  letI : Fintype P := hfin.fintype
  let color : ∀ p : P, RelEmbedding p.val N → D :=
    fun p u => c (approximateEmbedding hψ ha
      (toBaseEmbedding ι (palette_reduct ι hZ p.property) hN u))
  obtain ⟨ζ, hζ⟩ := simultaneous_source N (fun p : P => p.val)
    (fun p => hR p.val p.property) color
  let ζb : RelEmbedding B B := toBaseEmbedding ι hN hN ζ
  let g := approximateComp hψ (ζb.comp i)
  have hex : ∀ p : P, Nonempty (RelEmbedding p.val N) := by
    intro p
    obtain ⟨e, he⟩ := p.property
    have hi := RelEmbedding.pullback N (i.comp e) (i.comp e).injective
    change RelEmbedding (N.pullback (i.comp e)) N at hi
    have he' : N.pullback (i.comp e) = p.val := he
    rw [he'] at hi
    exact ⟨hi⟩
  let witness : ∀ p : P, RelEmbedding p.val N := fun p => Classical.choice (hex p)
  refine ⟨g, fun p => color p (ζ.comp (witness p)), ?_⟩
  intro e
  let p : P := ⟨Z.pullback e, ⟨e, rfl⟩⟩
  let u : RelEmbedding p.val N :=
    RelEmbedding.pullback N (i.comp e) (i.comp e).injective
  have heq : approximateEmbedding hψ ha
      (toBaseEmbedding ι (palette_reduct ι hZ p.property) hN (ζ.comp u))
      = g.comp e := by
    ext x
    rfl
  have hc := hζ p u (witness p)
  change color p (ζ.comp u) = color p (ζ.comp (witness p)) at hc
  rw [show color p (ζ.comp u) = c (g.comp e) by
    change c (approximateEmbedding hψ ha
      (toBaseEmbedding ι (palette_reduct ι hZ p.property) hN (ζ.comp u))) = _
    rw [heq]] at hc
  exact hc

/-- Actual embedding-degree bounds, parameterized by a nonnegative integer. -/
def EmbeddingDegreeBound {A X : Type} {L : Language}
    (a : RelStructure L A) (K : RelStructure L X) (t : ℕ) : Prop :=
  Generic3Ramsey.Palette.DegreeBound
    (fun (g : RelEmbedding K K) (e : RelEmbedding a K) => g.comp e) t

theorem source_degree_bound (ι : LanguageInclusion L S)
    {a : RelStructure L A} [Finite A]
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (hN : N.reduct ι = B) {ψ : M → X} (hψ : Approximate K B ψ)
    (i : RelEmbedding K B) (ha : Nonempty (RelEmbedding a K))
    (hfin : (palette a K (N.pullback i)).Finite)
    (hR : ∀ p ∈ palette a K (N.pullback i), SourceDegreeOne N p) :
    EmbeddingDegreeBound a K (palette a K (N.pullback i)).ncard := by
  classical
  letI : Fintype (palette a K (N.pullback i)) := hfin.fintype
  have h := Generic3Ramsey.Palette.canonicalization_degreeBound
    (fun (g : RelEmbedding K K) (e : RelEmbedding a K) => g.comp e)
    (fun e => (⟨(N.pullback i).pullback e, ⟨e, rfl⟩⟩ : palette a K (N.pullback i)))
    (fun D _ c => source_canonization ι hN hψ i ha hfin hR D c)
  simpa only [EmbeddingDegreeBound, Set.fintypeCard_eq_ncard] using h

end RelationalRamsey632.Transfer
