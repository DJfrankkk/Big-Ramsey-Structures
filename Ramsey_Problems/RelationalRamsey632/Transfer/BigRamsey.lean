import RelationalRamsey632.Transfer.AgeTransport
import RelationalRamsey632.Transfer.Rigidity

namespace RelationalRamsey632.Transfer

open RelStructure

variable {L S : Language} {X M F : Type}

def ExactEmbeddingDegree {A X : Type} {L : Language}
    (a : RelStructure L A) (K : RelStructure L X) (t : ℕ) : Prop :=
  EmbeddingDegreeBound a K t ∧ ∀ s, EmbeddingDegreeBound a K s → t ≤ s

theorem type_coloring_surjective {a : RelStructure L F} {K : RelStructure L X}
    (Y : RelStructure S X) (hu : Unavoidable a K Y) (α : RelEmbedding K K) :
    Function.Surjective (fun e : RelEmbedding a K =>
      (⟨Y.pullback (α.comp e), ⟨α.comp e, rfl⟩⟩ : palette a K Y)) := by
  intro p
  have hp : p.val ∈ palette a K (Y.pullback α) := by
    rw [hu α]
    exact p.property
  obtain ⟨e, he⟩ := hp
  exact ⟨e, Subtype.ext he⟩

theorem exact_degree_from_source_stage (ι : LanguageInclusion L S)
    {a : RelStructure L F} [Finite F]
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (hN : N.reduct ι = B) {ψ : M → X} (hψ : Approximate K B ψ)
    (i : RelEmbedding K B) (ha : Nonempty (RelEmbedding a K))
    (hfin : (palette a K (N.pullback i)).Finite)
    (hR : ∀ p ∈ palette a K (N.pullback i), SourceDegreeOne N p)
    (Y : RelStructure S X)
    (htypes : ∀ e : RelEmbedding a K, Y.pullback e = (N.pullback i).pullback e)
    (hu : Unavoidable a K Y) :
    (palette a K Y).Finite ∧
      ExactEmbeddingDegree a K (palette a K Y).ncard ∧
      ∀ (D : Type) [Fintype D] (c : RelEmbedding a K → D),
        ∃ g : RelEmbedding K K, ∃ d : palette a K Y → D,
          ∀ e, c (g.comp e) = d ⟨Y.pullback e, ⟨e, rfl⟩⟩ := by
  classical
  have hp : palette a K Y = palette a K (N.pullback i) :=
    congrArg Set.range (funext htypes)
  have hYfin : (palette a K Y).Finite := hp ▸ hfin
  letI : Fintype (palette a K Y) := hYfin.fintype
  have hcanon : ∀ (D : Type) [Fintype D] (c : RelEmbedding a K → D),
      ∃ g : RelEmbedding K K, ∃ d : palette a K Y → D,
        ∀ e, c (g.comp e) = d ⟨Y.pullback e, ⟨e, rfl⟩⟩ := by
    intro D _ c
    obtain ⟨g, d, hd⟩ := source_canonization ι hN hψ i ha hfin hR D c
    let dY : palette a K Y → D :=
      fun p => d ⟨p.val, hp ▸ p.property⟩
    refine ⟨g, dY, ?_⟩
    intro e
    rw [hd e]
    apply congrArg d
    apply Subtype.ext
    exact (htypes e).symm
  have hexact := Generic3Ramsey.Palette.exact_degree_of_canonicalization
    (fun (g : RelEmbedding K K) (e : RelEmbedding a K) => g.comp e)
    (fun e => (⟨Y.pullback e, ⟨e, rfl⟩⟩ : palette a K Y))
    (type_coloring_surjective Y hu) hcanon
  refine ⟨hYfin, ?_, hcanon⟩
  simpa only [ExactEmbeddingDegree, EmbeddingDegreeBound, Set.fintypeCard_eq_ncard]
    using hexact

theorem source_palette_rigid [Countable M]
    {a : RelStructure L F} [Finite F]
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (i : RelEmbedding K B)
    (hR : ∀ p ∈ palette a K (N.pullback i), SourceDegreeOne N p) :
    ∀ p ∈ palette a K (N.pullback i), Rigid p := by
  intro p hp
  have hr := hR p hp
  obtain ⟨e, he⟩ := hp
  have u := RelEmbedding.pullback N (i.comp e) (i.comp e).injective
  have he' : N.pullback (i.comp e) = p := he
  rw [he'] at u
  exact source_rigid ⟨u⟩ hr

/-- Exact structural big Ramsey expansion: finite unavoidable full
palettes, source-derived canonization, exact embedding degrees, minimum
attainment in the original pullback, and rigidity for every finite A. -/
theorem countable_big_ramsey_expansion (ι : LanguageInclusion L S)
    [Countable X] [Countable M]
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (hN : N.reduct ι = B) {ψ : M → X} (hψ : Approximate K B ψ)
    (φ : RelEmbedding K B) (hsource : PrecompactSource N φ) :
    ∃ Y : RelStructure S X, Y.reduct ι = K ∧
      ∀ (F : Type) [Finite F] (a : RelStructure L F)
        (_ha : Nonempty (RelEmbedding a K)),
        (palette a K Y).Finite ∧ Unavoidable a K Y ∧
        ExactEmbeddingDegree a K (palette a K Y).ncard ∧
        (∀ η : RelEmbedding K K,
          (palette a K Y).ncard ≤ (palette a K (N.pullback (φ.comp η))).ncard) ∧
        (∃ η : RelEmbedding K K,
          (palette a K Y).ncard = (palette a K (N.pullback (φ.comp η))).ncard) ∧
        (∀ p ∈ palette a K Y, Rigid p) ∧
        ∀ (D : Type) [Fintype D] (c : RelEmbedding a K → D),
          ∃ g : RelEmbedding K K, ∃ d : palette a K Y → D,
            ∀ e, c (g.comp e) = d ⟨Y.pullback e, ⟨e, rfl⟩⟩ := by
  classical
  obtain ⟨A, a, hA, ha, hcover⟩ := countable_age_cover K
  letI : ∀ j, Finite (A j) := hA
  obtain ⟨η, Y, hYK, _, _, _, htypes, hunav⟩ :=
    uniform_stabilized_expansion ι a hN hψ φ hsource ha
  refine ⟨Y, hYK, ?_⟩
  intro F _ b hb
  obtain ⟨j, u, hu⟩ := hcover F b hb
  let i := φ.comp (η (j + 1))
  have hbtypes : ∀ e : RelEmbedding b K,
      Y.pullback e = (N.pullback i).pullback e :=
    full_types_transfer u hu Y (N.pullback i) (htypes j)
  have hbunav := unavoidable_transfer u hu Y (hunav j)
  obtain ⟨hfin, hR⟩ := precompact_source_pullback hsource (η (j + 1)) F b hb
  obtain ⟨hYfin, hexact, hcanon⟩ :=
    exact_degree_from_source_stage ι hN hψ i hb hfin hR Y hbtypes hbunav
  have hp : palette b K Y = palette b K (N.pullback i) :=
    congrArg Set.range (funext hbtypes)
  refine ⟨hYfin, hbunav, hexact, ?_, ⟨η (j + 1), congrArg Set.ncard hp⟩, ?_, hcanon⟩
  · intro α
    obtain ⟨hαfin, hαR⟩ := precompact_source_pullback hsource α F b hb
    exact hexact.2 _ (source_degree_bound ι hN hψ (φ.comp α) hb hαfin hαR)
  · intro p hpy
    exact source_palette_rigid i hR p (hp ▸ hpy)

end RelationalRamsey632.Transfer
