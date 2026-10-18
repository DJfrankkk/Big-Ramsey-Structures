import RelationalRamsey632.Transfer.SupportTransport
import RelationalRamsey632.Transfer.Minimization

namespace RelationalRamsey632.Transfer

open RelStructure
open scoped BigOperators

variable {L S : Language} {X M : Type}

instance finite_relEmbedding {A B : Type} [Finite A] [Finite B]
    {a : RelStructure L A} {b : RelStructure L B} : Finite (RelEmbedding a b) :=
  Finite.of_injective (fun e : RelEmbedding a b => e.toFun)
    (fun _ _ h => RelEmbedding.ext (fun x => congrFun h x))

def Determines {J : Type} {A : J → Type}
    (a : ∀ j, RelStructure L (A j)) (K : RelStructure L X)
    (Y : RelStructure S X) : Prop :=
  ∀ (F : Type) [Finite F] (b : RelStructure L F), Nonempty (RelEmbedding b K) →
    ∀ p ∈ palette b K Y, ∀ q ∈ palette b K Y,
      (∀ j (h : RelEmbedding (a j) b), p.pullback h = q.pullback h) → p = q

theorem determination_pullback {J : Type} {A : J → Type}
    (a : ∀ j, RelStructure L (A j)) (K : RelStructure L X)
    (Y : RelStructure S X) (hD : Determines a K Y) (η : RelEmbedding K K) :
    Determines a K (Y.pullback η) := by
  intro F _ b hb p hp q hq h
  exact hD F b hb p (palette_pullback_subset b K Y η hp)
    q (palette_pullback_subset b K Y η hq) h

/-- Finite determination really makes every complete finite palette finite,
even in a language with infinitely many symbols at a fixed arity. -/
theorem finite_palette_of_determination {J : Type} [Finite J]
    {A : J → Type} [∀ j, Finite (A j)]
    (a : ∀ j, RelStructure L (A j)) (K : RelStructure L X)
    (Y : RelStructure S X) (hfin : ∀ j, (palette (a j) K Y).Finite)
    (hD : Determines a K Y)
    {F : Type} [Finite F] (b : RelStructure L F) (hb : Nonempty (RelEmbedding b K)) :
    (palette b K Y).Finite := by
  classical
  letI : ∀ j, Finite (palette (a j) K Y) := fun j => (hfin j).to_subtype
  let restrict : palette b K Y → ∀ j, RelEmbedding (a j) b → palette (a j) K Y :=
    fun p j h => ⟨p.val.pullback h, by
      obtain ⟨e, he⟩ := p.property
      exact ⟨e.comp h, congrArg (fun q => q.pullback h) he⟩⟩
  have hinj : Function.Injective restrict := by
    intro p q hpq
    apply Subtype.ext
    apply hD F b hb p.val p.property q.val q.property
    intro j h
    exact congrArg Subtype.val (congrFun (congrFun hpq j) h)
  letI : Finite (palette b K Y) := Finite.of_injective restrict hinj
  exact Set.toFinite _

/-- The explicit product bound of Section 5. Finite determination embeds
the full labelled palette into the product of all selected restriction
tables. Only finite domains, rather than finiteness of the base language
or its isomorphism types at a size, are used. -/
theorem palette_card_bound {J : Type} [Fintype J]
    {A : J → Type} [∀ j, Finite (A j)]
    (a : ∀ j, RelStructure L (A j)) (K : RelStructure L X)
    (Y : RelStructure S X) (hfin : ∀ j, (palette (a j) K Y).Finite)
    (hD : Determines a K Y)
    {F : Type} [Finite F] (b : RelStructure L F) (hb : Nonempty (RelEmbedding b K)) :
    1 ≤ (palette b K Y).ncard ∧
      (palette b K Y).ncard ≤
        ∏ j, (palette (a j) K Y).ncard ^ Nat.card (RelEmbedding (a j) b) := by
  classical
  have hfinB := finite_palette_of_determination a K Y hfin hD b hb
  letI : ∀ j, Fintype (palette (a j) K Y) := fun j => (hfin j).fintype
  letI : Fintype (palette b K Y) := hfinB.fintype
  letI : ∀ j, Fintype (RelEmbedding (a j) b) := fun _ => Fintype.ofFinite _
  let restrict : palette b K Y → ∀ j, RelEmbedding (a j) b → palette (a j) K Y :=
    fun p j h => ⟨p.val.pullback h, by
      obtain ⟨e, he⟩ := p.property
      exact ⟨e.comp h, congrArg (fun q => q.pullback h) he⟩⟩
  have hinj : Function.Injective restrict := by
    intro p q hpq
    apply Subtype.ext
    apply hD F b hb p.val p.property q.val q.property
    intro j h
    exact congrArg Subtype.val (congrFun (congrFun hpq j) h)
  constructor
  · have hnonempty : (palette b K Y).Nonempty := by
      let e := Classical.choice hb
      exact ⟨Y.pullback e, e, rfl⟩
    exact Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos hfinB).mpr hnonempty).ne'
  · have hcard := Fintype.card_le_of_injective restrict hinj
    have htables : Fintype.card (∀ j, RelEmbedding (a j) b → palette (a j) K Y) =
        ∏ j, Fintype.card (palette (a j) K Y) ^ Fintype.card (RelEmbedding (a j) b) := by
      rw [Fintype.card_pi]
      apply Finset.prod_congr rfl
      intro j _
      exact Fintype.card_fun
    rw [htables] at hcard
    simpa only [Nat.card_eq_fintype_card, Set.fintypeCard_eq_ncard] using hcard

/-- Preserving every selected type lifts to preservation of the complete
expanded structure precisely under the finite-determination premise. -/
theorem preserves_family_full_embedding {J : Type} {A : J → Type}
    (a : ∀ j, RelStructure L (A j)) (K : RelStructure L X)
    (Y : RelStructure S X) (hD : Determines a K Y)
    (g : RelEmbedding K K) (hg : PreservesFamily a K Y g) :
    IsEmbeddingMap Y Y g := by
  classical
  have hfull : ∀ (F : Type) [Finite F] (b : RelStructure L F)
      (e : RelEmbedding b K), Y.pullback (g.comp e) = Y.pullback e := by
    intro F _ b e
    apply hD F b ⟨e⟩ (Y.pullback (g.comp e)) ⟨g.comp e, rfl⟩
      (Y.pullback e) ⟨e, rfl⟩
    intro j h
    exact hg j (e.comp h)
  refine ⟨g.injective, ?_⟩
  intro r R t
  let F : Set X := Set.range t
  have hF : F.Finite := by
    simpa [F] using (Set.finite_univ : (Set.univ : Set (Fin r)).Finite).image t
  letI : Finite F := hF.to_subtype
  let b := K.pullback (Subtype.val : F → X)
  let e := RelEmbedding.pullback K (Subtype.val : F → X) Subtype.val_injective
  let s : Fin r → F := fun j => ⟨t j, ⟨j, rfl⟩⟩
  have h := congrArg (fun p : RelStructure S F => p.rel R s) (hfull F b e)
  exact h.symm.to_iff

/-- The recurrence implication of the finite-transfer theorem, with source
degree one derived in the proof rather than supplied as a cofinality oracle. -/
theorem finite_transfer_recurrence (ι : LanguageInclusion L S)
    {J : Type} [Fintype J] {A : J → Type} [∀ j, Finite (A j)]
    (a : ∀ j, RelStructure L (A j))
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (hN : N.reduct ι = B) {ψ : M → X} (hψ : Approximate K B ψ)
    (φ : RelEmbedding K B) (ha : ∀ j, Nonempty (RelEmbedding (a j) K))
    (hfin : ∀ j, (palette (a j) K (N.pullback φ)).Finite)
    (hD : Determines a K (N.pullback φ))
    (hR : ∀ j p, p ∈ palette (a j) K (N.pullback φ) → SourceDegreeOne N p) :
    ∃ η : RelEmbedding K K,
      Determines a K (N.pullback (φ.comp η)) ∧
      (∀ (F : Type) [Finite F] (b : RelStructure L F)
        (_hb : Nonempty (RelEmbedding b K)), (palette b K (N.pullback (φ.comp η))).Finite) ∧
      ∀ α : RelEmbedding K K, ∃ β : RelEmbedding K K,
        IsEmbeddingMap (N.pullback (φ.comp η)) (N.pullback (φ.comp η)) (α.comp β) := by
  obtain ⟨η, hmin⟩ := minimum_palette_rank a K (N.pullback φ)
  have hu := minimizing_palettes_unavoidable a K (N.pullback φ) hfin η hmin
  have hDη := determination_pullback a K (N.pullback φ) hD η
  have hs : ∀ j, palette (a j) K (N.pullback (φ.comp η)) ⊆ palette (a j) K (N.pullback φ) :=
    fun j => palette_pullback_subset (a j) K (N.pullback φ) η
  have hfinη := fun j => (hfin j).subset (hs j)
  refine ⟨η, hDη, ?_, ?_⟩
  · intro F _ b hb
    exact finite_palette_of_determination a K (N.pullback (φ.comp η)) hfinη hDη b hb
  · intro α
    obtain ⟨β, hβ⟩ := coarse_recurrence ι a hN hψ (φ.comp η) ha hfinη hu
      (fun j p hp => hR j p (hs j hp)) α
    exact ⟨β, preserves_family_full_embedding a K (N.pullback (φ.comp η)) hDη (α.comp β) hβ⟩

/-- The support test identifies full Y-types only inside the original
palette. It does not promote arbitrary supported source pullbacks. -/
theorem support_full_palette_criterion (ι : LanguageInclusion L S)
    {J : Type} [Fintype J] {A : J → Type} [∀ j, Finite (A j)]
    (a : ∀ j, RelStructure L (A j))
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (hN : N.reduct ι = B) {ψ : M → X} (hψ : Approximate K B ψ)
    (i φ : RelEmbedding K B) (ha : ∀ j, Nonempty (RelEmbedding (a j) K))
    (hfin : ∀ j, (palette (a j) K (N.pullback i)).Finite)
    (hunav : ∀ j, Unavoidable (a j) K (N.pullback i))
    (hR : ∀ j p, p ∈ palette (a j) K (N.pullback i) → SourceDegreeOne N p)
    (hsub : ∀ (F : Type) [Finite F] (b : RelStructure L F),
      palette b K (N.pullback i) ⊆ palette b K (N.pullback φ))
    (hD : Determines a K (N.pullback φ))
    {F : Type} [Finite F] (b : RelStructure L F) (hb : Nonempty (RelEmbedding b K))
    (p : RelStructure S F) :
    p ∈ palette b K (N.pullback i) ↔
      p ∈ palette b K (N.pullback φ) ∧
        ∀ j (h : RelEmbedding (a j) b),
          p.pullback h ∈ palette (a j) K (N.pullback i) := by
  constructor
  · intro hp
    refine ⟨hsub F b hp, ?_⟩
    obtain ⟨e, he⟩ := hp
    intro j h
    exact ⟨e.comp h, congrArg (fun z => z.pullback h) he⟩
  · rintro ⟨hp, hsmall⟩
    obtain ⟨Q, hQ, hret⟩ := support_return_map ι a hN hψ i ha hfin hunav hR
    obtain ⟨e, he⟩ := hp
    let u := φ.comp e
    let v := approximateEmbedding hQ hb u
    have hv : (N.pullback i).pullback v ∈ palette b K (N.pullback φ) :=
      hsub F b ⟨v, rfl⟩
    have heq : (N.pullback i).pullback v = p := by
      apply hD F b hb _ hv p ⟨e, he⟩
      intro j h
      have hh : N.pullback (u.comp h) ∈ palette (a j) K (N.pullback i) := by
        change (N.pullback u).pullback h ∈ palette (a j) K (N.pullback i)
        have he' : N.pullback u = p := he
        rw [he']
        exact hsmall j h
      have hret' := hret j (u.comp h) hh
      have he' : N.pullback u = p := he
      exact hret'.trans (congrArg (fun z => z.pullback h) he')
    exact ⟨v, heq⟩

/-- Under finite determination the explicitly certified factorial return
power is an embedding of the full expansion, including every relation
symbol and every repeated-coordinate tuple. -/
theorem determined_factorial_return (ι : LanguageInclusion L S)
    {J : Type} [Fintype J] {A : J → Type} [∀ j, Finite (A j)]
    (a : ∀ j, RelStructure L (A j))
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (hN : N.reduct ι = B) {ψ : M → X} (hψ : Approximate K B ψ)
    (i : RelEmbedding K B) (ha : ∀ j, Nonempty (RelEmbedding (a j) K))
    (hfin : ∀ j, (palette (a j) K (N.pullback i)).Finite)
    (hunav : ∀ j, Unavoidable (a j) K (N.pullback i))
    (hR : ∀ j p, p ∈ palette (a j) K (N.pullback i) → SourceDegreeOne N p)
    (hD : Determines a K (N.pullback i)) (α : RelEmbedding K K) :
    ∃ h : RelEmbedding K K,
      IsEmbeddingMap (N.pullback i) (N.pullback i)
        (embeddingIterate (α.comp h) (∑ j, (palette (a j) K (N.pullback i)).ncard).factorial) ∧
      ∃ β : RelEmbedding K K,
        embeddingIterate (α.comp h) (∑ j, (palette (a j) K (N.pullback i)).ncard).factorial
          = α.comp β := by
  obtain ⟨h, hp, β, heq⟩ := coarse_recurrence_quantitative ι a hN hψ i ha hfin hunav hR α
  exact ⟨h, preserves_family_full_embedding a K (N.pullback i) hD _ hp, β, heq⟩

end RelationalRamsey632.Transfer
