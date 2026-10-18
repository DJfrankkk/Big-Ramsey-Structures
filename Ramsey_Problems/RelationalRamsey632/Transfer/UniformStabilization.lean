import RelationalRamsey632.Transfer.Minimization

namespace RelationalRamsey632.Transfer

open RelStructure

variable {L S : Language} {X M : Type}

/-- All source premises concern actual full finite pullback tables. -/
def PrecompactSource {K : RelStructure L X} {B : RelStructure L M}
    (N : RelStructure S M) (φ : RelEmbedding K B) : Prop :=
  ∀ (F : Type) [Finite F] (b : RelStructure L F),
    Nonempty (RelEmbedding b K) →
      (palette b K (N.pullback φ)).Finite ∧
      ∀ p ∈ palette b K (N.pullback φ), SourceDegreeOne N p

theorem precompact_source_pullback {K : RelStructure L X} {B : RelStructure L M}
    {N : RelStructure S M} {φ : RelEmbedding K B}
    (hsource : PrecompactSource N φ) (η : RelEmbedding K K) :
    PrecompactSource N (φ.comp η) := by
  intro F _ b hb
  obtain ⟨hfin, hR⟩ := hsource F b hb
  have hs := palette_pullback_subset b K (N.pullback φ) η
  exact ⟨hfin.subset hs, fun p hp => hR p (hs hp)⟩

/-- A finite-stage minimization can be refined to preserve every earlier
selected type on every embedding, not merely on a finite sample. -/
theorem uniform_stage_step (ι : LanguageInclusion L S)
    {A : ℕ → Type} [∀ j, Finite (A j)] (a : ∀ j, RelStructure L (A j))
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (hN : N.reduct ι = B) {ψ : M → X} (hψ : Approximate K B ψ)
    (φ : RelEmbedding K B) (hsource : PrecompactSource N φ)
    (ha : ∀ j, Nonempty (RelEmbedding (a j) K))
    (n : ℕ) (η : RelEmbedding K K)
    (hgood : ∀ j, j < n → Unavoidable (a j) K (N.pullback (φ.comp η))) :
    ∃ u : RelEmbedding K K,
      (∀ j, j < n + 1 → Unavoidable (a j) K (N.pullback (φ.comp (η.comp u)))) ∧
      ∀ j, j < n → ∀ e : RelEmbedding (a j) K,
        (N.pullback (φ.comp (η.comp u))).pullback e
          = (N.pullback (φ.comp η)).pullback e := by
  classical
  let i := φ.comp η
  let Z := N.pullback i
  have hs := precompact_source_pullback hsource η
  let aNew : ∀ j : Fin (n + 1), RelStructure L (A j.val) := fun j => a j.val
  have hfin : ∀ j : Fin (n + 1), (palette (aNew j) K Z).Finite :=
    fun j => (hs (A j.val) (a j.val) (ha j.val)).1
  obtain ⟨h, hmin⟩ := minimum_palette_rank aNew K Z
  let aOld : ∀ j : Fin n, RelStructure L (A j.val) := fun j => a j.val
  have holdfin : ∀ j : Fin n, (palette (aOld j) K Z).Finite :=
    fun j => (hs (A j.val) (a j.val) (ha j.val)).1
  have holdR : ∀ (j : Fin n) p, p ∈ palette (aOld j) K Z → SourceDegreeOne N p :=
    fun j => (hs (A j.val) (a j.val) (ha j.val)).2
  obtain ⟨β, hβ⟩ := coarse_recurrence ι aOld hN hψ i
    (fun j => ha j.val) holdfin (fun j => hgood j.val j.isLt) holdR h
  let u := h.comp β
  have humin := refined_minimizer aNew K Z hfin h hmin β
  have hu := minimizing_palettes_unavoidable aNew K Z hfin u humin
  refine ⟨u, ?_, ?_⟩
  · intro j hj
    exact hu ⟨j, hj⟩
  · intro j hj e
    exact hβ ⟨j, hj⟩ e

private structure StageState {A : ℕ → Type} (a : ∀ j, RelStructure L (A j))
    (K : RelStructure L X) {B : RelStructure L M} (N : RelStructure S M)
    (φ : RelEmbedding K B) (n : ℕ) where
  η : RelEmbedding K K
  good : ∀ j, j < n → Unavoidable (a j) K (N.pullback (φ.comp η))

/-- The paper's countable recursion, with stages indexed so that the
zero-based representative j stabilizes at stage j+1. -/
theorem uniform_stabilization (ι : LanguageInclusion L S)
    {A : ℕ → Type} [∀ j, Finite (A j)] (a : ∀ j, RelStructure L (A j))
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (hN : N.reduct ι = B) {ψ : M → X} (hψ : Approximate K B ψ)
    (φ : RelEmbedding K B) (hsource : PrecompactSource N φ)
    (ha : ∀ j, Nonempty (RelEmbedding (a j) K)) :
    ∃ η : ℕ → RelEmbedding K K,
      η 0 = RelEmbedding.refl K ∧
      (∀ n, ∃ u : RelEmbedding K K, η (n + 1) = (η n).comp u) ∧
      (∀ j n, j + 1 ≤ n → ∀ e : RelEmbedding (a j) K,
        (N.pullback (φ.comp (η n))).pullback e
          = (N.pullback (φ.comp (η (j + 1)))).pullback e) ∧
      ∀ j, Unavoidable (a j) K (N.pullback (φ.comp (η (j + 1)))) := by
  classical
  let chooseU : ∀ n, StageState a K N φ n → RelEmbedding K K := fun n s =>
    Classical.choose (uniform_stage_step ι a hN hψ φ hsource ha n s.η s.good)
  have hU : ∀ n (s : StageState a K N φ n),
      (∀ j, j < n + 1 → Unavoidable (a j) K
        (N.pullback (φ.comp (s.η.comp (chooseU n s))))) ∧
      ∀ j, j < n → ∀ e : RelEmbedding (a j) K,
        (N.pullback (φ.comp (s.η.comp (chooseU n s)))).pullback e
          = (N.pullback (φ.comp s.η)).pullback e := by
    intro n s
    exact Classical.choose_spec (uniform_stage_step ι a hN hψ φ hsource ha n s.η s.good)
  let next : ∀ n, StageState a K N φ n → StageState a K N φ (n + 1) :=
    fun n s => ⟨s.η.comp (chooseU n s), (hU n s).1⟩
  let stages : ∀ n, StageState a K N φ n :=
    fun n => Nat.rec ⟨RelEmbedding.refl K, fun j hj => (Nat.not_lt_zero j hj).elim⟩ next n
  let η := fun n => (stages n).η
  refine ⟨η, rfl, ?_, ?_, ?_⟩
  · intro n
    exact ⟨chooseU n (stages n), rfl⟩
  · intro j n hnj e
    induction n, hnj using Nat.le_induction with
    | base => rfl
    | succ n hnj ih =>
      have hh := (hU n (stages n)).2 j (Nat.lt_of_succ_le hnj) e
      exact hh.trans ih
  · intro j
    exact (stages (j + 1)).good j (Nat.lt_succ_self j)

/-- Truth is defined directly on the fixed domain by eventual stage values;
no convergence of embeddings and no intersection of their ranges is used. -/
def eventualStructure (Z : ℕ → RelStructure S X) : RelStructure S X where
  rel R t := ∃ k, ∀ n, k ≤ n → (Z n).rel R t

theorem eventual_pullback_eq {F : Type} (Z : ℕ → RelStructure S X)
    (e : F → X) (k : ℕ)
    (hstable : ∀ n, k ≤ n → (Z n).pullback e = (Z k).pullback e) :
    (eventualStructure Z).pullback e = (Z k).pullback e := by
  apply RelStructure.ext_rel
  intro r R t
  constructor
  · rintro ⟨m, hm⟩
    have ht := hm (max m k) (le_max_left _ _)
    have he := hstable (max m k) (le_max_right _ _)
    have hh := congrArg (fun p : RelStructure S F => p.rel R t) he
    exact hh.mp ht
  · intro ht
    refine ⟨k, ?_⟩
    intro n hn
    have he := hstable n hn
    have hh := congrArg (fun p : RelStructure S F => p.rel R t) he
    exact hh.mpr ht

theorem eventual_expands (ι : LanguageInclusion L S) (K : RelStructure L X)
    (Z : ℕ → RelStructure S X) (hZ : ∀ n, (Z n).reduct ι = K) :
    (eventualStructure Z).reduct ι = K := by
  apply RelStructure.ext_rel
  intro r R t
  constructor
  · rintro ⟨k, hk⟩
    have ht := hk k le_rfl
    have hh := congrArg (fun p : RelStructure L X => p.rel R t) (hZ k)
    exact hh.mp ht
  · intro ht
    refine ⟨0, ?_⟩
    intro n _
    have hh := congrArg (fun p : RelStructure L X => p.rel R t) (hZ n)
    exact hh.mpr ht

/-- The uniform recursion realizes its full representative palettes as an
actual expansion of K in the original language, including infinite languages. -/
theorem uniform_stabilized_expansion (ι : LanguageInclusion L S)
    {A : ℕ → Type} [∀ j, Finite (A j)] (a : ∀ j, RelStructure L (A j))
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (hN : N.reduct ι = B) {ψ : M → X} (hψ : Approximate K B ψ)
    (φ : RelEmbedding K B) (hsource : PrecompactSource N φ)
    (ha : ∀ j, Nonempty (RelEmbedding (a j) K)) :
    ∃ η : ℕ → RelEmbedding K K, ∃ Y : RelStructure S X,
      Y.reduct ι = K ∧
      η 0 = RelEmbedding.refl K ∧
      (∀ n, ∃ u : RelEmbedding K K, η (n + 1) = (η n).comp u) ∧
      (∀ j n, j + 1 ≤ n → ∀ e : RelEmbedding (a j) K,
        (N.pullback (φ.comp (η n))).pullback e
          = (N.pullback (φ.comp (η (j + 1)))).pullback e) ∧
      (∀ j (e : RelEmbedding (a j) K),
        Y.pullback e = (N.pullback (φ.comp (η (j + 1)))).pullback e) ∧
      ∀ j, Unavoidable (a j) K Y := by
  obtain ⟨η, hη0, hn, hs, hu⟩ := uniform_stabilization ι a hN hψ φ hsource ha
  let Z := fun n => N.pullback (φ.comp (η n))
  let Y := eventualStructure Z
  have hYZ : ∀ j (e : RelEmbedding (a j) K), Y.pullback e = (Z (j + 1)).pullback e :=
    fun j e => eventual_pullback_eq Z e (j + 1) (fun n hn => hs j n hn e)
  refine ⟨η, Y, ?_, hη0, hn, hs, hYZ, ?_⟩
  · apply eventual_expands ι K Z
    intro n
    rw [reduct_pullback, hN]
    exact (φ.comp (η n)).pullback_eq
  · intro j α
    have hp : palette (a j) K Y = palette (a j) K (Z (j + 1)) := by
      exact congrArg Set.range (funext (hYZ j))
    have hpa : palette (a j) K (Y.pullback α)
        = palette (a j) K ((Z (j + 1)).pullback α) := by
      exact congrArg Set.range (funext (fun e => hYZ j (α.comp e)))
    rw [hpa, hp]
    exact hu j α

end RelationalRamsey632.Transfer
