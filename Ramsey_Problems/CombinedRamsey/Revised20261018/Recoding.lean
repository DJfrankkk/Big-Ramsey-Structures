import RelationalRamsey632.Transfer.IsoRepresentatives

/-!
Injective names of complete finite source types, without restrictions on the
base language or on repeated tuples in its relations.  Nullary source
predicates are handled by equality inside one actual pullback palette.
-/

namespace CombinedRamsey.Revised20261018

open RelationalRamsey632 RelationalRamsey632.RelStructure
open RelationalRamsey632.Transfer RelationalRamsey632.Transfer.Named

variable {L S : Language} {X : Type}

/-- The source of a finite stage: base relations plus names of the
complete original source pullbacks on the selected finite structures. -/
def recodedSource {J M : Type} {n : J → ℕ}
    (a : ∀ j, RelStructure L (Fin (n j))) (K : RelStructure L X)
    (B : RelStructure L M) (N : RelStructure S M) (φ : RelEmbedding K B) :=
  onStructure a K (N.pullback φ) B N

theorem source_embedding_preserves_recoding {J M : Type} {n : J → ℕ}
    (a : ∀ j, RelStructure L (Fin (n j))) (K : RelStructure L X)
    (B : RelStructure L M) (N : RelStructure S M) (φ : RelEmbedding K B)
    (ι : LanguageInclusion L S) (hN : N.reduct ι = B)
    (z : RelEmbedding N N) :
    IsEmbeddingMap (recodedSource a K B N φ) (recodedSource a K B N φ) z := by
  let zb := toBaseEmbedding ι hN hN z
  have h := names_covariant a K (N.pullback φ) zb N
  change (recodedSource a K B N φ).pullback z =
    onStructure a K (N.pullback φ) B (N.pullback z) at h
  rw [z.pullback_eq] at h
  exact ⟨z.injective, fun r R t =>
    (congrArg (fun Q => Q.rel R t) h).symm.to_iff⟩

/-- Equation (6.2): on a selected nonempty A, the distinguished positive
name forces the entire original source table.  This is equality of all
underlying embedding maps, including occurrences outside φ[K]. -/
theorem recoded_embedding_iff {J M : Type} {n : J → ℕ}
    (a : ∀ j, RelStructure L (Fin (n j))) (K : RelStructure L X)
    (B : RelStructure L M) (N : RelStructure S M) (φ : RelEmbedding K B)
    (ι : LanguageInclusion L S) (hN : N.reduct ι = B)
    (j : J) (hj : 0 < n j) (p : palette (a j) K (N.pullback φ))
    (f : Fin (n j) → M) :
    IsEmbeddingMap (onStructure a K (N.pullback φ) (a j) p.val)
      (recodedSource a K B N φ) f ↔ IsEmbeddingMap p.val N f := by
  have hpbase : p.val.reduct ι = a j := by
    apply palette_reduct ι (show (N.pullback φ).reduct ι = K from ?_) p.property
    rw [reduct_pullback, hN]
    exact φ.pullback_eq
  constructor
  · intro hf
    have hp : (onStructure a K (N.pullback φ) (a j) p.val).rel
        (name a K (N.pullback φ) j hj p) id :=
      (name_rel a K (N.pullback φ) (a j) p.val j hj p id).mpr
        ⟨Function.injective_id, rfl, rfl⟩
    have hn := (hf.2 _ _ id).mp hp
    have he := ((name_rel a K (N.pullback φ) B N j hj p f).mp hn).2.2
    exact ⟨hf.1, fun r R t => (congrArg (fun Q => Q.rel R t) he).symm.to_iff⟩
  · intro hf
    let z := embeddingOfMap f hf
    let zb := toBaseEmbedding ι hpbase hN z
    have h := names_covariant a K (N.pullback φ) zb N
    change (recodedSource a K B N φ).pullback z =
      onStructure a K (N.pullback φ) (a j) (N.pullback z) at h
    rw [z.pullback_eq] at h
    exact ⟨hf.1, fun r R t => (congrArg (fun Q => Q.rel R t) h).symm.to_iff⟩

/-- The degree-one part of equation (6.2), obtained by the actual
embedding-map equivalence and by N-self-embeddings preserving N_n. -/
theorem recoded_source_degree_one {J M : Type} {n : J → ℕ}
    (a : ∀ j, RelStructure L (Fin (n j))) (K : RelStructure L X)
    (B : RelStructure L M) (N : RelStructure S M) (φ : RelEmbedding K B)
    (ι : LanguageInclusion L S) (hN : N.reduct ι = B)
    (j : J) (hj : 0 < n j) (p : palette (a j) K (N.pullback φ))
    (hR : SourceDegreeOne N p.val) :
    SourceDegreeOne (recodedSource a K B N φ)
      (onStructure a K (N.pullback φ) (a j) p.val) := by
  intro D _ c
  let Q := onStructure a K (N.pullback φ) (a j) p.val
  let NN := recodedSource a K B N φ
  let lift : RelEmbedding p.val N → RelEmbedding Q NN := fun e =>
    embeddingOfMap e ((recoded_embedding_iff a K B N φ ι hN j hj p e).mpr
      ⟨e.injective, fun _ R t => e.map_rel R t⟩)
  let forget : RelEmbedding Q NN → RelEmbedding p.val N := fun e =>
    embeddingOfMap e ((recoded_embedding_iff a K B N φ ι hN j hj p e).mp
      ⟨e.injective, fun _ R t => e.map_rel R t⟩)
  obtain ⟨z, hz⟩ := hR D (fun e => c (lift e))
  let zz : RelEmbedding NN NN := embeddingOfMap z
    (source_embedding_preserves_recoding a K B N φ ι hN z)
  refine ⟨zz, ?_⟩
  intro u v
  have hu : lift (z.comp (forget u)) = zz.comp u := by
    apply RelationalRamsey632.RelEmbedding.ext
    intro x
    rfl
  have hv : lift (z.comp (forget v)) = zz.comp v := by
    apply RelationalRamsey632.RelEmbedding.ext
    intro x
    rfl
  simpa only [hu, hv] using hz (forget u) (forget v)

theorem countable_labelled_age [Countable X] (K : RelStructure L X) (r : ℕ) :
    Countable (AgeStates K r) := by
  classical
  let f : AgeStates K r → (Fin r → X) := fun b x => (Classical.choice b.property) x
  apply Function.Injective.countable (f := f)
  intro b c h
  apply Subtype.ext
  have hb := (Classical.choice b.property).pullback_eq
  have hc := (Classical.choice c.property).pullback_eq
  exact hb.symm.trans ((congrArg K.pullback h).trans hc)

theorem countable_labelled_age_index [Countable X] (K : RelStructure L X) :
    Countable (AgeIndex K) := by
  letI : ∀ r, Countable (AgeStates K r) := countable_labelled_age K
  unfold AgeIndex
  infer_instance

def permuteAge (K : RelStructure L X) {r : ℕ} (b : AgeStates K r)
    (σ : Equiv.Perm (Fin r)) : AgeStates K r :=
  ⟨b.val.pullback σ, ⟨(Classical.choice b.property).comp
    (RelEmbedding.pullback b.val σ σ.injective)⟩⟩

theorem finite_labelled_age_of_finite_iso (K : RelStructure L X) (r : ℕ)
    [Finite (IsoAge K r)] : Finite (AgeStates K r) := by
  classical
  let f : IsoAge K r × Equiv.Perm (Fin r) → AgeStates K r :=
    fun p => permuteAge K (representative K r p.1) p.2
  apply Finite.of_surjective f
  intro b
  let q : IsoAge K r := Quotient.mk _ b
  obtain ⟨σ, hσ⟩ := Quotient.exact (representative_class K r q)
  refine ⟨⟨q, σ.symm⟩, ?_⟩
  apply Subtype.ext
  change (representative K r q).val.pullback σ.symm = b.val
  rw [← hσ, pullback_comp]
  have he : σ ∘ σ.symm = id := funext σ.apply_symm_apply
  rw [he, pullback_id]

theorem finite_labelled_age_arity (K : RelStructure L X) (r : ℕ)
    [Finite (AgeStates K r)] :
    Finite {j : AgeIndex K // ageArity K j = r} := by
  classical
  let f : {j : AgeIndex K // ageArity K j = r} → AgeStates K r := fun j =>
    j.property ▸ j.val.snd
  exact Finite.of_injective f (by
    rintro ⟨⟨s, b⟩, hs⟩ ⟨⟨t, c⟩, ht⟩ h
    change s = r at hs
    change t = r at ht
    subst s
    subst t
    change b = c at h
    cases h
    rfl)

theorem empty_palette_subsingleton {F : Type} [IsEmpty F]
    (b : RelStructure L F) (K : RelStructure L X) (Y : RelStructure S X) :
    Subsingleton (palette b K Y) := by
  constructor
  rintro ⟨p, e, rfl⟩ ⟨q, f, rfl⟩
  apply Subtype.ext
  exact congrArg Y.pullback (funext fun x => isEmptyElim x)

/-- Literal names recover the full type, even when the source has nullaries. -/
theorem allAge_paletteMap_injective (K : RelStructure L X) (Y : RelStructure S X)
    {F : Type} [Finite F] (b : RelStructure L F)
    (hb : Nonempty (RelEmbedding b K)) :
    Function.Injective (paletteMap (ageFamily K) K Y b) := by
  classical
  intro p q h
  by_cases hF : Nonempty F
  · obtain ⟨j, u, hu⟩ := age_family_covers K F b hb
    have hj : 0 < ageArity K j := by
      obtain ⟨x⟩ := hF
      obtain ⟨z, _⟩ := hu x
      exact Nat.zero_lt_of_lt z.isLt
    let pt := restrictedType (ageFamily K) K Y p j u
    have hp : (onStructure (ageFamily K) K Y b p.val).rel
        (name (ageFamily K) K Y j hj pt) u :=
      (name_rel (ageFamily K) K Y b p.val j hj pt u).mpr
        ⟨u.injective, u.pullback_eq, rfl⟩
    have htable := congrArg Subtype.val h
    change onStructure (ageFamily K) K Y b p.val =
      onStructure (ageFamily K) K Y b q.val at htable
    have hq := htable ▸ hp
    have he := ((name_rel (ageFamily K) K Y b q.val j hj pt u).mp hq).2.2
    apply Subtype.ext
    exact pullback_injective_of_surjective u hu he.symm
  · haveI : IsEmpty F := not_nonempty_iff.mp hF
    haveI := empty_palette_subsingleton b K Y
    exact Subsingleton.elim p q

noncomputable def allAgePaletteEquivArbitrary (K : RelStructure L X)
    (Y : RelStructure S X) {F : Type} [Finite F] (b : RelStructure L F)
    (hb : Nonempty (RelEmbedding b K)) :
    palette b K Y ≃ palette b K (allAgeExpansion K Y) :=
  Equiv.ofBijective (paletteMap (ageFamily K) K Y b)
    ⟨allAge_paletteMap_injective K Y b hb,
      paletteMap_surjective (ageFamily K) K Y b⟩

theorem allAge_palette_card_arbitrary (K : RelStructure L X) (Y : RelStructure S X)
    {F : Type} [Finite F] (b : RelStructure L F)
    (hb : Nonempty (RelEmbedding b K)) :
    (palette b K (allAgeExpansion K Y)).ncard = (palette b K Y).ncard :=
  (Nat.card_congr (allAgePaletteEquivArbitrary K Y b hb)).symm

theorem countable_added_symbols [Countable X] (K : RelStructure L X)
    (Y : RelStructure S X)
    (hfin : ∀ (F : Type) [Finite F] (b : RelStructure L F),
      Nonempty (RelEmbedding b K) → (palette b K Y).Finite) :
    Countable (Σ r, Symbols (ageFamily K) K Y r) := by
  letI := countable_labelled_age_index K
  letI : ∀ r, Countable (Symbols (ageFamily K) K Y r) := fun r =>
    countable_symbols (ageFamily K) K Y
      (fun j => hfin _ (ageFamily K j) j.snd.property) r
  infer_instance

theorem finite_added_symbols (K : RelStructure L X) (Y : RelStructure S X)
    (hiso : ∀ r, Finite (IsoAge K r))
    (hfin : ∀ (F : Type) [Finite F] (b : RelStructure L F),
      Nonempty (RelEmbedding b K) → (palette b K Y).Finite) (r : ℕ) :
    Finite (Symbols (ageFamily K) K Y r) := by
  letI := hiso r
  letI := finite_labelled_age_of_finite_iso K r
  letI := finite_labelled_age_arity K r
  exact finite_symbols (ageFamily K) K Y
    (fun j => hfin _ (ageFamily K j) j.snd.property) r

/-- Only the newly added names are injective; no condition is imposed on
the arities or repeated tuples of the original relations. -/
theorem added_relations_injective (K : RelStructure L X) (Y : RelStructure S X)
    {r : ℕ} (R : Symbols (ageFamily K) K Y r) (t : Fin r → X)
    (h : (allAgeExpansion K Y).rel (Sum.inr R) t) : Function.Injective t := by
  rcases R with ⟨j, q⟩
  intro x y hxy
  have hi : Function.Injective (t ∘ Fin.cast j.property.1) := h.1
  have he := hi (show
      t (Fin.cast j.property.1 (Fin.cast j.property.1.symm x)) =
        t (Fin.cast j.property.1 (Fin.cast j.property.1.symm y)) by simpa using hxy)
  exact (Fin.cast_injective j.property.1.symm) he

end CombinedRamsey.Revised20261018
