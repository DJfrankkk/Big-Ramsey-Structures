import RelationalRamsey632.Transfer.SizeIndex
import RelationalRamsey632.Transfer.AgeTransport

namespace RelationalRamsey632.Transfer

open RelStructure

variable {L S : Language} {M : Type}

theorem stage_factorization (K : RelStructure L ℕ) (η : ℕ → RelEmbedding K K)
    (hs : ∀ n, ∃ u : RelEmbedding K K, η (n + 1) = (η n).comp u)
    (n m : ℕ) (hnm : n ≤ m) : ∃ u : RelEmbedding K K, η m = (η n).comp u := by
  induction m, hnm using Nat.le_induction with
  | base => exact ⟨RelEmbedding.refl K, (RelEmbedding.comp_refl _).symm⟩
  | succ m hnm ih =>
    obtain ⟨u, hu⟩ := ih
    obtain ⟨v, hv⟩ := hs m
    exact ⟨u.comp v, by rw [hv, hu, RelEmbedding.comp_assoc]⟩

theorem size_stabilized_expansion (ι : LanguageInclusion L S) [IsEmpty (S.Rel 0)]
    {K : RelStructure L ℕ} (hK : K.InjectiveRelations) (hL : L.FinitePerArity)
    {B : RelStructure L M} {N : RelStructure S M}
    (hN : N.reduct ι = B) {ψ : M → ℕ} (hψ : Approximate K B ψ)
    (φ : RelEmbedding K B) (hsource : PrecompactSource N φ) :
    ∃ η : ℕ → RelEmbedding K K, ∃ Y : RelStructure S ℕ,
      Y.reduct ι = K ∧ η 0 = RelEmbedding.refl K ∧
      (∀ n, ∃ u : RelEmbedding K K, η (n + 1) = (η n).comp u) ∧
      (∀ m (b : RelStructure L (Fin m)) (_hb : Nonempty (RelEmbedding b K)),
        ∀ n, m ≤ n → ∀ e : RelEmbedding b K,
          Y.pullback e = (N.pullback (φ.comp (η n))).pullback e) ∧
      ∀ (F : Type) [Finite F] (b : RelStructure L F)
        (_hb : Nonempty (RelEmbedding b K)), Unavoidable b K Y := by
  classical
  letI := positiveIndex_nonempty K
  letI := positiveIndex_countable K hK hL
  obtain ⟨enum, hEnum⟩ := exists_surjective_nat (PositiveIsoIndex K)
  let index : PositiveIsoIndex K → ℕ := fun j => Classical.choose (hEnum j)
  have hindex : ∀ j, enum (index j) = j := fun j => Classical.choose_spec (hEnum j)
  let A : ℕ → Type := fun j => Fin (positiveArity K (enum j))
  let a : ∀ j, RelStructure L (A j) := fun j => positiveFamily K (enum j)
  haveI : ∀ j, Finite (A j) := fun _ => inferInstance
  have ha : ∀ j, Nonempty (RelEmbedding (a j) K) :=
    fun j => Named.isoAgeFamily_realized K (enum j).val
  obtain ⟨ηraw, Y, hY, hzero, hstep, hstable, htypes, hunav⟩ :=
    uniform_stabilized_expansion ι a hN hψ φ hsource ha
  let bound := sizeThreshold K hK hL index
  let η := fun n => ηraw (bound n)
  have hrep : ∀ j : PositiveIsoIndex K, ∀ n, index j + 1 ≤ n →
      ∀ e : RelEmbedding (positiveFamily K j) K,
        Y.pullback e = (N.pullback (φ.comp (ηraw n))).pullback e := by
    intro j n hn
    have ht : ∀ e : RelEmbedding (a (index j)) K,
        Y.pullback e = (N.pullback (φ.comp (ηraw n))).pullback e :=
      fun e => (htypes (index j) e).trans (hstable (index j) n hn e).symm
    change ∀ e : RelEmbedding (positiveFamily K (enum (index j))) K,
      Y.pullback e = (N.pullback (φ.comp (ηraw n))).pullback e at ht
    rw [hindex j] at ht
    exact ht
  have hrepUnav : ∀ j : PositiveIsoIndex K, Unavoidable (positiveFamily K j) K Y := by
    intro j
    have ht := hunav (index j)
    change Unavoidable (positiveFamily K (enum (index j))) K Y at ht
    rw [hindex j] at ht
    exact ht
  refine ⟨η, Y, hY, ?_, ?_, ?_, ?_⟩
  · change ηraw (sizeThreshold K hK hL index 0) = _
    rw [sizeThreshold_zero]
    exact hzero
  · intro n
    exact stage_factorization K ηraw hstep (bound n) (bound (n + 1))
      (sizeThreshold_monotone K hK hL index (Nat.le_succ n))
  · intro m b hb n hmn e
    by_cases hm : 0 < m
    · letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
      obtain ⟨j, u, hu⟩ := positiveFamily_covers_nonempty K b hb
      have hcard : positiveArity K j = m := by
        simpa using Fintype.card_congr (Equiv.ofBijective u ⟨u.injective, hu⟩)
      exact full_types_transfer u hu Y (N.pullback (φ.comp (η n)))
        (hrep j (bound n) (sizeThreshold_ge K hK hL index n j (hcard ▸ hmn))) e
    · have hm0 : m = 0 := by omega
      haveI : IsEmpty (Fin m) := hm0 ▸ (inferInstance : IsEmpty (Fin 0))
      exact Named.eq_on_empty _ _
  · intro F _ b hb
    by_cases hF : Nonempty F
    · letI := hF
      obtain ⟨j, u, hu⟩ := positiveFamily_covers_nonempty K b hb
      exact unavoidable_transfer u hu Y (hrepUnav j)
    · haveI : IsEmpty F := not_nonempty_iff.mp hF
      intro α
      apply Set.Subset.antisymm (palette_pullback_subset b K Y α)
      rintro p ⟨e, _⟩
      exact ⟨e, Named.eq_on_empty _ _⟩

end RelationalRamsey632.Transfer
