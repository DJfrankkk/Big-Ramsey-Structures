import CombinedRamsey.Positive.Truncation
import RelationalRamsey632.Transfer.SizeIndex

/-! The literal finite-stage lemma for arbitrary ξ : K → M. Ramsey
homogenization takes place in the full source N, never in its truncated
reduct. Its recurrence conclusion concerns the entire N≤n pullback. -/

namespace CombinedRamsey.Positive.Relational.Truncation

open RelationalRamsey632 RelationalRamsey632.Source RelationalRamsey632.Coding
open RelationalRamsey632.RelStructure RelationalRamsey632.Transfer

variable (L : Language) [∀ r, Fintype (L.Rel r)] [IsEmpty (L.Rel 0)]

theorem finite_stage_upper_bound (K : RelStructure L ℕ)
    (hEP : Existence.OnePointExtensionProperty true K) (n : ℕ)
    (ξ : RelationalRamsey632.RelEmbedding K (decoder L))
    {F : Type} [Finite F] (a : RelStructure L F)
    (ha : Nonempty (RelationalRamsey632.RelEmbedding a K)) (hF : Nat.card F ≤ n)
    (hfin : (palette a K (pullback L n ξ)).Finite) :
    EmbeddingDegreeBound a K (palette a K (pullback L n ξ)).ncard := by
  have hfull := full_palette_finite L n ξ a hF hfin
  have hbound := source_degree_bound (Relational.baseInclusion L) (expandedSource_base L)
    (return_approximate L K hEP) ξ ha hfull (source_ramsey_for_palette L ξ a)
  exact palette_card_eq L n ξ a hF ▸ hbound

theorem finite_stage_exact_degree (K : RelStructure L ℕ)
    (hEP : Existence.OnePointExtensionProperty true K) (n : ℕ)
    (ξ : RelationalRamsey632.RelEmbedding K (decoder L))
    {F : Type} [Finite F] (a : RelStructure L F)
    (ha : Nonempty (RelationalRamsey632.RelEmbedding a K)) (hF : Nat.card F ≤ n)
    (hfin : (palette a K (pullback L n ξ)).Finite)
    (hu : Unavoidable a K (pullback L n ξ)) :
    ExactEmbeddingDegree a K (palette a K (pullback L n ξ)).ncard := by
  have hfull := full_palette_finite L n ξ a hF hfin
  have hufull := full_palette_unavoidable L n ξ a hF hu
  obtain ⟨_, hd, _⟩ := exact_degree_from_source_stage (Relational.baseInclusion L)
    (expandedSource_base L) (return_approximate L K hEP) ξ ha hfull
    (source_ramsey_for_palette L ξ a) ((expandedSource L).pullback ξ) (fun _ => rfl) hufull
  exact palette_card_eq L n ξ a hF ▸ hd

noncomputable def selectedFamily (K : RelStructure L ℕ) (n : ℕ)
    (j : BoundedPositiveIsoIndex K n) : RelStructure L (Fin (positiveArity K j.val)) :=
  positiveFamily K j.val

omit [∀ r, Fintype (L.Rel r)] [IsEmpty (L.Rel 0)] in
theorem selected_realized (K : RelStructure L ℕ) (n : ℕ) (j : BoundedPositiveIsoIndex K n) :
    Nonempty (RelationalRamsey632.RelEmbedding (selectedFamily L K n j) K) :=
  Named.isoAgeFamily_realized K j.val.val

omit [∀ r, Fintype (L.Rel r)] [IsEmpty (L.Rel 0)] in
theorem selected_size_le (K : RelStructure L ℕ) (n : ℕ) (j : BoundedPositiveIsoIndex K n) :
    Nat.card (Fin (positiveArity K j.val)) ≤ n := by
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using j.property

omit [IsEmpty (L.Rel 0)] in
/-- Preserving all full selected types of size at most n preserves every
added n-bounded predicate on every tuple, including repeated tuples. The
whole base language is preserved by the given full K-self-embedding. -/
theorem preserves_selected_truncated_embedding (K : RelStructure L ℕ) (n : ℕ)
    (ξ : RelationalRamsey632.RelEmbedding K (decoder L))
    (f : RelationalRamsey632.RelEmbedding K K)
    (hpres : ∀ j : BoundedPositiveIsoIndex K n,
      ∀ e : RelationalRamsey632.RelEmbedding (selectedFamily L K n j) K,
        ((expandedSource L).pullback ξ).pullback (f.comp e) =
          ((expandedSource L).pullback ξ).pullback e) :
    IsEmbeddingMap (pullback L n ξ) (pullback L n ξ) f := by
  classical
  refine ⟨f.injective, ?_⟩
  intro r R t
  cases R with
  | inl R => exact (ξ.map_rel R t).symm.trans ((f.map_rel R t).trans (ξ.map_rel R (f ∘ t)))
  | inr R =>
    by_cases ht : Function.Injective t
    · haveI : Nonempty (Fin r) := ⟨⟨0, R.val.property⟩⟩
      let a := K.pullback t
      let e : RelationalRamsey632.RelEmbedding a K := RelationalRamsey632.RelEmbedding.pullback K t ht
      obtain ⟨j, u, hu⟩ := positiveFamily_covers_nonempty K a ⟨e⟩
      have hcard : positiveArity K j = r := by
        simpa only [Fintype.card_fin] using Fintype.card_congr (Equiv.ofBijective u ⟨u.injective, hu⟩)
      let J : BoundedPositiveIsoIndex K n := ⟨j, hcard.symm ▸ R.property⟩
      have htypes : ∀ v : RelationalRamsey632.RelEmbedding a K,
          ((expandedSource L).pullback ξ).pullback (f.comp v) =
            ((expandedSource L).pullback ξ).pullback v :=
        full_types_transfer u hu (((expandedSource L).pullback ξ).pullback f)
          ((expandedSource L).pullback ξ) (hpres J)
      have heq := congrArg (fun p => p.rel (Sum.inr R.val) (id : Fin r → Fin r)) (htypes e)
      exact heq.to_iff.symm
    · apply iff_of_false
      · intro h
        exact ht h.1.of_comp
      · intro h
        have hi : Function.Injective ((ξ ∘ f) ∘ t) := h.1
        exact ht hi.of_comp

/-- Literal recurrence of the whole n-truncated expansion. Hypotheses
only concern the finite I_n palette list, while the source Ramsey theorem
is internally instantiated on the actual full source N. -/
theorem finite_stage_recurrent (K : RelStructure L ℕ) (hK : K.InjectiveRelations)
    (hEP : Existence.OnePointExtensionProperty true K) (n : ℕ)
    (ξ : RelationalRamsey632.RelEmbedding K (decoder L))
    (hfin : ∀ j : BoundedPositiveIsoIndex K n,
      (palette (selectedFamily L K n j) K (pullback L n ξ)).Finite)
    (hunav : ∀ j : BoundedPositiveIsoIndex K n,
      Unavoidable (selectedFamily L K n j) K (pullback L n ξ)) :
    ∀ g : RelationalRamsey632.RelEmbedding K K,
      ∃ h : RelationalRamsey632.RelEmbedding K K,
        IsEmbeddingMap (pullback L n ξ) (pullback L n ξ) (g.comp h) := by
  classical
  have hL : L.FinitePerArity := fun _ => inferInstance
  letI := boundedPositiveIndex_finite K hK hL n
  letI := Fintype.ofFinite (BoundedPositiveIsoIndex K n)
  let family := selectedFamily L K n
  have hfinFull : ∀ j, (palette (family j) K ((expandedSource L).pullback ξ)).Finite :=
    fun j => full_palette_finite L n ξ (family j) (selected_size_le L K n j) (hfin j)
  have hunavFull : ∀ j, Unavoidable (family j) K ((expandedSource L).pullback ξ) :=
    fun j => full_palette_unavoidable L n ξ (family j) (selected_size_le L K n j) (hunav j)
  intro g
  obtain ⟨h, hh⟩ := coarse_recurrence (Relational.baseInclusion L) family
    (expandedSource_base L) (return_approximate L K hEP) ξ
    (selected_realized L K n) hfinFull hunavFull
    (fun j => source_ramsey_for_palette L ξ (family j)) g
  exact ⟨h, preserves_selected_truncated_embedding L K n ξ (g.comp h) hh⟩

/-- The complete printed finite-stage lemma, simultaneously for I_n.
The upper-bound-only assertion is separately exported above. -/
theorem finite_stage_lemma (K : RelStructure L ℕ) (hK : K.InjectiveRelations)
    (hEP : Existence.OnePointExtensionProperty true K) (n : ℕ)
    (ξ : RelationalRamsey632.RelEmbedding K (decoder L))
    (hfin : ∀ j : BoundedPositiveIsoIndex K n,
      (palette (selectedFamily L K n j) K (pullback L n ξ)).Finite)
    (hunav : ∀ j : BoundedPositiveIsoIndex K n,
      Unavoidable (selectedFamily L K n j) K (pullback L n ξ)) :
    (∀ j : BoundedPositiveIsoIndex K n,
      ExactEmbeddingDegree (selectedFamily L K n j) K
        (palette (selectedFamily L K n j) K (pullback L n ξ)).ncard) ∧
    (∀ g : RelationalRamsey632.RelEmbedding K K,
      ∃ h : RelationalRamsey632.RelEmbedding K K,
        IsEmbeddingMap (pullback L n ξ) (pullback L n ξ) (g.comp h)) := by
  refine ⟨?_, finite_stage_recurrent L K hK hEP n ξ hfin hunav⟩
  intro j
  exact finite_stage_exact_degree L K hEP n ξ (selectedFamily L K n j)
    (selected_realized L K n j) (selected_size_le L K n j) (hfin j) (hunav j)

end CombinedRamsey.Positive.Relational.Truncation
