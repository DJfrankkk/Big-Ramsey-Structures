import CombinedRamsey.Negative.EncodingCanonical
import CombinedRamsey.Negative.EncodingHomOrder
import CombinedRamsey.Negative.Ages

/-! The completion criterion is the actual induced age of one-point realizations. -/

namespace CombinedRamsey.Negative

open RelationalRamsey632

variable {X W : Type} {k : ℕ} (H : Digraph (Fin k))
  (K : RelStructure language X) (b : RelEmbedding (boundary H).toRel K)

def EncodedRealizations : Set X :=
  {x | ∃ p : RelEmbedding (typeTable H).toRel K,
    (∀ a, p (.inl a) = b a) ∧ p (.inr ()) = x}

theorem encoded_outside_base {x : X} (hx : x ∈ EncodedRealizations H K b) :
    x ∉ Set.range b := by
  obtain ⟨p,hp,hstar⟩ := hx
  rintro ⟨a,ha⟩
  have hn := p.injective (hstar.trans (ha.symm.trans (hp a).symm))
  cases hn

theorem realization_age_completion_necessity
    (hKlegal : (Table.ofRel K).Legal)
    (B : Table W) (hB : B.Canonical)
    (h : InAgeOn K (EncodedRealizations H K b) B.toRel) : HasCompletion H B := by
  classical
  obtain ⟨e,he⟩ := h
  let f : EncodedBoundary H ⊕ W → X := Sum.elim b e
  have hf : Function.Injective f := by
    intro a c hac
    cases a with
    | inl a =>
      cases c with
      | inl c => exact congrArg Sum.inl (b.injective hac)
      | inr c => exact (encoded_outside_base H K b (he c) ⟨a,hac⟩).elim
    | inr a =>
      cases c with
      | inl c => exact (encoded_outside_base H K b (he a) ⟨c,hac.symm⟩).elim
      | inr c => exact congrArg Sum.inr (e.injective hac)
  let Y := Table.ofRel (K.pullback f)
  have hold : Y.pullback Sum.inl = boundary H := by
    rw [← Table.ofRel_pullback]
    have hcomp : f ∘ Sum.inl = b := rfl
    rw [RelStructure.pullback_comp, hcomp, b.pullback_eq]
    exact Table.ofRel_toRel _ (boundary_canonical H)
  have hnew : Y.pullback Sum.inr = B := by
    rw [← Table.ofRel_pullback]
    have hcomp : f ∘ Sum.inr = e := rfl
    rw [RelStructure.pullback_comp, hcomp, e.pullback_eq]
    exact Table.ofRel_toRel B hB
  have hpoint : ∀ x : W, Y.pullback (Completion.pointMap (H := H) x) = typeTable H := by
    intro x
    obtain ⟨p,hp,hstar⟩ := he x
    have hcomp : f ∘ Completion.pointMap (H := H) x = p := by
      funext a
      cases a with
      | inl a => exact (hp a).symm
      | inr a => cases a; exact hstar.symm
    rw [← Table.ofRel_pullback]
    rw [RelStructure.pullback_comp, hcomp, p.pullback_eq]
    exact Table.ofRel_toRel _ (typeTable_canonical H)
  have hYlegal : Y.Legal := by
    dsimp only [Y]
    rw [Table.ofRel_pullback]
    exact Table.legal_pullback (Table.ofRel K) f hf hKlegal
  refine ⟨Y,hYlegal,?_⟩
  constructor
  · intro u a; exact Iff.of_eq (congrArg (fun T => T.unary u a) hold)
  · intro u x; exact Iff.of_eq (congrArg (fun T => T.unary u x) hnew)
  · intro r a c; exact Iff.of_eq (congrArg (fun T => T.binary r a c) hold)
  · intro r x y; exact Iff.of_eq (congrArg (fun T => T.binary r x y) hnew)
  · intro r a x
    exact Iff.of_eq (congrArg (fun T => T.binary r (.inl a) (.inr ())) (hpoint x))
  · intro r x a
    exact Iff.of_eq (congrArg (fun T => T.binary r (.inr ()) (.inl a)) (hpoint x))
  · intro r a c d
    have hh := congrArg (fun T => T.ternary r a c d) hold
    intro ht
    exact (Iff.of_eq hh).mp ht
  · intro r x y z; exact Iff.of_eq (congrArg (fun T => T.ternary r x y z) hnew)
  · intro x u
    have hn := congrArg (fun T => T.unary u x) hnew
    have hp := congrArg (fun T => T.unary u (.inr ())) (hpoint x)
    exact (Iff.of_eq hn).symm.trans (Iff.of_eq hp)
  · intro x r a c d _ _ _
    have hp := congrArg (fun T => T.ternary r a c d) (hpoint x)
    intro ht
    exact (Iff.of_eq hp).mp ht

/-- Full finite extension over the actual old domain. This is instantiated
    from the numerical constrained EP, rather than assumed for the final K. -/
def RelFiniteExtension (K : RelStructure language X) : Prop :=
  ∀ (V W : Type) [Finite V] [Finite W]
    (D : RelStructure language (V ⊕ W)), D.InjectiveRelations → (Table.ofRel D).Legal →
    ∀ f : RelEmbedding (D.pullback Sum.inl) K,
      ∃ g : RelEmbedding D K, ∀ v, g (.inl v) = f v

theorem realization_age_completion_sufficiency [Finite W]
    (hEP : RelFiniteExtension K) (B : Table W) (h : HasCompletion H B) :
    InAgeOn K (EncodedRealizations H K b) B.toRel := by
  obtain ⟨Y,hYlegal,hY⟩ := h
  have hred : Y.toRel.pullback Sum.inl = (boundary H).toRel := hY.oldEmbedding.pullback_eq
  let old : RelEmbedding (Y.toRel.pullback Sum.inl) K := {
    toFun := b
    injective := b.injective
    map_rel := fun R t => (Iff.of_eq (congrArg (fun D => D.rel R t) hred)).trans
      (b.map_rel R t) }
  have hcanon : (Table.ofRel Y.toRel).Legal := (Table.canonical_legal_iff Y).mpr hYlegal
  obtain ⟨g,hg⟩ := hEP (EncodedBoundary H) W Y.toRel Y.toRel_injective hcanon old
  refine ⟨g.comp hY.newEmbedding, ?_⟩
  intro x
  refine ⟨g.comp (hY.pointEmbedding x), ?_, rfl⟩
  intro a
  exact hg a

theorem realization_age_formula [Finite W] (hk : 0 < k)
    (hKlegal : (Table.ofRel K).Legal)
    (hEP : RelFiniteExtension K) (B : Table W) (hB : B.Canonical) :
    InAgeOn K (EncodedRealizations H K b) B.toRel ↔
      B.PureDelta ∧ ∀ h, Nonempty (Hom (B.localGraph h) H) := by
  rw [← legal_completion_iff hk H B]
  exact ⟨realization_age_completion_necessity H K b hKlegal B hB,
    realization_age_completion_sufficiency H K b hEP B⟩

end CombinedRamsey.Negative
