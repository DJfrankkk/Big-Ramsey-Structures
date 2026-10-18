import CombinedRamsey.Positive.ProfileMain
import CombinedRamsey.Positive.Conjecture47
import RelationalRamsey632.Source.DiagramIso

/-!
Positive results for the 18 October 2026 manuscript.  The relevant
mathematical statements correspond to the verified 10 October edition.
This module exports the positive existence conclusion and closes the
explicit quantitative palette estimate labelled `prop:precompact`.

The profile alphabet is the original marker alphabet: q_(r+1) + 1,
without a hidden alphabet enlargement.  No bound on the arities or their
relation counts is assumed.
-/

namespace CombinedRamsey.Revised20261018.Positive

open RelationalRamsey632 RelationalRamsey632.Source RelationalRamsey632.Transfer
open RelationalRamsey632.RelStructure
open CombinedRamsey.Positive.Relational
open scoped BigOperators

variable (L : Language) [∀ r, Fintype (L.Rel r)] [IsEmpty (L.Rel 0)]

/-- The exact right-hand side in `prop:precompact`, with the manuscript's
profile alphabet and the same uniform R(k). -/
noncomputable def paletteBound (n : ℕ) : ℕ :=
  (Nat.card (RelationalRamsey632.Coding.UnaryProfile L) *
    ∑ h : Fin (CombinedRamsey.Positive.originalEnvelopeBound n),
      ∏ r ∈ Finset.Icc 1 h.val, (profileColours L r + 2) ^ h.val.choose r) ^ n

/-- The full pullback palette injects into the realized literal normal
forms.  This makes explicit the last counting step in `prop:precompact`. -/
theorem initial_palette_card_le_normalForms (K : RelStructure L ℕ)
    (hK : K.InjectiveRelations) (n : ℕ) (b : RelStructure L (Fin n)) :
    Nat.card (palette b K ((expandedSource L).pullback (codingEmbedding L K hK))) ≤
      Nat.card (codingNormalForms L K n) := by
  classical
  let X := (expandedSource L).pullback (codingEmbedding L K hK)
  let witness : palette b K X → RelEmbedding b K := fun p => Classical.choose p.property
  have hw : ∀ p : palette b K X, X.pullback (witness p) = p.val :=
    fun p => Classical.choose_spec p.property
  let f : palette b K X → codingNormalForms L K n := fun p =>
    ⟨normalForm (codingMap L K ∘ witness p),
      ⟨⟨witness p, (witness p).injective⟩, rfl⟩⟩
  haveI : Finite (codingNormalForms L K n) := (uniform_finite_normal_forms L K n).to_subtype
  apply Nat.card_le_card_of_injective f
  intro p q hpq
  apply Subtype.ext
  rw [← hw p, ← hw q]
  have hnf : normalForm (codingMap L K ∘ witness p) =
      normalForm (codingMap L K ∘ witness q) := congrArg Subtype.val hpq
  calc
    X.pullback (witness p) = (expandedSource L).pullback
        (normalForm (codingMap L K ∘ witness p)) :=
      (expandedSource_normalForm_pullback L _
        ((codingMap_injective L K).comp (witness p).injective)).symm
    _ = (expandedSource L).pullback
        (normalForm (codingMap L K ∘ witness q)) := congrArg _ hnf
    _ = X.pullback (witness q) := expandedSource_normalForm_pullback L _
      ((codingMap_injective L K).comp (witness q).injective)

/-- `prop:precompact`, including its displayed quantitative bound for any
fixed labelled n-element structure, not only finiteness. -/
theorem initial_palette_quantitative_bound_fin (K : RelStructure L ℕ)
    (hK : K.InjectiveRelations) (n : ℕ) (b : RelStructure L (Fin n)) :
    (palette b K ((expandedSource L).pullback (codingEmbedding L K hK))).Finite ∧
      Nat.card (palette b K ((expandedSource L).pullback (codingEmbedding L K hK))) ≤
        paletteBound L n := by
  refine ⟨uniform_precompact_palettes L K hK (Fin n) b, ?_⟩
  have hNF := CombinedRamsey.Positive.Marker.uniform_normalFormImage_bound
    (profileColours L) (relationCodes L K) (RelationalRamsey632.Coding.unaryAt L K) n
  exact (initial_palette_card_le_normalForms L K hK n b).trans hNF.2

/-- The same displayed bound for arbitrary finite underlying types. -/
theorem initial_palette_quantitative_bound (K : RelStructure L ℕ)
    (hK : K.InjectiveRelations) (F : Type) [Finite F] (b : RelStructure L F) :
    (palette b K ((expandedSource L).pullback (codingEmbedding L K hK))).Finite ∧
      Nat.card (palette b K ((expandedSource L).pullback (codingEmbedding L K hK))) ≤
        paletteBound L (Nat.card F) := by
  classical
  letI := Fintype.ofFinite F
  let E := Fintype.equivFin F
  let X := (expandedSource L).pullback (codingEmbedding L K hK)
  let bE := b.pullback E.symm
  let u : RelEmbedding bE b := RelEmbedding.pullback b E.symm E.symm.injective
  let f : palette b K X → palette bE K X := fun p =>
    ⟨p.val.pullback u, by
      obtain ⟨e, he⟩ := p.property
      exact ⟨e.comp u, congrArg (fun z => z.pullback u) he⟩⟩
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    exact pullback_injective_of_surjective u E.symm.surjective
      (congrArg (fun z : palette bE K X => z.val) h)
  haveI : Finite (palette bE K X) := (uniform_precompact_palettes L K hK _ bE).to_subtype
  have hc := Nat.card_le_card_of_injective f hf
  have hbound := initial_palette_quantitative_bound_fin L K hK (Fintype.card F) bE
  refine ⟨uniform_precompact_palettes L K hK F b, ?_⟩
  simpa only [Nat.card_eq_fintype_card (α := F)] using hc.trans hbound.2

/-- `thm:brs`: an actual generic structure in every permitted
positive language has a finite-per-arity big Ramsey expansion. -/
theorem unrestricted_existence :
    let hL : L.FinitePerArity := fun _ => inferInstance
    let K := Existence.GenericConstruction.natModel L hL (fun _ => False)
    let hK := Existence.GenericConstruction.natModel_injective L hL (fun _ => False)
    ∃ eta : ℕ → RelEmbedding K K,
      ∃ Y : RelStructure (expandedSourceLanguage L) ℕ,
        FullStageAgreement L K eta Y ∧ OriginalConclusion L K hK Y ∧ ActiveConclusion L K Y :=
  main_generic_theorem L

/-- The language used by the auxiliary envelope theorem has arities at
least two.  Unary relations in the main theorem are handled by labels. -/
theorem auxiliary_language_has_no_unary (colours : ℕ → ℕ) :
    IsEmpty ((CombinedRamsey.Positive.Marker.hypergraphLanguage colours).Rel 1) :=
  ⟨fun R => by have h := R.property; omega⟩

end CombinedRamsey.Revised20261018.Positive
