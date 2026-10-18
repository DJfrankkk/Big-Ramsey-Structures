import RelationalRamsey632.Coding.ExpandedSource
import RelationalRamsey632.Source.NormalFormCoherence
import RelationalRamsey632.Transfer.AgeTransport
import RelationalRamsey632.Coding.LevelBoundFormula

namespace RelationalRamsey632.Source

def BoundedNodes (A : ℕ → Type) (B : ℕ) := {t : Node A 0 // t.height < B}

theorem boundedNodes_finite (A : ℕ → Type) [∀ j, Fintype (A j)] (B : ℕ) :
    Finite (BoundedNodes A B) := by
  let f : BoundedNodes A B → Σ n : Fin B, Level A 0 n.val :=
    fun t => ⟨⟨t.val.height, t.property⟩, t.val.table⟩
  let g : (Σ n : Fin B, Level A 0 n.val) → Node A 0 := fun t => ⟨t.fst.val, t.snd⟩
  exact Finite.of_injective f (by
    intro t u h
    apply Subtype.ext
    exact congrArg g h)

def boundedTupleMap {A : ℕ → Type} {U : Type} {n B : ℕ}
    (t : Fin n → U × BoundedNodes A B) : Fin n → U × Node A 0 :=
  fun j => ((t j).1, (t j).2.val)

theorem finite_bounded_tuples (A : ℕ → Type) [∀ j, Fintype (A j)]
    (U : Type) [Finite U] (n B : ℕ) :
    (Set.range (boundedTupleMap (A := A) (U := U) (n := n) (B := B))).Finite := by
  letI := boundedNodes_finite A B
  exact Set.finite_range _

end RelationalRamsey632.Source

namespace RelationalRamsey632.Coding

open Source RelStructure

variable (L : Language) [∀ r, Fintype (L.Rel r)]

def codingNormalForms (K : RelStructure L ℕ) (n : ℕ) : Set (Fin n → DecoderVertex L) :=
  Set.range (fun t : Fin n ↪ ℕ => normalForm (codingMap L K ∘ t))

theorem finite_coding_normal_forms (K : RelStructure L ℕ) (n B : ℕ)
    (hB : ∀ t : Fin n ↪ ℕ, (tupleLevels (codingMap L K ∘ t)).card ≤ B) :
    (codingNormalForms L K n).Finite := by
  classical
  apply (finite_bounded_tuples (ProfileAlphabet L) (UnaryProfile L) n B).subset
  rintro τ ⟨t, rfl⟩
  let s : Fin n → UnaryProfile L × BoundedNodes (ProfileAlphabet L) B :=
    fun j => ((normalForm (codingMap L K ∘ t) j).1,
      ⟨(normalForm (codingMap L K ∘ t) j).2,
        (normalForm_height_bound (codingMap L K ∘ t) j).trans_le (hB t)⟩)
  exact ⟨s, rfl⟩

theorem finite_coding_palette_fin [IsEmpty (L.Rel 0)]
    (K : RelStructure L ℕ) (hK : K.InjectiveRelations) (n : ℕ)
    (hNF : (codingNormalForms L K n).Finite) (b : RelStructure L (Fin n)) :
    (palette b K ((expandedSource L).pullback (codingEmbedding L K hK))).Finite := by
  apply (hNF.image (fun τ => (expandedSource L).pullback τ)).subset
  rintro p ⟨e, rfl⟩
  let t : Fin n ↪ ℕ := ⟨e, e.injective⟩
  refine ⟨normalForm (codingMap L K ∘ t), ⟨t, rfl⟩, ?_⟩
  exact expandedSource_normalForm_pullback L (codingMap L K ∘ t)
    ((codingMap_injective L K).comp e.injective)

theorem finite_coding_palette [IsEmpty (L.Rel 0)]
    (K : RelStructure L ℕ) (hK : K.InjectiveRelations)
    (hNF : ∀ n, (codingNormalForms L K n).Finite)
    (F : Type) [Finite F] (b : RelStructure L F) :
    (palette b K ((expandedSource L).pullback (codingEmbedding L K hK))).Finite := by
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
  letI : Finite (palette bE K X) :=
    (finite_coding_palette_fin L K hK (Fintype.card F) (hNF _) bE).to_subtype
  haveI : Finite (palette b K X) := Finite.of_injective f (by
    intro p q h
    apply Subtype.ext
    exact Transfer.pullback_injective_of_surjective u E.symm.surjective
      (congrArg (fun z : palette bE K X => z.val) h))
  exact Set.toFinite _

def CodingSeparated (K : RelStructure L ℕ) : Prop :=
  SeparatedAtAllDepths (Set.range (family (profileSize L) (relationCodes L K)))
    (originalPositions (profileSize L))

theorem coding_tuple_level_bound (K : RelStructure L ℕ) (hsep : CodingSeparated L K)
    (n : ℕ) (t : Fin n ↪ ℕ) :
    (tupleLevels (codingMap L K ∘ t)).card ≤ levelBound n := by
  let X := tupleProjections (codingMap L K ∘ t)
  have hXR : X ⊆ Set.range (family (profileSize L) (relationCodes L K)) := by
    rintro s ⟨j, hj⟩
    exact ⟨t j, hj⟩
  have hi : Function.Injective (fun j : Fin n => (codingMap L K (t j)).2) := by
    intro i j h
    apply t.injective
    apply (originalHeight_strictMono (profileSize L)).injective
    exact congrArg Node.height h
  have hcard : Nat.card X = n := by
    change Nat.card (Set.range (fun j : Fin n => (codingMap L K (t j)).2)) = n
    rw [Nat.card_range_of_injective hi, Nat.card_fin]
  have hb := separated_closure_level_bound hsep hXR (tupleProjections_finite (codingMap L K ∘ t))
  rw [hcard, ← tupleLevels_coe] at hb
  simpa only [Nat.card_coe_set_eq, Set.ncard_coe_finset] using hb

theorem separated_finite_normal_forms (K : RelStructure L ℕ) (hsep : CodingSeparated L K)
    (n : ℕ) : (codingNormalForms L K n).Finite :=
  finite_coding_normal_forms L K n (levelBound n) (coding_tuple_level_bound L K hsep n)

theorem separated_precompact_palettes [IsEmpty (L.Rel 0)]
    (K : RelStructure L ℕ) (hK : K.InjectiveRelations) (hsep : CodingSeparated L K)
    (F : Type) [Finite F] (b : RelStructure L F) :
    (palette b K ((expandedSource L).pullback (codingEmbedding L K hK))).Finite :=
  finite_coding_palette L K hK (separated_finite_normal_forms L K hsep) F b

end RelationalRamsey632.Coding
