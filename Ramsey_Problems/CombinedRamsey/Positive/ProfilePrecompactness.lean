import CombinedRamsey.Positive.ProfileExpandedSource
import CombinedRamsey.Positive.UniformNormalForms
import RelationalRamsey632.Transfer.AgeTransport
import RelationalRamsey632.Transfer.UniformStabilization

namespace CombinedRamsey.Positive.Relational

open RelationalRamsey632 RelationalRamsey632.Source RelationalRamsey632.RelStructure RelationalRamsey632.Coding

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
  let u : RelationalRamsey632.RelEmbedding bE b := RelationalRamsey632.RelEmbedding.pullback b E.symm E.symm.injective
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

theorem uniform_finite_normal_forms (K : RelStructure L ℕ) (n : ℕ) :
    (codingNormalForms L K n).Finite := by
  have h := Marker.uniform_normalFormImage_bound (profileColours L) (relationCodes L K)
    (unaryAt L K) n
  exact h.1

theorem uniform_precompact_palettes [IsEmpty (L.Rel 0)]
    (K : RelStructure L ℕ) (hK : K.InjectiveRelations) (F : Type) [Finite F] (b : RelStructure L F) :
    (palette b K ((expandedSource L).pullback (codingEmbedding L K hK))).Finite :=
  finite_coding_palette L K hK (uniform_finite_normal_forms L K) F b

theorem uniform_source_conditions [IsEmpty (L.Rel 0)]
    (K : RelStructure L ℕ) (hK : K.InjectiveRelations) :
    Transfer.PrecompactSource (expandedSource L) (codingEmbedding L K hK) := by
  intro F _ b _
  refine ⟨uniform_precompact_palettes L K hK F b, ?_⟩
  intro p hp
  obtain ⟨e, he⟩ := hp
  let f := (codingEmbedding L K hK).comp e
  have hf : (expandedSource L).pullback f = p := he
  let u : RelationalRamsey632.RelEmbedding p (expandedSource L) := by
    rw [← hf]
    exact RelationalRamsey632.RelEmbedding.pullback (expandedSource L) f f.injective
  exact source_degree_one_lift L p u
    (sourceDegreeOne (p.reduct (nfInclusion L)) ⟨nfReductEmbedding L u⟩)

end CombinedRamsey.Positive.Relational

