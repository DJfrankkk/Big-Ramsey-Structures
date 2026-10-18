import RelationalRamsey632.Source.TupleEnvelopes

/-!
# The finite-core vector Milliken reduction

VectorMilliken is the explicit interface of this reusable reduction.
It is supplied by the internal proof in Milliken.SourceSpecialization
when CompleteRamsey derives the unconditional source theorem. Its colors
inspect only the first h coordinate trees and their first h selected levels.

The theorem below proves the remaining source-Ramsey implication,
including actual relational embeddings, actual marked occurrences, and
independence of irrelevant finite-vector record data.
-/

namespace RelationalRamsey632.Source

structure FiniteFrame (A : ℕ → Type) (h : ℕ) where
  level : ℕ → ℕ
  level_mono : StrictMono level
  vector : FiniteStrongVector A level level_mono h

abbrev RealizedVectorCore (A : ℕ → Type) (h : ℕ) :=
  {C : FiniteVectorCore A h // ∃ F : FiniteFrame A h, F.vector.core = C}

namespace FiniteStrongVector

noncomputable def realizedCore {A : ℕ → Type} {e : ℕ → ℕ} {he : StrictMono e} {h : ℕ}
    (V : FiniteStrongVector A e he h) : RealizedVectorCore A h :=
  ⟨V.core, ⟨⟨e, he, V⟩, rfl⟩⟩

end FiniteStrongVector

/-- The source specialization of the finite-dimensional vector theorem.
The infinite coordinates not read by the color are completion data. -/
def VectorMilliken (A : ℕ → Type) : Prop :=
  ∀ h : ℕ, 0 < h → ∀ (D : Type) [Fintype D],
    ∀ c : RealizedVectorCore A h → D,
      ∃ e : ℕ → ℕ, ∃ he : StrictMono e,
      ∃ S : StrongVector A e he, ∃ a : D,
        ∀ l : ℕ → ℕ, ∀ hl : StrictMono l,
        ∀ V : FiniteStrongVector A (e ∘ l) (he.comp hl) h,
          (∀ i n, i < h → n < h → V.nodes i n ⊆ S.nodes i (l n)) →
            c V.realizedCore = a

noncomputable def finiteCoreEmbedding {A : ℕ → Type} {U F : Type} {h : ℕ}
    (p : RelStructure (normalFormLanguage A U) F)
    (k : RelEmbedding p (normalFormStructure A U)) (hk : ∀ x, (k x).2.height < h)
    (C : RealizedVectorCore A h) : RelEmbedding p (normalFormStructure A U) :=
  let F := Classical.choose C.property
  F.vector.imageEmbedding p k hk

theorem finiteCoreEmbedding_realized {A : ℕ → Type} {U F : Type}
    {e : ℕ → ℕ} {he : StrictMono e} {h : ℕ}
    (V : FiniteStrongVector A e he h)
    (p : RelStructure (normalFormLanguage A U) F)
    (k : RelEmbedding p (normalFormStructure A U)) (hk : ∀ x, (k x).2.height < h) :
    finiteCoreEmbedding p k hk V.realizedCore = V.imageEmbedding p k hk := by
  let F := Classical.choose V.realizedCore.property
  have hcore : F.vector.core = V.core := Classical.choose_spec V.realizedCore.property
  exact F.vector.imageEmbedding_eq_of_core p V hcore k hk

/-- Only the named external vector theorem remains a parameter; none of
the source normal-form, envelope, or relational steps are assumed. -/
theorem sourceDegreeOne_of_vectorMilliken {A : ℕ → Type}
    [∀ j, Fintype (A j)] [∀ j, Nonempty (A j)] {U F : Type} [Finite F]
    (hMilliken : VectorMilliken A)
    (p : RelStructure (normalFormLanguage A U) F)
    (hp : Nonempty (RelEmbedding p (normalFormStructure A U))) :
    Transfer.SourceDegreeOne (normalFormStructure A U) p := by
  classical
  letI := Fintype.ofFinite F
  let j := Classical.choice hp
  intro D _ c
  by_cases hF : Nonempty F
  · let H := (tupleLevels (patternTuple p j)).card
    let k := patternEmbedding p j
    have hk : ∀ x, (k x).2.height < H := patternEmbedding_height p j
    have hH : 0 < H := by
      have hx := hk (Classical.choice hF)
      omega
    let d : RealizedVectorCore A H → D := fun C => c (finiteCoreEmbedding p k hk C)
    obtain ⟨e, he, S, a, hS⟩ := hMilliken H hH D d
    let ζ := S.relationalEmbedding (U := U)
    have hconst : ∀ g : RelEmbedding p (normalFormStructure A U), c (ζ.comp g) = a := by
      intro g
      let v := g ∘ (Fintype.equivFin F).symm
      have hnF : 0 < Fintype.card F := Fintype.card_pos_iff.mpr hF
      have hnf : normalForm (patternTuple p j) = normalForm v :=
        normalForm_of_finiteEmbedding A U p j g hnF
          (Fintype.equivFin F).symm (Fintype.equivFin F).symm.injective
      have hdim : (tupleLevels v).card = H := by
        have h := congrArg tupleLevels hnf
        rw [tupleLevels_normalForm, tupleLevels_normalForm] at h
        simpa only [Finset.card_range] using (congrArg Finset.card h).symm
      obtain ⟨V, hrelative, hmark⟩ := S.marked_tuple_envelope_height v H hdim
      have hEmb : V.imageEmbedding p k hk = ζ.comp g := by
        apply RelEmbedding.ext
        intro x
        have hx := hmark ((Fintype.equivFin F) x)
        rw [← hnf] at hx
        simpa only [FiniteStrongVector.imageEmbedding, patternEmbedding_apply,
          patternMap, k, v, ζ, StrongVector.relationalEmbedding_apply,
          RelEmbedding.comp_apply, Function.comp_apply, Equiv.symm_apply_apply] using hx
      have hd := hS (levelEnumeration (tupleLevels v))
        (levelEnumeration_strictMono (tupleLevels v)) V (fun i n _ _ => hrelative i n)
      change c (finiteCoreEmbedding p k hk V.realizedCore) = a at hd
      rw [finiteCoreEmbedding_realized, hEmb] at hd
      exact hd
    exact ⟨ζ, fun u v => (hconst u).trans (hconst v).symm⟩
  · haveI : IsEmpty F := not_nonempty_iff.mp hF
    refine ⟨RelEmbedding.refl _, ?_⟩
    intro u v
    apply congrArg c
    apply RelEmbedding.ext
    intro x
    exact isEmptyElim x

end RelationalRamsey632.Source
