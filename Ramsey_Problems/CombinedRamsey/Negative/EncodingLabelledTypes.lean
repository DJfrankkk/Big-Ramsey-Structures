import CombinedRamsey.Negative.EncodingRealizations
import CombinedRamsey.Negative.PersistenceTypes

/-! Literal finite labelled pointed types used by the persistence theorem. -/

namespace CombinedRamsey.Negative

open RelationalRamsey632

variable {k : ℕ}

def deltaTable : Table Unit where
  unary u _ := u = .V
  binary _ _ _ := False
  ternary _ _ _ _ := False

def delta : RelStructure language Unit := deltaTable.toRel

noncomputable abbrev boundarySize (H : Digraph (Fin k)) := Nat.card (EncodedBoundary H)

noncomputable def boundaryEnum (H : Digraph (Fin k)) :
    Fin (boundarySize H) ≃ EncodedBoundary H := by
  classical
  letI := Fintype.ofFinite (EncodedBoundary H)
  simpa [boundarySize, Nat.card_eq_fintype_card] using (Fintype.equivFin (EncodedBoundary H)).symm

noncomputable def labelledPointEquiv (H : Digraph (Fin k)) :
    (Fin (boundarySize H) ⊕ Unit) ≃ (EncodedBoundary H ⊕ Unit) :=
  Equiv.sumCongr (boundaryEnum H) (Equiv.refl Unit)

noncomputable def labelledType (H : Digraph (Fin k)) :
    RelStructure language (Fin (boundarySize H) ⊕ Unit) :=
  (typeTable H).toRel.pullback (labelledPointEquiv H)

noncomputable def labelledBase {X : Type} (H : Digraph (Fin k))
    (K : RelStructure language X) (b : RelEmbedding (boundary H).toRel K) :
    RelEmbedding ((labelledType H).pullback Sum.inl) K where
  toFun a := b (boundaryEnum H a)
  injective := b.injective.comp (boundaryEnum H).injective
  map_rel R t := by
    have he := congrArg (fun A => A.rel R (boundaryEnum H ∘ t)) (boundary_type_reduct H)
    exact (Iff.of_eq he).trans (b.map_rel R (boundaryEnum H ∘ t))

theorem type_singleton (H : Digraph (Fin k)) :
    (typeTable H).toRel.pullback (fun _ : Unit => Sum.inr ()) = delta := by
  apply RelStructure.ext_rel
  intro r R t
  cases R <;> simp [RelStructure.pullback, Table.toRel, typeTable, delta, deltaTable]

theorem labelled_type_singleton (H : Digraph (Fin k)) :
    (labelledType H).pullback (fun _ : Unit => Sum.inr ()) = delta := by
  unfold labelledType
  rw [RelStructure.pullback_comp]
  exact type_singleton H

theorem labelled_realizations_eq {X : Type} (H : Digraph (Fin k))
    (K : RelStructure language X) (b : RelEmbedding (boundary H).toRel K) :
    Realizations (labelledType H) K (labelledBase H K b) = EncodedRealizations H K b := by
  apply Set.ext
  intro x
  constructor
  · rintro ⟨p,hp,hstar⟩
    let fromOriginal : RelEmbedding (typeTable H).toRel (labelledType H) := {
      toFun := (labelledPointEquiv H).symm
      injective := (labelledPointEquiv H).symm.injective
      map_rel := fun R t => by
        change (typeTable H).toRel.rel R t ↔
          (typeTable H).toRel.rel R (labelledPointEquiv H ∘ (labelledPointEquiv H).symm ∘ t)
        simp [Function.comp_def] }
    refine ⟨p.comp fromOriginal, ?_, ?_⟩
    · intro a
      change p (.inl ((boundaryEnum H).symm a)) = b a
      rw [hp]
      change b (boundaryEnum H ((boundaryEnum H).symm a)) = b a
      rw [Equiv.apply_symm_apply]
    · exact hstar
  · rintro ⟨p,hp,hstar⟩
    let intoOriginal := RelEmbedding.pullback (typeTable H).toRel (labelledPointEquiv H)
      (labelledPointEquiv H).injective
    refine ⟨p.comp intoOriginal, ?_, ?_⟩
    · intro a
      exact hp (boundaryEnum H a)
    · exact hstar

end CombinedRamsey.Negative
