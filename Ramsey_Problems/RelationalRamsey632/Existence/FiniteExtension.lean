import RelationalRamsey632.Existence.ExtensionConsequences
import Mathlib.Logic.Equiv.Fin.Basic

namespace RelationalRamsey632.Existence

variable {L : Language} {X : Type}

noncomputable def onePointEquiv (V : Type) [Fintype V] :
    Fin (Fintype.card V + 1) ≃ (V ⊕ Unit) :=
  finSumFinEquiv.symm.trans
    (Equiv.sumCongr (Fintype.equivFin V).symm (Equiv.ofUnique (Fin 1) Unit))

theorem onePointEquiv_old (V : Type) [Fintype V] (v : V) :
    onePointEquiv V (Fintype.equivFin V v).castSucc = Sum.inl v := by
  simp [onePointEquiv, finSumFinEquiv_symm_apply_castSucc]

theorem admissible_pullback {inj : Bool} {V W : Type} (B : RelStructure L W)
    (hB : Admissible inj B) (f : V → W) : Admissible inj (B.pullback f) := by
  intro hi
  exact RelStructure.injectiveRelations_pullback (hB hi) f

/-- The numerical EP gives the actual extension over every finite domain,
with no assumption that the old embedding respects an enumeration. -/
theorem extend_one_point_finite {inj : Bool} {V : Type} [Finite V]
    (K : RelStructure L X) (hK : OnePointExtensionProperty inj K)
    (B : RelStructure L (V ⊕ Unit)) (hB : Admissible inj B)
    (f : RelEmbedding (B.pullback Sum.inl) K) :
    ∃ g : RelEmbedding B K, ∀ v : V, g (Sum.inl v) = f v := by
  classical
  letI := Fintype.ofFinite V
  let phi := onePointEquiv V
  let Bfin := B.pullback phi
  let old : RelEmbedding (Bfin.pullback Fin.castSucc) K := {
    toFun := fun i => f ((Fintype.equivFin V).symm i)
    injective := f.injective.comp (Fintype.equivFin V).symm.injective
    map_rel := by
      intro r R t
      have hpoint : phi ∘ Fin.castSucc ∘ t =
          Sum.inl ∘ (Fintype.equivFin V).symm ∘ t := by
        funext i
        simpa only [Equiv.apply_symm_apply, Function.comp_def] using
          onePointEquiv_old V ((Fintype.equivFin V).symm (t i))
      change B.rel R (phi ∘ Fin.castSucc ∘ t) ↔ _
      rw [hpoint]
      exact f.map_rel R ((Fintype.equivFin V).symm ∘ t) }
  obtain ⟨gfin, hg⟩ := hK (Fintype.card V) Bfin (admissible_pullback B hB phi) old
  let intoFin : RelEmbedding B Bfin := {
    toFun := phi.symm
    injective := phi.symm.injective
    map_rel := by
      intro r R t
      change B.rel R t ↔ B.rel R (phi ∘ phi.symm ∘ t)
      have heq : phi ∘ phi.symm ∘ t = t := by funext i; exact phi.apply_symm_apply (t i)
      rw [heq] }
  refine ⟨gfin.comp intoFin, ?_⟩
  intro v
  have hidx : phi.symm (Sum.inl v) = (Fintype.equivFin V v).castSucc := by
    apply phi.injective
    rw [phi.apply_symm_apply]
    exact (onePointEquiv_old V v).symm
  change gfin (phi.symm (Sum.inl v)) = f v
  rw [hidx, hg]
  change f ((Fintype.equivFin V).symm (Fintype.equivFin V v)) = f v
  rw [Equiv.symm_apply_apply]

end RelationalRamsey632.Existence
