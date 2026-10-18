import CombinedRamsey.Negative.OrdinaryBRS

/-! The actual constructed Kstar is a native Mathlib Fraisse limit of
the full finite injective forbidden class. This is not an assumed limit. -/

namespace CombinedRamsey.Negative

open RelationalRamsey632
open scoped FirstOrder

def nativeForbiddenClass : Set (CategoryTheory.Bundled.{0} Lstar.toFirstOrder.Structure) :=
  fun B => Finite B ∧ ForbStar (RelStructure.ofFirstOrder B.str)

theorem Kstar_native_age :
    letI := Kstar.toFirstOrder
    Lstar.toFirstOrder.age ℕ = nativeForbiddenClass := by
  letI := Kstar.toFirstOrder
  ext B
  constructor
  · rintro ⟨hFG, ⟨f⟩⟩
    haveI : Finite B := hFG.finite
    let e : RelEmbedding (RelStructure.ofFirstOrder B.str) Kstar := {
      toFun := f
      injective := f.injective
      map_rel := fun R t => (f.map_rel' R t).symm }
    exact ⟨inferInstance, (Kstar_age_exact (RelStructure.ofFirstOrder B.str)).mp ⟨e⟩⟩
  · rintro ⟨hFin, hB⟩
    letI := hFin
    obtain ⟨e⟩ := (Kstar_age_exact (RelStructure.ofFirstOrder B.str)).mpr hB
    refine ⟨FirstOrder.Language.Structure.FG.of_finite, ⟨?_⟩⟩
    exact {
      toFun := e
      inj' := e.injective
      map_fun' := fun F => Empty.elim F
      map_rel' := fun R t => (e.map_rel R t).symm }

theorem Kstar_isFraisseLimit :
    letI := Kstar.toFirstOrder
    FirstOrder.Language.IsFraisseLimit nativeForbiddenClass ℕ := by
  letI := Kstar.toFirstOrder
  exact ⟨Kstar_ultrahomogeneous, Kstar_native_age⟩

theorem forbidden_class_isFraisse : FirstOrder.Language.IsFraisse nativeForbiddenClass := by
  letI := Kstar.toFirstOrder
  exact Kstar_isFraisseLimit.isFraisse

end CombinedRamsey.Negative
