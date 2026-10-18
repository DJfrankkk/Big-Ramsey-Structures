import RelationalRamsey632.Source.NormalForms
import RelationalRamsey632.Source.CompressionConsequences

/-! Consecutive compressed closure levels and idempotent literal normal forms. -/

namespace RelationalRamsey632.Source

theorem normalForm_projections {A : ℕ → Type} {U : Type} {b : ℕ}
    (v : Fin b → U × Node A 0) :
    tupleProjections (normalForm v) =
      canonicalCompression (tupleLevels v) '' tupleProjections v := by
  apply Set.Subset.antisymm
  · rintro t ⟨j, hj⟩
    exact ⟨(v j).2, ⟨j, rfl⟩, hj⟩
  · rintro t ⟨s, ⟨j, hj⟩, hs⟩
    exact ⟨j, (congrArg (canonicalCompression (tupleLevels v)) hj).trans hs⟩

theorem tupleLevels_normalForm {A : ℕ → Type} {U : Type} {b : ℕ}
    (v : Fin b → U × Node A 0) :
    tupleLevels (normalForm v) = Finset.range (tupleLevels v).card := by
  apply Finset.coe_injective
  rw [tupleLevels_coe, normalForm_projections]
  exact (canonical_compression_closure (tupleLevels v) (tupleLevels_coe v).symm).2

theorem normalForm_height_bound {A : ℕ → Type} {U : Type} {b : ℕ}
    (v : Fin b → U × Node A 0) (j : Fin b) :
    (normalForm v j).2.height < (tupleLevels v).card := by
  apply canonicalCompression_height_bound (tupleLevels v) (v j).2
  change (v j).2.height ∈ (tupleLevels v : Set ℕ)
  rw [tupleLevels_coe]
  exact Generated.height _ (Generated.generator _ ⟨j, rfl⟩)

theorem normalForm_idempotent {A : ℕ → Type} {U : Type} {b : ℕ}
    (v : Fin b → U × Node A 0) :
    normalForm (normalForm v) = normalForm v := by
  funext j
  apply Prod.ext
  · rfl
  · change canonicalCompression (tupleLevels (normalForm v)) (normalForm v j).2 =
      (normalForm v j).2
    rw [tupleLevels_normalForm]
    exact canonicalCompression_range_identity (tupleLevels v).card
      (normalForm v j).2 (normalForm_height_bound v j)

end RelationalRamsey632.Source
