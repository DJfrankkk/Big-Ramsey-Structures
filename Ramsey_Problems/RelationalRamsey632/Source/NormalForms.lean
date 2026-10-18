import RelationalRamsey632.Source.CompressionMeets

/-! Literal ordered normal forms for tuples of labelled source nodes. -/

namespace RelationalRamsey632.Source

theorem closureLevels_finite_of_finite {A : ℕ → Type} {X : Set (Node A 0)}
    (hX : X.Finite) : (closureLevels A X).Finite := by
  classical
  apply closureLevels_finite A (H := hX.toFinset.sup Node.height)
  intro t ht
  exact Finset.le_sup (f := Node.height) (hX.mem_toFinset.mpr ht)

def tupleProjections {A : ℕ → Type} {U : Type} {b : ℕ}
    (v : Fin b → U × Node A 0) : Set (Node A 0) :=
  Set.range (fun j => (v j).2)

theorem tupleProjections_finite {A : ℕ → Type} {U : Type} {b : ℕ}
    (v : Fin b → U × Node A 0) : (tupleProjections v).Finite :=
  Set.finite_range _

noncomputable def tupleLevels {A : ℕ → Type} {U : Type} {b : ℕ}
    (v : Fin b → U × Node A 0) : Finset ℕ :=
  (closureLevels_finite_of_finite (tupleProjections_finite v)).toFinset

theorem tupleLevels_coe {A : ℕ → Type} {U : Type} {b : ℕ}
    (v : Fin b → U × Node A 0) :
    (tupleLevels v : Set ℕ) = closureLevels A (tupleProjections v) :=
  (closureLevels_finite_of_finite (tupleProjections_finite v)).coe_toFinset

noncomputable def normalForm {A : ℕ → Type} {U : Type} {b : ℕ}
    (v : Fin b → U × Node A 0) : Fin b → U × Node A 0 :=
  fun j => ((v j).1, canonicalCompression (tupleLevels v) (v j).2)

@[simp] theorem normalForm_label {A : ℕ → Type} {U : Type} {b : ℕ}
    (v : Fin b → U × Node A 0) (j : Fin b) :
    (normalForm v j).1 = (v j).1 := rfl

theorem normalForm_injective {A : ℕ → Type} {U : Type} {b : ℕ}
    (v : Fin b → U × Node A 0) (hinj : Function.Injective v) :
    Function.Injective (normalForm v) := by
  intro j k hjk
  have hlabels : (v j).1 = (v k).1 := by
    simpa only [normalForm] using congrArg (fun p : U × Node A 0 => p.1) hjk
  have hnodes : canonicalCompression (tupleLevels v) (v j).2 =
      canonicalCompression (tupleLevels v) (v k).2 := by
    simpa only [normalForm] using congrArg (fun p : U × Node A 0 => p.2) hjk
  have hsource := canonicalCompression_injective_on_closure
    (tupleLevels v) (tupleLevels_coe v).symm 0
    (Generated.generator _ ⟨j, rfl⟩) (Generated.generator _ ⟨k, rfl⟩) hnodes
  apply hinj
  exact Prod.ext hlabels hsource

end RelationalRamsey632.Source
