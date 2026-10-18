import RelationalRamsey632.Existence.Affirmative
import Mathlib.Logic.Denumerable

namespace RelationalRamsey632.Existence

variable {L : Language} {X Y : Type}

def forwardDomainEmbedding (K : RelStructure L X) (E : X ≃ Y) :
    RelEmbedding K (K.pullback E.symm) where
  toFun := E
  injective := E.injective
  map_rel R t := by
    have he : E.symm ∘ E ∘ t = t := by
      funext j
      exact E.symm_apply_apply (t j)
    change K.rel R t ↔ K.rel R (E.symm ∘ E ∘ t)
    rw [he]

theorem extensionProperty_domainEquiv {inj : Bool} (K : RelStructure L X)
    (hEP : OnePointExtensionProperty inj K) (E : X ≃ Y) :
    OnePointExtensionProperty inj (K.pullback E.symm) := by
  intro n B hB f
  let back := RelEmbedding.pullback K E.symm E.symm.injective
  obtain ⟨g, hg⟩ := hEP n B hB (back.comp f)
  refine ⟨(forwardDomainEmbedding K E).comp g, ?_⟩
  intro j
  change E (g j.castSucc) = f j
  rw [hg]
  exact E.apply_symm_apply (f j)

namespace GenericConstruction

variable (L : Language) (hL : L.FinitePerArity) (θ : L.Rel 0 → Prop)

noncomputable def limitEquivNat : Limit L true hL θ ≃ ℕ := by
  haveI := countable_limit L true hL θ
  haveI := infinite_limit L true hL θ
  exact Classical.choice (inferInstance : Nonempty (Limit L true hL θ ≃ ℕ))

noncomputable def natModel : RelStructure L ℕ :=
  (limitModel L true hL θ).pullback (limitEquivNat L hL θ).symm

theorem natModel_injective : (natModel L hL θ).InjectiveRelations :=
  RelStructure.injectiveRelations_pullback (limit_admissible L true hL θ rfl) _

theorem natModel_EP : OnePointExtensionProperty true (natModel L hL θ) :=
  extensionProperty_domainEquiv _ (extension_property L true hL θ) (limitEquivNat L hL θ)

theorem natModel_nullary : ∀ (R : L.Rel 0) (t : Fin 0 → ℕ),
    (natModel L hL θ).rel R t ↔ θ R := by
  intro R t
  exact limit_nullary L true hL θ R ((limitEquivNat L hL θ).symm ∘ t)

theorem natModel_ultrahomogeneous :
    @FirstOrder.Language.IsUltrahomogeneous L.toFirstOrder ℕ (natModel L hL θ).toFirstOrder :=
  ultrahomogeneous_of_EP _ (fun _ => natModel_injective L hL θ) (natModel_EP L hL θ)

end GenericConstruction
end RelationalRamsey632.Existence
