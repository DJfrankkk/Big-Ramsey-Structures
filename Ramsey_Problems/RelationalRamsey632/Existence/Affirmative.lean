import RelationalRamsey632.Existence.LimitProperties
import RelationalRamsey632.Existence.Homogeneity
import RelationalRamsey632.Existence.FreeAmalgamation

/-!
The affirmative existence theorem instantiated as an actual Mathlib Fraïssé
limit of the fixed-nullary class, with uniqueness and countable universality.
-/

namespace RelationalRamsey632.Existence

open scoped FirstOrder

instance countableNativeFunctions (L : Language) :
    Countable ((n : ℕ) × L.toFirstOrder.Functions n) := by
  change Countable ((n : ℕ) × Empty)
  infer_instance

def finiteClass (L : Language) (inj : Bool) (θ : L.Rel 0 → Prop) :
    Set (CategoryTheory.Bundled.{0} L.toFirstOrder.Structure) :=
  fun B => Finite B ∧ Admissible inj (RelStructure.ofFirstOrder B.str) ∧
    FixedNullary L θ (RelStructure.ofFirstOrder B.str)

namespace GenericConstruction

variable (L : Language) (inj : Bool) (hL : LocallyFiniteLanguage L inj)
variable (θ : L.Rel 0 → Prop)

instance countableGeneric : Countable (Limit L inj hL θ) :=
  countable_limit L inj hL θ

theorem native_age :
    @FirstOrder.Language.age L.toFirstOrder (Limit L inj hL θ)
      (limitModel L inj hL θ).toFirstOrder = finiteClass L inj θ := by
  letI := (limitModel L inj hL θ).toFirstOrder
  ext B
  constructor
  · rintro ⟨hFG, ⟨f⟩⟩
    haveI : Finite B := hFG.finite
    let e : RelEmbedding (RelStructure.ofFirstOrder B.str) (limitModel L inj hL θ) := {
      toFun := f
      injective := f.injective
      map_rel := fun R t => (f.map_rel' R t).symm }
    exact ⟨inferInstance,
      (finite_age_exact L inj hL θ (RelStructure.ofFirstOrder B.str)).mp ⟨e⟩⟩
  · rintro ⟨hFin, hB, hθ⟩
    letI := hFin
    obtain ⟨e⟩ := universal L inj hL θ (RelStructure.ofFirstOrder B.str) hB hθ
    refine ⟨FirstOrder.Language.Structure.FG.of_finite, ⟨?_⟩⟩
    exact {
      toFun := e
      inj' := e.injective
      map_fun' := fun F => Empty.elim F
      map_rel' := fun R t => (e.map_rel R t).symm }

theorem isFraisseLimit :
    letI := (limitModel L inj hL θ).toFirstOrder
    FirstOrder.Language.IsFraisseLimit (finiteClass L inj θ) (Limit L inj hL θ) := by
  letI := (limitModel L inj hL θ).toFirstOrder
  exact {
    ultrahomogeneous := ultrahomogeneous_of_EP (limitModel L inj hL θ)
      (limit_admissible L inj hL θ) (extension_property L inj hL θ)
    age := native_age L inj hL θ }

include hL in
theorem isFraisse : FirstOrder.Language.IsFraisse (finiteClass L inj θ) := by
  letI := (limitModel L inj hL θ).toFirstOrder
  exact (isFraisseLimit L inj hL θ).isFraisse

theorem unique {V : Type} [Countable V] [L.toFirstOrder.Structure V]
    (hV : FirstOrder.Language.IsFraisseLimit (finiteClass L inj θ) V) :
    letI := (limitModel L inj hL θ).toFirstOrder
    Nonempty (FirstOrder.Language.Equiv L.toFirstOrder (Limit L inj hL θ) V) := by
  letI := (limitModel L inj hL θ).toFirstOrder
  exact (isFraisseLimit L inj hL θ).nonempty_equiv hV

end GenericConstruction

theorem injective_fixednullary_isFraisse (L : Language) (hL : L.FinitePerArity)
    (θ : L.Rel 0 → Prop) : FirstOrder.Language.IsFraisse (finiteClass L true θ) :=
  GenericConstruction.isFraisse L true hL θ

theorem ordinary_fixednullary_isFraisse (L : Language)
    [Finite (L.Rel 0)] [Finite L.PositiveSymbol] (θ : L.Rel 0 → Prop) :
    FirstOrder.Language.IsFraisse (finiteClass L false θ) :=
  GenericConstruction.isFraisse L false
    (L.finite_symbols_of_finite_positive) θ

theorem ordinary_infinite_not_isFraisse (L : Language) [Infinite L.PositiveSymbol]
    (θ : L.Rel 0 → Prop) : ¬ FirstOrder.Language.IsFraisse (finiteClass L false θ) := by
  classical
  intro h
  obtain ⟨M, hCG, hage⟩ := FirstOrder.Language.exists_cg_is_age_of
    h.is_nonempty h.is_essentially_countable h.FG h.hereditary h.jointEmbedding
  haveI : Countable M := FirstOrder.Language.Structure.cg_iff_countable.mp hCG
  let K := RelStructure.ofFirstOrder M.str
  apply no_countable_ordinary_universal L K θ
  intro b
  let B : CategoryTheory.Bundled.{0} L.toFirstOrder.Structure :=
    ⟨Unit, (ordinarySingleton L θ b).toFirstOrder⟩
  letI : L.toFirstOrder.Structure B := B.str
  have hAd : Admissible false (RelStructure.ofFirstOrder B.str) := by
    intro hi
    cases hi
  have hB : B ∈ finiteClass L false θ :=
    ⟨inferInstance, hAd, ordinarySingleton_nullary L θ b⟩
  have hBM : B ∈ L.toFirstOrder.age M := by
    rw [hage]
    exact hB
  obtain ⟨_, ⟨f⟩⟩ := hBM
  exact ⟨{
    toFun := f
    injective := f.injective
    map_rel := fun R t => (f.map_rel' R t).symm }⟩

theorem ordinary_fixednullary_isFraisse_iff (L : Language) [Finite (L.Rel 0)]
    (θ : L.Rel 0 → Prop) :
    FirstOrder.Language.IsFraisse (finiteClass L false θ) ↔ Finite L.PositiveSymbol := by
  constructor
  · intro h
    by_contra hf
    haveI := not_finite_iff_infinite.mp hf
    exact ordinary_infinite_not_isFraisse L θ h
  · intro hf
    letI := hf
    exact ordinary_fixednullary_isFraisse L θ

theorem ordinary_infinite_no_FraisseLimit (L : Language) [Infinite L.PositiveSymbol]
    (θ : L.Rel 0 → Prop) {V : Type} [Countable V] [L.toFirstOrder.Structure V] :
    ¬ FirstOrder.Language.IsFraisseLimit (finiteClass L false θ) V := by
  intro h
  exact ordinary_infinite_not_isFraisse L θ h.isFraisse

end RelationalRamsey632.Existence
