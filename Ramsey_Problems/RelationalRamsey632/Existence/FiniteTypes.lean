import RelationalRamsey632.Model
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega

/-! Finite labelled state spaces in the two affirmative existence ranges. -/

namespace RelationalRamsey632

namespace RelStructure

variable {L : Language} {X : Type}

theorem injectiveTuple_arity_le [Fintype X] (A : RelStructure L X)
    (hA : A.InjectiveRelations) {r : ℕ} (R : L.Rel r) (t : Fin r → X)
    (hr : 0 < r) (ht : A.rel R t) : r ≤ Fintype.card X := by
  simpa using Fintype.card_le_of_injective t (hA r R t hr ht)

theorem high_arity_false {n r : ℕ} (A : RelStructure L (Fin n)) (hA : A.InjectiveRelations)
    (R : L.Rel r) (t : Fin r → Fin n) (hr : n < r) :
    ¬ A.rel R t := by
  intro ht
  have hp : 0 < r := by omega
  have hle := A.injectiveTuple_arity_le hA R t hp ht
  exact (Nat.not_le_of_lt hr) (by simpa using hle)

end RelStructure

namespace Existence

variable (L : Language)

abbrev InjectiveStructure (X : Type) :=
  {A : RelStructure L X // A.InjectiveRelations}

abbrev FiniteInjectiveCode (n : ℕ) :=
  (r : Fin (n + 1)) → L.Rel r.val → (Fin r.val → Fin n) → Bool

noncomputable def injectiveCode (n : ℕ) (A : InjectiveStructure L (Fin n)) :
    FiniteInjectiveCode L n := by
  classical
  exact fun r R t => decide (A.val.rel R t)

theorem injectiveCode_injective (n : ℕ) : Function.Injective (injectiveCode L n) := by
  classical
  intro A B h
  apply Subtype.ext
  apply RelStructure.ext_rel
  intro r R t
  by_cases hr : r ≤ n
  · have hb := congrFun (congrFun (congrFun h ⟨r, by omega⟩) R) t
    simpa [injectiveCode] using hb
  · have hgt : n < r := Nat.lt_of_not_ge hr
    exact iff_of_false (A.val.high_arity_false A.property R t hgt)
      (B.val.high_arity_false B.property R t hgt)

theorem finite_injective_structures (hL : L.FinitePerArity) (n : ℕ) :
    Finite (InjectiveStructure L (Fin n)) := by
  letI : ∀ r, Finite (L.Rel r) := hL
  exact Finite.of_injective (injectiveCode L n) (injectiveCode_injective L n)

theorem finite_injective_structures_on_finite (hL : L.FinitePerArity)
    (X : Type) [Finite X] : Finite (InjectiveStructure L X) := by
  classical
  letI := Fintype.ofFinite X
  let e : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  let f : InjectiveStructure L X → InjectiveStructure L (Fin (Fintype.card X)) :=
    fun A => ⟨A.val.pullback e.symm, A.val.injectiveRelations_pullback A.property e.symm⟩
  letI := finite_injective_structures L hL (Fintype.card X)
  apply Finite.of_injective f
  intro A B h
  apply Subtype.ext
  apply RelStructure.ext_rel
  intro r R t
  have hv := congrArg Subtype.val h
  have ht := congrArg (fun S : RelStructure L (Fin (Fintype.card X)) => S.rel R (e ∘ t)) hv
  simpa [f, RelStructure.pullback, Function.comp_def] using ht

theorem countable_labelled_injective_structures (hL : L.FinitePerArity) :
    Countable ((n : ℕ) × InjectiveStructure L (Fin n)) := by
  letI : ∀ n, Finite (InjectiveStructure L (Fin n)) :=
    finite_injective_structures L hL
  infer_instance

abbrev OrdinaryCode (n : ℕ) :=
  (s : Sigma L.Rel) → (Fin s.1 → Fin n) → Bool

noncomputable def ordinaryCode (n : ℕ) (A : RelStructure L (Fin n)) :
    OrdinaryCode L n := by
  classical
  exact fun s t => decide (A.rel s.2 t)

theorem ordinaryCode_injective (n : ℕ) : Function.Injective (ordinaryCode L n) := by
  classical
  intro A B h
  apply RelStructure.ext_rel
  intro r R t
  have hb := congrFun (congrFun h ⟨r, R⟩) t
  simpa [ordinaryCode] using hb

theorem finite_ordinary_structures [Finite (Sigma L.Rel)] (n : ℕ) :
    Finite (RelStructure L (Fin n)) :=
  Finite.of_injective (ordinaryCode L n) (ordinaryCode_injective L n)

end Existence

end RelationalRamsey632
