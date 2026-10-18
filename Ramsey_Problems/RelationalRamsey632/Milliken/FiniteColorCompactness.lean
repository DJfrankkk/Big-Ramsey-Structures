import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Push

/-! The finite compactness step used to synchronize mixed-height dense
matrices. It is proved via pointwise finite ultrafilter limits, rather than
assumed as an external Ramsey principle. -/

namespace RelationalRamsey632.Milliken

open Filter

def Monochromatic {X K : Type} (c : X → K) (s : Finset X) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, c x = c y

/-- If every finite coloring has a finite valid witness, one bounded
finite domain contains a witness for every coloring. Validity is arbitrary
but independent of the coloring. This is the exact compactness principle
in the proof SDHL → finite SDHL. -/
theorem finite_color_compactness {X K W : Type} [Fintype K]
    (support : W → Finset X) (Valid : W → Prop) (domain : ℕ → Finset X)
    (hcover : ∀ x : X, ∀ᶠ n in atTop, x ∈ domain n)
    (hglobal : ∀ c : X → K, ∃ w : W, Valid w ∧ Monochromatic c (support w)) :
    ∃ n, ∀ c : X → K, ∃ w : W,
      Valid w ∧ support w ⊆ domain n ∧ Monochromatic c (support w) := by
  classical
  by_contra hfail
  have hbad : ∀ n, ∃ c : X → K,
      ∀ w : W, Valid w → support w ⊆ domain n → ¬Monochromatic c (support w) := by
    push Not at hfail
    exact hfail
  choose colors hcolors using hbad
  let U := Ultrafilter.of (atTop : Filter ℕ)
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  have hlimit : ∀ x : X, ∃ k : K, ∀ᶠ n in U, colors n x = k := by
    intro x
    apply Ultrafilter.eventually_exists_iff.mp
    exact Filter.Eventually.of_forall (fun n => ⟨colors n x, rfl⟩)
  choose color hcolor using hlimit
  obtain ⟨w, hw, hmono⟩ := hglobal color
  have hmatch : ∀ᶠ n in U, ∀ x : support w, colors n x.val = color x.val :=
    Filter.eventually_all.mpr (fun x => hcolor x.val)
  have hinside : ∀ᶠ n in U, ∀ x : support w, x.val ∈ domain n :=
    Filter.eventually_all.mpr (fun x => (hcover x.val).filter_mono hU)
  obtain ⟨n, hnmatch, hninside⟩ := (hmatch.and hinside).exists
  apply hcolors n w hw (fun x hx => hninside ⟨x, hx⟩)
  intro x hx y hy
  exact (hnmatch ⟨x, hx⟩).trans ((hmono x hx y hy).trans (hnmatch ⟨y, hy⟩).symm)

end RelationalRamsey632.Milliken
