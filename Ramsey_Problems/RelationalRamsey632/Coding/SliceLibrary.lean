import RelationalRamsey632.Source.Closure
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite

/-! Actual finite libraries of slices at original generator heights. -/

namespace RelationalRamsey632.Coding

open Source

theorem lastCases_injective {T : Type} {n : ℕ} (a : T) (f : Fin n → T)
    (hf : Function.Injective f) (hne : ∀ i, f i ≠ a) :
    Function.Injective (Fin.lastCases a f) := by
  intro i
  revert i
  refine Fin.lastCases ?_ (fun i => ?_)
  · intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · intro _
      rfl
    · intro h
      exact False.elim (hne j (by simpa using h.symm))
  · intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · intro h
      exact False.elim (hne i (by simpa using h))
    · intro h
      exact congrArg Fin.castSucc (hf (by simpa using h))

def evaluateSlices {A : ℕ → Type} (s : Node A 0) :
    (i : ℕ) → (Fin i → ℕ) → Option (Node A i)
  | 0, _ => some s
  | i + 1, coords =>
    match evaluateSlices s i (fun j => coords j.castSucc) with
    | none => none
    | some t => if hn : coords (Fin.last i) < t.height then
        some (t.slice (coords (Fin.last i)) hn) else none

theorem evaluateSlices_invariant {A : ℕ → Type} (s : Node A 0) (i : ℕ)
    (coords : Fin i → ℕ) (t : Node A i) (h : evaluateSlices s i coords = some t) :
    t.height ≤ s.height ∧ (∀ j, t.height ≤ coords j) ∧
      (∀ j, coords j < s.height) ∧ Function.Injective coords := by
  induction i with
  | zero =>
    have he : s = t := by simpa [evaluateSlices] using h
    subst t
    exact ⟨le_rfl, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0⟩
  | succ i ih =>
    cases hp : evaluateSlices s i (fun j => coords j.castSucc) with
    | none => simp [evaluateSlices, hp] at h
    | some u =>
      by_cases hn : coords (Fin.last i) < u.height
      · have ht : u.slice (coords (Fin.last i)) hn = t := by
          simpa [evaluateSlices, hp, hn] using h
        subst t
        obtain ⟨hheight, habove, hbelow, hinj⟩ := ih _ u hp
        have hc : coords = Fin.lastCases (coords (Fin.last i)) (fun j => coords j.castSucc) := by
          funext j
          refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
        refine ⟨hn.le.trans hheight, ?_, ?_, ?_⟩
        · intro j
          refine Fin.lastCases ?_ (fun j => ?_) j
          · exact le_rfl
          · exact hn.le.trans (habove j)
        · intro j
          refine Fin.lastCases ?_ (fun j => ?_) j
          · exact hn.trans_le hheight
          · exact hbelow j
        · rw [hc]
          exact lastCases_injective _ _ hinj (fun j => (hn.trans_le (habove j)).ne')
      · simp [evaluateSlices, hp, hn] at h

variable (A : ℕ → Type) (X : Set (Node A 0)) (H : Finset ℕ)

def sliceLibrary (i : ℕ) : Set (Node A i) :=
  {t | ∃ s ∈ X, ∃ coords : Fin i → ℕ,
    (∀ j, coords j ∈ H) ∧ evaluateSlices s i coords = some t}

theorem sliceLibrary_generator {s : Node A 0} (hs : s ∈ X) : s ∈ sliceLibrary A X H 0 :=
  ⟨s, hs, Fin.elim0, fun j => j.elim0, rfl⟩

theorem sliceLibrary_height {i : ℕ} {t : Node A i}
    (hX : ∀ s ∈ X, s.height ∈ H) (ht : t ∈ sliceLibrary A X H i) : t.height ∈ H := by
  obtain ⟨s, hs, coords, hcoords, he⟩ := ht
  cases i with
  | zero =>
    have ht : s = t := by simpa [evaluateSlices] using he
    exact ht ▸ hX s hs
  | succ i =>
    cases hp : evaluateSlices s i (fun j => coords j.castSucc) with
    | none => simp [evaluateSlices, hp] at he
    | some u =>
      by_cases hn : coords (Fin.last i) < u.height
      · have ht : u.slice (coords (Fin.last i)) hn = t := by
          simpa [evaluateSlices, hp, hn] using he
        exact congrArg Node.height ht ▸ hcoords (Fin.last i)
      · simp [evaluateSlices, hp, hn] at he

theorem sliceLibrary_step {i : ℕ} {t : Node A i} (ht : t ∈ sliceLibrary A X H i)
    (n : ℕ) (hnH : n ∈ H) (hn : n < t.height) : t.slice n hn ∈ sliceLibrary A X H (i + 1) := by
  obtain ⟨s, hs, coords, hcoords, he⟩ := ht
  refine ⟨s, hs, Fin.lastCases n coords, ?_, ?_⟩
  · intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using hnH
    · simpa using hcoords j
  · simp [evaluateSlices, he, hn]

theorem sliceLibrary_depth_bound {i : ℕ} {t : Node A i}
    (hX : ∀ s ∈ X, s.height ∈ H) (ht : t ∈ sliceLibrary A X H i) : i + 1 ≤ H.card := by
  classical
  obtain ⟨s, hs, coords, hcoords, he⟩ := ht
  obtain ⟨_, _, hbelow, hinj⟩ := evaluateSlices_invariant s i coords t he
  let f : Fin (i + 1) → ℕ := Fin.lastCases s.height coords
  have hf : Function.Injective f := lastCases_injective _ _ hinj (fun j => (hbelow j).ne)
  let g : Fin (i + 1) → H := fun j =>
    ⟨f j, by
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa [f] using hX s hs
      · simpa [f] using hcoords j⟩
  have hg : Function.Injective g := fun a b hab => hf (congrArg Subtype.val hab)
  simpa using Fintype.card_le_of_injective g hg

theorem sliceLibrary_high_empty (hX : ∀ s ∈ X, s.height ∈ H) {i : ℕ} (hi : H.card ≤ i) :
    sliceLibrary A X H i = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have hd := sliceLibrary_depth_bound A X H hX ht
  omega

theorem sliceLibrary_finite_card (hX : X.Finite) (i : ℕ) :
    (sliceLibrary A X H i).Finite ∧
      Nat.card (sliceLibrary A X H i) ≤ Nat.card X * H.card ^ i := by
  classical
  let Code := X × (Fin i → H)
  haveI : Finite X := hX.to_subtype
  haveI : Finite Code := inferInstance
  have hcode : ∀ t : sliceLibrary A X H i, ∃ q : Code,
      evaluateSlices q.1.val i (fun j => (q.2 j).val) = some t.val := by
    intro t
    obtain ⟨s, hs, coords, hcoords, he⟩ := t.property
    exact ⟨(⟨s, hs⟩, fun j => ⟨coords j, hcoords j⟩), he⟩
  choose code hcode using hcode
  have hinj : Function.Injective code := by
    intro t u h
    apply Subtype.ext
    have he := (hcode t).symm.trans
      ((congrArg (fun q : Code => evaluateSlices q.1.val i (fun j => (q.2 j).val)) h).trans (hcode u))
    exact Option.some.inj he
  haveI : Finite (sliceLibrary A X H i) := Finite.of_injective code hinj
  refine ⟨Set.toFinite _, ?_⟩
  have hn := Nat.card_le_card_of_injective code hinj
  simpa [Code, Nat.card_prod, Nat.card_fun, Nat.card_eq_finsetCard] using hn

theorem sliceLibrary_card_power (hX : X.Finite) (hH : H.card ≤ Nat.card X) (i : ℕ) :
    Nat.card (sliceLibrary A X H i) ≤ Nat.card X ^ (i + 1) := by
  apply (sliceLibrary_finite_card A X H hX i).2.trans
  calc
    Nat.card X * H.card ^ i ≤ Nat.card X * Nat.card X ^ i :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hH _)
    _ = Nat.card X ^ (i + 1) := by rw [pow_succ, Nat.mul_comm]

noncomputable def generatorHeights (hX : X.Finite) : Finset ℕ :=
  hX.toFinset.image Node.height

theorem generatorHeights_contains (hX : X.Finite) {s : Node A 0} (hs : s ∈ X) :
    s.height ∈ generatorHeights A X hX :=
  Finset.mem_image.mpr ⟨s, hX.mem_toFinset.mpr hs, rfl⟩

theorem generatorHeights_card (hX : X.Finite) :
    (generatorHeights A X hX).card ≤ Nat.card X := by
  classical
  rw [Nat.card_eq_card_finite_toFinset hX]
  exact Finset.card_image_le

end RelationalRamsey632.Coding
