import CombinedRamsey.Negative.Ages
import Mathlib.Combinatorics.Colex

/-! The finite competing-realization-set argument in `neg:persistence`.
The predicates are actual induced relational ages, rather than abstract ranks. -/

namespace CombinedRamsey.Negative

open RelationalRamsey632

variable {L : Language} {X : Type}

/-- A finite union of subsets each missing an actual member of the age cannot
remove the whole age from an age-indivisible induced structure. -/
theorem age_survives_finite_exclusions {K : RelStructure L X} {P : Set X}
    (hP : AgeIndivisibleOn K P) {m : ℕ} (Q : Fin m → Set X)
    (hmissing : ∀ a, ∃ (n : ℕ) (d : RelStructure L (Fin n)),
      InAgeOn K P d ∧ ¬ InAgeOn K (Q a) d) :
    SameAgeOn K P K (P \ ⋃ a, Q a) := by
  classical
  let χ : X → Fin (m + 1) := fun x =>
    if hx : ∃ a, x ∈ Q a then (Classical.choose hx).succ else 0
  have hzero (x : X) : χ x = 0 ↔ ¬ ∃ a, x ∈ Q a := by
    dsimp only [χ]
    split_ifs with hx
    · simp only [Fin.succ_ne_zero, false_iff]
      exact not_not_intro hx
    · simp only [true_iff]
      exact hx
  have hsucc (a : Fin m) (x : X) : χ x = a.succ → x ∈ Q a := by
    dsimp only [χ]
    split_ifs with hx
    · intro heq
      have ha : Classical.choose hx = a := Fin.succ_injective _ heq
      exact ha ▸ Classical.choose_spec hx
    · intro heq
      exact False.elim ((Fin.succ_ne_zero a) heq.symm)
  obtain ⟨i, hi⟩ := hP m χ
  refine Fin.cases (fun h => ?_) (fun a h => ?_) i hi
  · have hset : P ∩ {x | χ x = 0} = P \ ⋃ a, Q a := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_sdiff,
        Set.mem_iUnion, hzero]
    exact hset ▸ h
  · obtain ⟨n, d, hd, hnot⟩ := hmissing a
    have ha : InAgeOn K (P ∩ {x | χ x = a.succ}) d := (h n d).mp hd
    exact False.elim (hnot (inAgeOn_mono (fun x hx => hsucc a x hx.2) ha))

/-- The conclusion can be transferred to the actual image of a realization
set under any full relational self-embedding. -/
theorem image_age_survives_finite_exclusions {K : RelStructure L X} {P : Set X}
    (hP : AgeIndivisibleOn K P) (f : RelEmbedding K K)
    {m : ℕ} (Q : Fin m → Set X)
    (hmissing : ∀ a, ∃ (n : ℕ) (d : RelStructure L (Fin n)),
      InAgeOn K P d ∧ ¬ InAgeOn K (Q a) d) :
    SameAgeOn K P K ((f '' P) \ ⋃ a, Q a) := by
  have hage := sameAgeOn_image f P
  have hY := ageIndivisible_of_sameAge hP hage
  apply sameAgeOn_trans hage
  apply age_survives_finite_exclusions hY Q
  intro a
  obtain ⟨n, d, hd, hn⟩ := hmissing a
  exact ⟨n, d, (hage n d).mp hd, hn⟩

/-- If every point outside finitely many competing realization sets has the
specified colour, that colour has the entire original induced age. -/
theorem persistent_age_of_finite_competitors {K : RelStructure L X} {P : Set X}
    (hP : AgeIndivisibleOn K P) (f : RelEmbedding K K)
    {C : Type} (χ : X → C) (i : C) {m : ℕ} (Q : Fin m → Set X)
    (hmissing : ∀ a, ∃ (n : ℕ) (d : RelStructure L (Fin n)),
      InAgeOn K P d ∧ ¬ InAgeOn K (Q a) d)
    (hcolour : ∀ x ∈ f '' P, (¬ ∃ a, x ∈ Q a) → χ x = i) :
    SameAgeOn K P K ((f '' P) ∩ {x | χ x = i}) := by
  have hres := image_age_survives_finite_exclusions hP f Q hmissing
  intro n d
  constructor
  · intro hd
    apply inAgeOn_mono _ ((hres n d).mp hd)
    intro x hx
    exact ⟨hx.1, hcolour x hx.1 (by simpa only [Set.mem_iUnion] using hx.2)⟩
  · intro hd
    exact ((sameAgeOn_image f P) n d).mpr (inAgeOn_mono Set.inter_subset_left hd)

/-- Binary boundary weights are genuinely injective. -/
theorem binaryWeight_injective : Function.Injective
    (fun s : Finset ℕ => ∑ x ∈ s, 2 ^ x) := by
  exact Finset.geomSum_injective (by omega)

/-- There are only finitely many boundary sets with bounded binary weight. -/
theorem finite_boundaries_below (w : ℕ) :
    {s : Finset ℕ | (∑ x ∈ s, 2 ^ x) < w}.Finite := by
  exact (Set.finite_Iio w).preimage binaryWeight_injective.injOn

end CombinedRamsey.Negative
