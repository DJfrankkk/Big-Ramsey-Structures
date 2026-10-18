import CombinedRamsey.Negative.Ages

namespace CombinedRamsey.Negative

open RelationalRamsey632

variable {L : Language} {X : Type}

def WeaklyIndivisible (K : RelStructure L X) : Prop :=
  ∀ P : Set X, (¬ SameAgeOn K Set.univ K P) →
    ∃ f : RelEmbedding K K, ∀ x, f x ∉ P

/-- The induction on the number of colours in `neg:age-indivisibility` (1).
Earlier colour exclusions are preserved by composition of actual embeddings. -/
theorem ageIndivisible_of_weaklyIndivisible {K : RelStructure L X}
    (hw : WeaklyIndivisible K) : AgeIndivisibleOn K Set.univ := by
  intro r
  induction r with
  | zero =>
    intro χ
    refine ⟨0, ?_⟩
    have hset : Set.univ ∩ {x | χ x = 0} = Set.univ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_setOf_eq,
        iff_true]
      apply Fin.ext
      have h := (χ x).isLt
      omega
    rw [hset]
    exact sameAgeOn_refl K Set.univ
  | succ r ih =>
    intro χ
    by_cases h0 : SameAgeOn K Set.univ K {x | χ x = 0}
    · refine ⟨0, ?_⟩
      simpa only [Set.univ_inter] using h0
    · obtain ⟨f, hf⟩ := hw {x | χ x = 0} h0
      let ψ : X → Fin (r + 1) := fun x => (χ (f x)).pred (hf x)
      obtain ⟨i, hi⟩ := ih ψ
      refine ⟨i.succ, ?_⟩
      intro n a
      constructor
      · intro ha
        obtain ⟨e, he⟩ := (hi n a).mp ha
        refine ⟨f.comp e, ?_⟩
        intro x
        refine ⟨Set.mem_univ _, ?_⟩
        change χ (f (e x)) = i.succ
        have hp : (χ (f (e x))).pred (hf (e x)) = i := (he x).2
        have hs := congrArg Fin.succ hp
        exact (Fin.succ_pred _ _).symm.trans hs
      · exact inAgeOn_mono Set.inter_subset_left

end CombinedRamsey.Negative
