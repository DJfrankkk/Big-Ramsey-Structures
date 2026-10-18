import CombinedRamsey.Positive.UniformClosureBound
import RelationalRamsey632.Source.SeparatedNormalFormBound

/-! Exact new R(k) normal-form upper bound, for arbitrary finite unary labels. -/

namespace CombinedRamsey.Positive.Marker

open RelationalRamsey632.Source
open scoped BigOperators

variable (colours : ℕ → ℕ) (c : ∀ v, GenuineColours colours v)

noncomputable def labelledMap {U : Type} (labels : ℕ → U) (v : ℕ) : U × Node (Alphabet colours) 0 :=
  (labels v, family colours c v)

theorem closureLevels_empty (A : ℕ → Type) : closureLevels A ∅ = ∅ := by
  have hc : Closed A (fun _ => ∅) ∅ := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> contradiction
  exact Set.Subset.antisymm
    (generatedClosure_least A ∅ (fun _ => ∅) ∅ hc (Set.Subset.refl _)).2
    (Set.empty_subset _)

theorem labelled_tuple_bound {U : Type} (labels : ℕ → U) (n : ℕ) (t : Fin n ↪ ℕ) :
    (tupleLevels (labelledMap colours c labels ∘ t)).card ≤
      CombinedRamsey.Positive.originalEnvelopeBound n := by
  classical
  let S := Finset.univ.image t
  have hcard : S.card = n := by
    rw [Finset.card_image_of_injective _ t.injective]
    exact Finset.card_fin n
  have himage : tupleProjections (labelledMap colours c labels ∘ t) =
      (imageSet colours c S : Set (Node (Alphabet colours) 0)) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact Finset.mem_image.mpr ⟨t j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, rfl⟩
    · intro hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨j, rfl⟩
  by_cases hne : S.Nonempty
  · have hbound := uniform_closure_level_bound colours c S hne
    rw [← himage, ← tupleLevels_coe, Nat.card_coe_set_eq, Set.ncard_coe_finset, hcard] at hbound
    exact hbound
  · have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have himpty : tupleProjections (labelledMap colours c labels ∘ t) = ∅ := by
      rw [himage, hS]
      simp only [imageSet, Finset.image_empty, Finset.coe_empty]
    have hlevels : tupleLevels (labelledMap colours c labels ∘ t) = ∅ := by
      apply Finset.coe_injective
      rw [tupleLevels_coe, himpty, closureLevels_empty, Finset.coe_empty]
    rw [hlevels]
    exact Nat.zero_le _

theorem uniform_normalFormImage_bound {U : Type} [Finite U] (labels : ℕ → U) (n : ℕ) :
    (normalFormImage (labelledMap colours c labels) n).Finite ∧
      Nat.card (normalFormImage (labelledMap colours c labels) n) ≤
        (Nat.card U * ∑ h : Fin (CombinedRamsey.Positive.originalEnvelopeBound n),
          ∏ r ∈ Finset.Icc 1 h.val, (colours r + 2) ^ h.val.choose r) ^ n := by
  have h := normalFormImage_bound (labelledMap colours c labels) n
    (CombinedRamsey.Positive.originalEnvelopeBound n) (labelled_tuple_bound colours c labels n)
  simpa only [Alphabet, Fintype.card_fin] using h

end CombinedRamsey.Positive.Marker
