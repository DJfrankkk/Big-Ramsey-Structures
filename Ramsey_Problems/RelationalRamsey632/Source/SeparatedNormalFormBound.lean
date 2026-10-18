import RelationalRamsey632.Coding.NodeCounting
import Mathlib.Algebra.BigOperators.Fin

namespace RelationalRamsey632.Source

open scoped BigOperators

def normalFormImage {A : ℕ → Type} {U : Type} (φ : ℕ → U × Node A 0) (n : ℕ) :
    Set (Fin n → U × Node A 0) := Set.range (fun t : Fin n ↪ ℕ => normalForm (φ ∘ t))

theorem separated_tuple_levels_bound {A : ℕ → Type} [∀ j, Zero (A j)]
    {U : Type} {R : Set (Node A 0)} {O : Set ℕ}
    (hsep : Coding.SeparatedAtAllDepths R O) (φ : ℕ → U × Node A 0)
    (hproj : Function.Injective (fun v => (φ v).2))
    (hR : ∀ v, (φ v).2 ∈ R) (n : ℕ) (t : Fin n ↪ ℕ) :
    (tupleLevels (φ ∘ t)).card ≤ Coding.levelBound n := by
  have hsub : tupleProjections (φ ∘ t) ⊆ R := by
    rintro x ⟨j, rfl⟩
    exact hR (t j)
  have hcard : Nat.card (tupleProjections (φ ∘ t)) = n := by
    change Nat.card (Set.range ((fun v => (φ v).2) ∘ t)) = n
    rw [Nat.card_range_of_injective (hproj.comp t.injective), Nat.card_fin]
  have hb := Coding.separated_closure_level_bound hsep hsub (tupleProjections_finite (φ ∘ t))
  rw [hcard, ← tupleLevels_coe] at hb
  simpa only [Nat.card_coe_set_eq, Set.ncard_coe_finset] using hb

theorem normalFormImage_bound {A : ℕ → Type} [∀ j, Fintype (A j)]
    {U : Type} [Finite U] (φ : ℕ → U × Node A 0) (n B : ℕ)
    (hB : ∀ t : Fin n ↪ ℕ, (tupleLevels (φ ∘ t)).card ≤ B) :
    (normalFormImage φ n).Finite ∧ Nat.card (normalFormImage φ n) ≤
      (Nat.card U * ∑ h : Fin B, ∏ r ∈ Finset.Icc 1 h.val,
        Fintype.card (A r) ^ h.val.choose r) ^ n := by
  classical
  letI := Fintype.ofFinite U
  have hheight : ∀ τ ∈ normalFormImage φ n, ∀ j, (τ j).2.height < B := by
    rintro τ ⟨t, rfl⟩ j
    exact (normalForm_height_bound (φ ∘ t) j).trans_le (hB t)
  have hfin : (normalFormImage φ n).Finite := by
    apply (finite_bounded_tuples A U n B).subset
    intro τ hτ
    exact ⟨fun j => ((τ j).1, ⟨(τ j).2, hheight τ hτ j⟩), rfl⟩
  let f : normalFormImage φ n → (Fin n → U × BoundedNodes A B) :=
    fun τ j => ((τ.val j).1, ⟨(τ.val j).2, hheight τ.val τ.property j⟩)
  have hf : Function.Injective f := by
    intro τ σ h
    apply Subtype.ext
    funext j
    exact congrArg (fun z : U × BoundedNodes A B => (z.1, z.2.val)) (congrFun h j)
  letI := boundedNodes_finite A B
  letI := Fintype.ofFinite (BoundedNodes A B)
  have hcard : Nat.card (Fin n → U × BoundedNodes A B) =
      (Nat.card U * ∑ h : Fin B, ∏ r ∈ Finset.Icc 1 h.val,
        Fintype.card (A r) ^ h.val.choose r) ^ n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_prod,
      ← Nat.card_eq_fintype_card (α := U),
      ← Nat.card_eq_fintype_card (α := BoundedNodes A B), boundedNodes_card]
  exact ⟨hfin, (Nat.card_le_card_of_injective f hf).trans_eq hcard⟩

theorem every_permitted_coding_bound {A : ℕ → Type} [∀ j, Fintype (A j)] [∀ j, Zero (A j)]
    {U : Type} [Finite U] {R : Set (Node A 0)} {O : Set ℕ}
    (hsep : Coding.SeparatedAtAllDepths R O) (φ : ℕ → U × Node A 0)
    (hproj : Function.Injective (fun v => (φ v).2)) (hR : ∀ v, (φ v).2 ∈ R) (n : ℕ) :
    (normalFormImage φ n).Finite ∧ Nat.card (normalFormImage φ n) ≤
      (Nat.card U * ∑ h : Fin (Coding.levelBound n), ∏ r ∈ Finset.Icc 1 h.val,
        Fintype.card (A r) ^ h.val.choose r) ^ n :=
  normalFormImage_bound φ n (Coding.levelBound n) (separated_tuple_levels_bound hsep φ hproj hR n)

theorem levelBound_monotone : Monotone Coding.levelBound := by
  intro m n hmn
  unfold Coding.levelBound
  apply Nat.add_le_add hmn
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (m ^ (i + 1) + 1).choose 2),
    Fin.sum_univ_eq_sum_range (fun i : ℕ => (n ^ (i + 1) + 1).choose 2)]
  calc
    (∑ i ∈ Finset.range m, (m ^ (i + 1) + 1).choose 2) ≤
        ∑ i ∈ Finset.range m, (n ^ (i + 1) + 1).choose 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.choose_le_choose 2 (Nat.add_le_add_right (Nat.pow_le_pow_left hmn _) 1)
    _ ≤ ∑ i ∈ Finset.range n, (n ^ (i + 1) + 1).choose 2 :=
      Finset.sum_le_sum_of_subset (Finset.range_mono hmn)

theorem separated_labelled_tuple_bound {A : ℕ → Type} [∀ j, Zero (A j)]
    {U : Type} {R : Set (Node A 0)} {O : Set ℕ}
    (hsep : Coding.SeparatedAtAllDepths R O) {n : ℕ}
    (v : Fin n → U × Node A 0) (hR : tupleProjections v ⊆ R) :
    (tupleLevels v).card ≤ Coding.levelBound n := by
  have hX : Nat.card (tupleProjections v) ≤ n := by
    let f : Fin n → tupleProjections v := fun j => ⟨(v j).2, ⟨j, rfl⟩⟩
    have hf : Function.Surjective f := by
      rintro ⟨x, j, hj⟩
      exact ⟨j, Subtype.ext hj⟩
    have hh := Nat.card_le_card_of_surjective f hf
    simpa only [Nat.card_fin] using hh
  have hb := Coding.separated_closure_level_bound hsep hR (tupleProjections_finite v)
  rw [← tupleLevels_coe, Nat.card_coe_set_eq, Set.ncard_coe_finset] at hb
  exact hb.trans (levelBound_monotone hX)

def labelledNormalForms {A : ℕ → Type} {U : Type} (R : Set (Node A 0)) (n : ℕ) :
    Set (Fin n → U × Node A 0) :=
  {τ | ∃ v : Fin n → U × Node A 0, tupleProjections v ⊆ R ∧ normalForm v = τ}

theorem separated_labelled_normal_forms {A : ℕ → Type}
    [∀ j, Fintype (A j)] [∀ j, Zero (A j)] {U : Type} [Finite U]
    {R : Set (Node A 0)} {O : Set ℕ} (hsep : Coding.SeparatedAtAllDepths R O) (n : ℕ) :
    (labelledNormalForms (U := U) R n).Finite ∧
      Nat.card (labelledNormalForms (U := U) R n) ≤
        (Nat.card U * ∑ h : Fin (Coding.levelBound n), ∏ r ∈ Finset.Icc 1 h.val,
          Fintype.card (A r) ^ h.val.choose r) ^ n := by
  classical
  let B := Coding.levelBound n
  letI := Fintype.ofFinite U
  have hheight : ∀ τ ∈ labelledNormalForms (U := U) R n, ∀ j, (τ j).2.height < B := by
    rintro τ ⟨v, hv, rfl⟩ j
    exact (normalForm_height_bound v j).trans_le (separated_labelled_tuple_bound hsep v hv)
  have hfin : (labelledNormalForms (U := U) R n).Finite := by
    apply (finite_bounded_tuples A U n B).subset
    intro τ hτ
    exact ⟨fun j => ((τ j).1, ⟨(τ j).2, hheight τ hτ j⟩), rfl⟩
  let f : labelledNormalForms (U := U) R n → (Fin n → U × BoundedNodes A B) :=
    fun τ j => ((τ.val j).1, ⟨(τ.val j).2, hheight τ.val τ.property j⟩)
  have hf : Function.Injective f := by
    intro τ σ h
    apply Subtype.ext
    funext j
    exact congrArg (fun z : U × BoundedNodes A B => (z.1, z.2.val)) (congrFun h j)
  letI := boundedNodes_finite A B
  letI := Fintype.ofFinite (BoundedNodes A B)
  have hcard : Nat.card (Fin n → U × BoundedNodes A B) =
      (Nat.card U * ∑ h : Fin B, ∏ r ∈ Finset.Icc 1 h.val,
        Fintype.card (A r) ^ h.val.choose r) ^ n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_prod,
      ← Nat.card_eq_fintype_card (α := U),
      ← Nat.card_eq_fintype_card (α := BoundedNodes A B), boundedNodes_card]
  exact ⟨hfin, (Nat.card_le_card_of_injective f hf).trans_eq hcard⟩

end RelationalRamsey632.Source
