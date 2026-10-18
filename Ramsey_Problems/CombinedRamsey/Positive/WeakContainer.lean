import RelationalRamsey632.Coding.SeparatedClosure
import Mathlib.Tactic.Linarith

/-!
The closure-container argument used by the new uniform envelope construction.
It needs only the original-level trap and closure of the original slice library;
it does not impose the older, stronger no-original-proper-meets condition.

All hypotheses concern actual nodes and actual intrinsic closure operations.
The marker construction must discharge these hypotheses separately.
-/

namespace CombinedRamsey.Positive

open RelationalRamsey632.Source

variable {A : ℕ → Type} [∀ j, Zero (A j)]

def augmentedFamily (F : (i : ℕ) → Set (Node A i)) (N i : ℕ) : Set (Node A i) :=
  F i ∪ {Node.zero i N}

def weakContainer (F : (i : ℕ) → Set (Node A i)) (N : ℕ)
    (L : Finset ℕ) (i : ℕ) : Set (Node A i) :=
  {t | ∃ s ∈ augmentedFamily F N i, ∃ n ∈ L,
    ∃ h : n ≤ s.height, t = s.restrict n h}

theorem weakContainer_zero {F : (i : ℕ) → Set (Node A i)} {N : ℕ}
    {L : Finset ℕ} {i n : ℕ} (hn : n ∈ L) (hN : n ≤ N) :
    Node.zero (A := A) i n ∈ weakContainer F N L i :=
  ⟨Node.zero i N, Or.inr rfl, n, hn, hN, rfl⟩

theorem weakContainer_restriction {F : (i : ℕ) → Set (Node A i)} {N : ℕ}
    {L : Finset ℕ} {i n : ℕ} {s : Node A i}
    (hs : s ∈ augmentedFamily F N i) (hn : n ∈ L) (h : n ≤ s.height) :
    s.restrict n h ∈ weakContainer F N L i := ⟨s, hs, n, hn, h, rfl⟩

theorem weakContainer_closed {F : (i : ℕ) → Set (Node A i)} {N : ℕ}
    {L H : Finset ℕ} {O : Set ℕ}
    (hL : ∀ n ∈ L, n ≤ N)
    (htrap : ∀ n ∈ L, n ∈ O → n ∈ H)
    (hmeet : ∀ i (s t : Node A i), s ∈ augmentedFamily F N i →
      t ∈ augmentedFamily F N i → s.meetHeight t ∈ L)
    (hstep : ∀ i (s : Node A i), s ∈ F i → ∀ n ∈ H,
      ∀ h : n < s.height, s.slice n h ∈ F (i + 1))
    (hmarker : ∀ i (s : Node A i), s ∈ F i → ∀ n,
      ∀ h : n < s.height, n ∉ O → s.slice n h = Node.zero (i + 1) n) :
    Closed A (weakContainer F N L) (L : Set ℕ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro i t ⟨s, hs, n, hn, h, rfl⟩
    exact hn
  · rintro i s t ⟨u, hu, a, ha, hau, rfl⟩ ⟨w, hw, b, hb, hbw, rfl⟩
    rw [Node.meet_restrictions]
    exact weakContainer_restriction hu
      (RelationalRamsey632.Coding.min_mem ha
        (RelationalRamsey632.Coding.min_mem hb (hmeet i u w hu hw)))
      ((Nat.min_le_left _ _).trans hau)
  · rintro i t n ⟨s, hs, m, hm, hms, rfl⟩ hn hnt
    rw [Node.restrict_restrict]
    exact weakContainer_restriction hs hn (hnt.trans hms)
  · rintro i t n ⟨s, hs, m, hm, hms, rfl⟩ hn hnt
    rw [RelationalRamsey632.Coding.node_slice_restriction]
    rcases hs with hs | hs
    · by_cases hO : n ∈ O
      · have hf := hstep i s hs n (htrap n hn hO) (hnt.trans_le hms)
        have he : s.slice n (hnt.trans_le hms) =
            (s.slice n (hnt.trans_le hms)).restrict n le_rfl :=
          (Node.restrict_refl _).symm
        rw [he]
        exact weakContainer_restriction (Or.inl hf) hn le_rfl
      · rw [hmarker i s hs n (hnt.trans_le hms) hO]
        exact weakContainer_zero hn (hL n hn)
    · change s = Node.zero i N at hs
      subst s
      rw [Node.zero_slice]
      exact weakContainer_zero hn (hL n hn)

/-- The true intrinsic closure adds no constants; zeros only live in the container. -/
theorem intrinsic_levels_subset_weakContainer
    {X : Set (Node A 0)} {F : (i : ℕ) → Set (Node A i)} {N : ℕ}
    {L H : Finset ℕ} {O : Set ℕ}
    (hX : X ⊆ F 0) (hheight : ∀ s ∈ X, s.height ∈ L)
    (hL : ∀ n ∈ L, n ≤ N)
    (htrap : ∀ n ∈ L, n ∈ O → n ∈ H)
    (hmeet : ∀ i (s t : Node A i), s ∈ augmentedFamily F N i →
      t ∈ augmentedFamily F N i → s.meetHeight t ∈ L)
    (hstep : ∀ i (s : Node A i), s ∈ F i → ∀ n ∈ H,
      ∀ h : n < s.height, s.slice n h ∈ F (i + 1))
    (hmarker : ∀ i (s : Node A i), s ∈ F i → ∀ n,
      ∀ h : n < s.height, n ∉ O → s.slice n h = Node.zero (i + 1) n) :
    closureLevels A X ⊆ (L : Set ℕ) := by
  apply (generatedClosure_least A X (weakContainer F N L) (L : Set ℕ)
    (weakContainer_closed hL htrap hmeet hstep hmarker) ?_).2
  intro s hs
  have hr : s = s.restrict s.height le_rfl := (Node.restrict_refl s).symm
  rw [hr]
  exact weakContainer_restriction (Or.inl (hX hs)) (hheight s hs) le_rfl

def originalEnvelopeBound (k : ℕ) : ℕ := 2 * k + (k * 4 ^ k + 1) ^ 2

theorem originalEnvelopeBound_count {k P a : ℕ}
    (ha : a ≤ 2 * k) (hP : P ≤ k * 4 ^ k) :
    a + P ^ 2 + 2 * P ≤ originalEnvelopeBound k := by
  have hp := Nat.pow_le_pow_left hP 2
  unfold originalEnvelopeBound
  nlinarith

omit [∀ j, Zero (A j)] in
theorem weakContainer_level_card_bound
    {X : Set (Node A 0)} {L : Finset ℕ} {k : ℕ}
    (hsub : closureLevels A X ⊆ (L : Set ℕ))
    (hcard : L.card ≤ originalEnvelopeBound k) :
    Nat.card (closureLevels A X) ≤ originalEnvelopeBound k := by
  let f : closureLevels A X → L := fun n => ⟨n.val, hsub n.property⟩
  have hf : Function.Injective f := fun n m h =>
    Subtype.ext (congrArg (fun q : L => q.val) h)
  exact (Nat.card_le_card_of_injective f hf).trans (by
    simpa only [Nat.card_eq_finsetCard] using hcard)

end CombinedRamsey.Positive
