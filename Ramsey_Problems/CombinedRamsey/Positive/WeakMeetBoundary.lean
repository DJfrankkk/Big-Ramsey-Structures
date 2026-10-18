import RelationalRamsey632.Coding.ZeroNodes

/-!
A literal boundary audit of Lemma 4.1 (weak-meets) in the combined paper.

Take every n_r = 0. Then sigma_j = 2, every genuine colour is zero,
every cutoff D is zero, there are no markers, and o_v = v. The actual
coding prescribed by the paper is the zero node at height v. Comparing
one such original 0-slice to a longer zero node gives an original meet
height, contrary to the unrestricted zero-comparator clause.

The subsequent envelope argument uses that clause only for incomparable
comparators. This file refutes the printed clause, not that corrected
incomparable version and not the envelope theorem.
-/

namespace CombinedRamsey.Positive

open RelationalRamsey632.Source

abbrev EmptyAlphabet (_ : ℕ) := Fin 2

def emptyHypergraphCoding (v : ℕ) : Node EmptyAlphabet 0 := Node.zero 0 v

@[simp] theorem emptyHypergraphCoding_height (v : ℕ) :
    (emptyHypergraphCoding v).height = v := rfl

theorem emptyHypergraphCoding_injective : Function.Injective emptyHypergraphCoding := by
  intro u v h
  exact congrArg Node.height h

theorem emptyHypergraph_original_zero_comparison :
    Node.meetHeight (emptyHypergraphCoding 1) (Node.zero (A := EmptyAlphabet) 0 2) = 1 := by
  have h := congrArg Node.height (Node.zero_meet (A := EmptyAlphabet) 0 1 2)
  exact h

/-- The original zero-slice is comparable to the zero comparator. -/
theorem emptyHypergraph_original_comparable :
    Node.Prefix (emptyHypergraphCoding 1) (Node.zero (A := EmptyAlphabet) 0 2) :=
  ⟨by decide, rfl⟩

/-- The zero-comparator sentence is false when it omits incomparability. -/
theorem literal_weak_meets_zero_clause_false :
    ¬ (∀ v N n : ℕ,
      Node.meetHeight (emptyHypergraphCoding v) (Node.zero (A := EmptyAlphabet) 0 N) = n →
      n < 0) := by
  intro h
  exact Nat.not_lt_zero 1 (h 1 2 1 emptyHypergraph_original_zero_comparison)

/-- Precisely why a comparable case must be handled separately. -/
theorem original_zero_meet_on_shorter_height (v N : ℕ) (h : v ≤ N) :
    Node.meetHeight (emptyHypergraphCoding v) (Node.zero (A := EmptyAlphabet) 0 N) = v := by
  have e := congrArg Node.height (Node.zero_meet (A := EmptyAlphabet) 0 v N)
  simpa only [emptyHypergraphCoding, Node.height_meet, Node.zero_height,
    Nat.min_eq_left h] using e

end CombinedRamsey.Positive
