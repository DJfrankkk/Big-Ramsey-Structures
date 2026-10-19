import Mathlib.Data.Finset.Union
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-!
The generated closure in Definition 2.1 of the supplied paper.

Matrices are lists of strict rows, with a separate `Triangular` predicate.
This makes finite examples transparent to the kernel. No paper theorem is
introduced as an axiom. In particular, compression and the Ramsey theorem
are not assumed here.
-/

namespace RamseyCommon

abbrev Word := List Bool
abbrev Matrix := List Word

def Triangular (M : Matrix) : Prop :=
  ∀ i : Fin M.length, (M[i.val]).length = i.val

def commonPrefix {α : Type} [DecidableEq α] : List α → List α → List α
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs => if a = b then a :: commonPrefix as bs else []

theorem commonPrefix_length_le_left {α : Type} [DecidableEq α]
    (u v : List α) : (commonPrefix u v).length ≤ u.length := by
  induction u generalizing v with
  | nil => simp [commonPrefix]
  | cons a as ih =>
    cases v with
    | nil => simp [commonPrefix]
    | cons b bs =>
      simp only [commonPrefix]
      split <;> simp_all

theorem commonPrefix_length_le_right {α : Type} [DecidableEq α]
    (u v : List α) : (commonPrefix u v).length ≤ v.length := by
  induction u generalizing v with
  | nil => simp [commonPrefix]
  | cons a as ih =>
    cases v with
    | nil => simp [commonPrefix]
    | cons b bs =>
      simp only [commonPrefix]
      split <;> simp_all

theorem commonPrefix_eq_take_left {α : Type} [DecidableEq α]
    (u v : List α) : commonPrefix u v = u.take (commonPrefix u v).length := by
  induction u generalizing v with
  | nil => simp [commonPrefix]
  | cons a as ih =>
    cases v with
    | nil => simp [commonPrefix]
    | cons b bs =>
      simp only [commonPrefix]
      split
      · simp only [List.length_cons, List.take_succ_cons]
        exact congrArg (List.cons a) (ih bs)
      · simp

theorem commonPrefix_comm {α : Type} [DecidableEq α] (u v : List α) :
    commonPrefix u v = commonPrefix v u := by
  induction u generalizing v with
  | nil => cases v <;> rfl
  | cons a as ih =>
    cases v with
    | nil => rfl
    | cons b bs =>
      by_cases h : a = b
      · subst b; simp [commonPrefix, ih]
      · simp [commonPrefix, h, Ne.symm h]

theorem commonPrefix_self {α : Type} [DecidableEq α] (u : List α) :
    commonPrefix u u = u := by
  induction u with
  | nil => rfl
  | cons a as ih => simp [commonPrefix, ih]

theorem commonPrefix_eq_take_right {α : Type} [DecidableEq α]
    (u v : List α) : commonPrefix u v = v.take (commonPrefix u v).length := by
  rw [commonPrefix_comm u v]
  exact commonPrefix_eq_take_left v u

def row (M : Matrix) (d : Nat) : Word := M.getD d []

inductive Node where
  | matrix : Matrix → Node
  | word : Word → Node
  | level : Nat → Node
  deriving DecidableEq, Repr

/-- Only the generators are inserted; in particular there is no root constant. -/
inductive Retained (X : Set Matrix) : Node → Prop where
  | original {M : Matrix} : M ∈ X → Retained X (.matrix M)
  | matrixMeet {M N : Matrix} : Retained X (.matrix M) →
      Retained X (.matrix N) → Retained X (.matrix (commonPrefix M N))
  | wordMeet {u v : Word} : Retained X (.word u) →
      Retained X (.word v) → Retained X (.word (commonPrefix u v))
  | matrixHeight {M : Matrix} : Retained X (.matrix M) →
      Retained X (.level M.length)
  | wordHeight {u : Word} : Retained X (.word u) →
      Retained X (.level u.length)
  | matrixRestrict {M : Matrix} {d : Nat} : Retained X (.matrix M) →
      Retained X (.level d) → d ≤ M.length → Retained X (.matrix (M.take d))
  | wordRestrict {u : Word} {d : Nat} : Retained X (.word u) →
      Retained X (.level d) → d ≤ u.length → Retained X (.word (u.take d))
  | strictRow {M : Matrix} {d : Nat} : Retained X (.matrix M) →
      Retained X (.level d) → d < M.length → Retained X (.word (row M d))

def Closed (C : Set Node) : Prop :=
  (∀ M N, Node.matrix M ∈ C → Node.matrix N ∈ C →
      Node.matrix (commonPrefix M N) ∈ C) ∧
  (∀ u v, Node.word u ∈ C → Node.word v ∈ C →
      Node.word (commonPrefix u v) ∈ C) ∧
  (∀ M, Node.matrix M ∈ C → Node.level M.length ∈ C) ∧
  (∀ u, Node.word u ∈ C → Node.level u.length ∈ C) ∧
  (∀ M d, Node.matrix M ∈ C → Node.level d ∈ C → d ≤ M.length →
      Node.matrix (M.take d) ∈ C) ∧
  (∀ u d, Node.word u ∈ C → Node.level d ∈ C → d ≤ u.length →
      Node.word (u.take d) ∈ C) ∧
  (∀ M d, Node.matrix M ∈ C → Node.level d ∈ C → d < M.length →
      Node.word (row M d) ∈ C)

theorem retained_closed (X : Set Matrix) : Closed {z | Retained X z} := by
  exact ⟨fun _ _ => Retained.matrixMeet, fun _ _ => Retained.wordMeet,
    fun _ => Retained.matrixHeight, fun _ => Retained.wordHeight,
    fun _ _ => Retained.matrixRestrict, fun _ _ => Retained.wordRestrict,
    fun _ _ => Retained.strictRow⟩

theorem retained_least {X : Set Matrix} {C : Set Node} (hC : Closed C)
    (hX : ∀ M ∈ X, Node.matrix M ∈ C) {z : Node} (hz : Retained X z) : z ∈ C := by
  induction hz with
  | original h => exact hX _ h
  | matrixMeet _ _ ih₁ ih₂ => exact hC.1 _ _ ih₁ ih₂
  | wordMeet _ _ ih₁ ih₂ => exact hC.2.1 _ _ ih₁ ih₂
  | matrixHeight _ ih => exact hC.2.2.1 _ ih
  | wordHeight _ ih => exact hC.2.2.2.1 _ ih
  | matrixRestrict _ _ hd ih₁ ih₂ => exact hC.2.2.2.2.1 _ _ ih₁ ih₂ hd
  | wordRestrict _ _ hd ih₁ ih₂ => exact hC.2.2.2.2.2.1 _ _ ih₁ ih₂ hd
  | strictRow _ _ hd ih₁ ih₂ => exact hC.2.2.2.2.2.2 _ _ ih₁ ih₂ hd

theorem retained_mono {X Y : Set Matrix} (hXY : X ⊆ Y) {z : Node}
    (hz : Retained X z) : Retained Y z :=
  retained_least (retained_closed Y) (fun _ h => Retained.original (hXY h)) hz

theorem retained_empty (z : Node) : ¬ Retained ∅ z := by
  intro hz
  have : z ∈ (∅ : Set Node) := retained_least (by simp [Closed]) (by simp) hz
  exact this

theorem commonPrefix_isPrefix_left {α : Type} [DecidableEq α] (u v : List α) :
    commonPrefix u v <+: u := by
  rw [List.prefix_iff_eq_take]
  exact commonPrefix_eq_take_left u v

theorem row_eq_of_prefix {A M : Matrix} (h : A <+: M) {d : Nat}
    (hd : d < A.length) : row A d = row M d := by
  obtain ⟨tail, rfl⟩ := h
  simp [row, List.getD_eq_getElem?_getD, List.getElem?_append_left hd]

/-- Every matrix is a prefix of a generator, every word is a prefix of an
original strict row, and every level is bounded by an original node height.
This invariant also works for arbitrary lists of rows. -/
def SourceBound (X : Set Matrix) : Node → Prop
  | .matrix A => ∃ M ∈ X, A <+: M
  | .word u => ∃ M ∈ X, ∃ d < M.length, u <+: row M d
  | .level a => ∃ M ∈ X, a ≤ M.length ∨ ∃ d < M.length, a ≤ (row M d).length

theorem retained_sourceBound {X : Set Matrix} {z : Node} (hz : Retained X z) :
    SourceBound X z := by
  induction hz with
  | original h => exact ⟨_, h, List.prefix_refl _⟩
  | matrixMeet _ _ ih₁ _ =>
    obtain ⟨M, hM, hp⟩ := ih₁
    exact ⟨M, hM, (commonPrefix_isPrefix_left _ _).trans hp⟩
  | wordMeet _ _ ih₁ _ =>
    obtain ⟨M, hM, d, hd, hp⟩ := ih₁
    exact ⟨M, hM, d, hd, (commonPrefix_isPrefix_left _ _).trans hp⟩
  | matrixHeight _ ih =>
    obtain ⟨M, hM, hp⟩ := ih
    exact ⟨M, hM, Or.inl hp.length_le⟩
  | wordHeight _ ih =>
    obtain ⟨M, hM, d, hd, hp⟩ := ih
    exact ⟨M, hM, Or.inr ⟨d, hd, hp.length_le⟩⟩
  | matrixRestrict _ _ _ ih₁ _ =>
    obtain ⟨M, hM, hp⟩ := ih₁
    exact ⟨M, hM, (List.take_prefix _ _).trans hp⟩
  | wordRestrict _ _ _ ih₁ _ =>
    obtain ⟨M, hM, d, hd, hp⟩ := ih₁
    exact ⟨M, hM, d, hd, (List.take_prefix _ _).trans hp⟩
  | @strictRow A d _ _ hd ih₁ _ =>
    obtain ⟨M, hM, hp⟩ := ih₁
    exact ⟨M, hM, d, lt_of_lt_of_le hd hp.length_le,
      by rw [row_eq_of_prefix hp hd]⟩

theorem triangular_of_prefix {A M : Matrix} (h : A <+: M) (hM : Triangular M) :
    Triangular A := by
  intro i
  rw [h.getElem i.isLt]
  exact hM ⟨i.val, lt_of_lt_of_le i.isLt h.length_le⟩

theorem retained_matrix_triangular {X : Set Matrix}
    (htri : ∀ M ∈ X, Triangular M) {A : Matrix}
    (hA : Retained X (.matrix A)) : Triangular A := by
  obtain ⟨M, hM, hp⟩ := retained_sourceBound hA
  exact triangular_of_prefix hp (htri M hM)

/-- A finite, explicitly enumerable set of all prefixes of a list. -/
def prefixes {α : Type} [DecidableEq α] (u : List α) : Finset (List α) :=
  (Finset.range (u.length + 1)).image u.take

theorem mem_prefixes_iff {α : Type} [DecidableEq α] (u v : List α) :
    u ∈ prefixes v ↔ u <+: v := by
  constructor
  · intro h
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp h
    exact List.take_prefix d v
  · intro h
    exact Finset.mem_image.mpr ⟨u.length,
      Finset.mem_range.mpr (Nat.lt_succ_of_le h.length_le),
      (List.prefix_iff_eq_take.mp h).symm⟩

def sourceNodes (M : Matrix) : Finset Node :=
  (prefixes M).image Node.matrix ∪
  (Finset.range M.length).biUnion (fun d => (prefixes (row M d)).image Node.word) ∪
  (Finset.range (M.length + 1)).image Node.level ∪
  (Finset.range M.length).biUnion
    (fun d => (Finset.range ((row M d).length + 1)).image Node.level)

theorem sourceBound_mem {X : Finset Matrix} {z : Node}
    (h : SourceBound (↑X) z) : z ∈ X.biUnion sourceNodes := by
  cases z with
  | matrix A =>
    obtain ⟨M, hM, hp⟩ := h
    apply Finset.mem_biUnion.mpr
    refine ⟨M, hM, ?_⟩
    simp only [sourceNodes, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl (Finset.mem_image.mpr
      ⟨A, (mem_prefixes_iff A M).mpr hp, rfl⟩)))
  | word u =>
    obtain ⟨M, hM, d, hd, hp⟩ := h
    apply Finset.mem_biUnion.mpr
    refine ⟨M, hM, ?_⟩
    simp only [sourceNodes, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inr (Finset.mem_biUnion.mpr
      ⟨d, Finset.mem_range.mpr hd, Finset.mem_image.mpr
      ⟨u, (mem_prefixes_iff u (row M d)).mpr hp, rfl⟩⟩)))
  | level a =>
    obtain ⟨M, hM, hlen | ⟨d, hd, hlen⟩⟩ := h
    · apply Finset.mem_biUnion.mpr
      refine ⟨M, hM, ?_⟩
      simp only [sourceNodes, Finset.mem_union]
      exact Or.inl (Or.inr (Finset.mem_image.mpr
        ⟨a, Finset.mem_range.mpr (Nat.lt_succ_of_le hlen), rfl⟩))
    · apply Finset.mem_biUnion.mpr
      refine ⟨M, hM, ?_⟩
      simp only [sourceNodes, Finset.mem_union]
      exact Or.inr (Finset.mem_biUnion.mpr
        ⟨d, Finset.mem_range.mpr hd, Finset.mem_image.mpr
        ⟨a, Finset.mem_range.mpr (Nat.lt_succ_of_le hlen), rfl⟩⟩)

/-- Finiteness of the least generated closure, proved from finite sources;
not assumed as a property of a normalization oracle. -/
theorem retained_finite (X : Finset Matrix) :
    {z | Retained (↑X) z}.Finite := by
  apply (X.biUnion sourceNodes).finite_toSet.subset
  intro z hz
  exact sourceBound_mem (retained_sourceBound hz)

/-- Triangularity turns the source bound on levels into an original-height bound. -/
theorem retained_level_bound {X : Set Matrix} (htri : ∀ M ∈ X, Triangular M)
    {d : Nat} (hd : Retained X (.level d)) : ∃ M ∈ X, d ≤ M.length := by
  obtain ⟨M, hM, hlen | ⟨a, ha, hlen⟩⟩ := retained_sourceBound hd
  · exact ⟨M, hM, hlen⟩
  · have hr : (row M a).length = a := by
      simpa [row, List.getD_eq_getElem?_getD, ha] using htri M hM ⟨a, ha⟩
    exact ⟨M, hM, by omega⟩

theorem retained_singleton_iff (M : Matrix) (z : Node) :
    Retained {M} z ↔ z = .matrix M ∨ z = .level M.length := by
  constructor
  · intro hz
    have hc : Closed {z | z = Node.matrix M ∨ z = Node.level M.length} := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro A B hA hB
        simp only [Set.mem_setOf_eq, Node.matrix.injEq, reduceCtorEq, or_false] at *
        subst A; subst B; simp [commonPrefix_self]
      · intro u v hu; simp at hu
      · intro A hA
        simp only [Set.mem_setOf_eq, Node.matrix.injEq, reduceCtorEq, or_false] at hA
        subst A; simp
      · intro u hu; simp at hu
      · intro A d hA hd _
        simp only [Set.mem_setOf_eq, Node.matrix.injEq, reduceCtorEq, or_false] at hA
        simp only [Set.mem_setOf_eq, Node.level.injEq, reduceCtorEq, false_or] at hd
        subst A; subst d; simp
      · intro u d hu; simp at hu
      · intro A d hA hd hlt
        simp only [Set.mem_setOf_eq, Node.matrix.injEq, reduceCtorEq, or_false] at hA
        simp only [Set.mem_setOf_eq, Node.level.injEq, reduceCtorEq, false_or] at hd
        subst A; subst d; omega
    exact retained_least hc (by simp) hz
  · rintro (rfl | rfl)
    · exact Retained.original (by simp)
    · exact Retained.matrixHeight (Retained.original (by simp))

end RamseyCommon
