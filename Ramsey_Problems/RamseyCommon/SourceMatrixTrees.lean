import RamseyCommon.SourceTrees

/-!
# Matrix valuations built from actual strong vector subtrees

This file uses the word valuation constructed in `SourceTrees`. Matrix
successors are specified in actual ambient cones, and the valuation is built
by recursion. Membership, triangularity, height, entire-row preservation,
selected entries, and injectivity are consequences, not input hypotheses.
There is no Milliken or Ramsey axiom.
-/

namespace RamseyCommon.SourceTrees

open RamseyCommon

theorem triangular_append_iff (M : Matrix) (v : Word) :
    Triangular (M ++ [v]) ↔ Triangular M ∧ v.length = M.length := by
  constructor
  · intro htri
    refine ⟨triangular_of_prefix (List.prefix_append _ _) htri, ?_⟩
    have hlast : M.length < (M ++ [v]).length := by simp
    have hrow := htri ⟨M.length, hlast⟩
    simpa [List.getElem_append_right] using hrow
  · rintro ⟨htri, hv⟩
    intro i
    by_cases hi : i.val < M.length
    · simpa only [List.getElem_append_left hi] using htri ⟨i.val, hi⟩
    · have hieq : i.val = M.length := by
        have hil := i.isLt
        simp only [List.length_append, List.length_singleton] at hil
        omega
      simpa [List.getElem_append_right, hi, hieq] using hv

/-- The matrix coordinate of an infinite strong vector subtree on a fixed
selected level set. A cone is indexed by an entire ambient row, so matrix
branching at ambient height `n` is the full set of binary words of length `n`. -/
structure StrongMatrixTree (level : ℕ → ℕ) where
  nodes : ℕ → Set Matrix
  root : Matrix
  root_mem : root ∈ nodes 0
  root_unique : ∀ M ∈ nodes 0, M = root
  node_length : ∀ n M, M ∈ nodes n → M.length = level n
  node_triangular : ∀ n M, M ∈ nodes n → Triangular M
  successor : ∀ n M, M ∈ nodes n → ∀ v : Word, v.length = level n →
    ∃! N : Matrix, N ∈ nodes (n + 1) ∧ M ++ [v] <+: N
  parent : ∀ n N, N ∈ nodes (n + 1) →
    ∃ M : Matrix, M ∈ nodes n ∧ M <+: N

namespace StrongMatrixTree

variable {S : StrongWordTree} (R : StrongMatrixTree S.level)

noncomputable def next (n : ℕ) (M : Matrix) (v : Word) : Matrix := by
  classical
  exact if hM : M ∈ R.nodes n then
    if hv : v.length = S.level n then Classical.choose (R.successor n M hM v hv) else []
  else []

theorem next_mem (n : ℕ) (M : Matrix) (hM : M ∈ R.nodes n)
    (v : Word) (hv : v.length = S.level n) :
    R.next n M v ∈ R.nodes (n + 1) := by
  simp only [next, dif_pos hM, dif_pos hv]
  exact (Classical.choose_spec (R.successor n M hM v hv)).1.1

theorem next_cone (n : ℕ) (M : Matrix) (hM : M ∈ R.nodes n)
    (v : Word) (hv : v.length = S.level n) :
    M ++ [v] <+: R.next n M v := by
  simp only [next, dif_pos hM, dif_pos hv]
  exact (Classical.choose_spec (R.successor n M hM v hv)).1.2

/-- The matrix map Ψ is recursively built using the already constructed ν. -/
noncomputable def valuation (M : Matrix) : Matrix :=
  List.reverseRecOn M R.root (fun M v N => R.next M.length N (S.valuation v))

@[simp] theorem valuation_nil : R.valuation [] = R.root := by
  simp [valuation]

@[simp] theorem valuation_append (M : Matrix) (v : Word) :
    R.valuation (M ++ [v]) = R.next M.length (R.valuation M) (S.valuation v) := by
  simp only [valuation, List.reverseRecOn_concat]

theorem valuation_mem (M : Matrix) (htri : Triangular M) :
    R.valuation M ∈ R.nodes M.length := by
  revert htri
  induction M using List.reverseRecOn with
  | nil => intro _; simpa using R.root_mem
  | append_singleton M v ih =>
      intro htri
      obtain ⟨hM, hv⟩ := (triangular_append_iff M v).mp htri
      have hν : (S.valuation v).length = S.level M.length := by simp [hv]
      simpa only [List.length_append, List.length_singleton, valuation_append] using
        R.next_mem M.length (R.valuation M) (ih hM) (S.valuation v) hν

@[simp] theorem valuation_length (M : Matrix) (htri : Triangular M) :
    (R.valuation M).length = S.level M.length :=
  R.node_length _ _ (R.valuation_mem M htri)

theorem valuation_triangular (M : Matrix) (htri : Triangular M) :
    Triangular (R.valuation M) :=
  R.node_triangular _ _ (R.valuation_mem M htri)

theorem valuation_append_cone (M : Matrix) (v : Word)
    (htri : Triangular (M ++ [v])) :
    R.valuation M ++ [S.valuation v] <+: R.valuation (M ++ [v]) := by
  obtain ⟨hM, hv⟩ := (triangular_append_iff M v).mp htri
  rw [valuation_append]
  apply R.next_cone M.length (R.valuation M) (R.valuation_mem M hM) (S.valuation v)
  simp [hv]

theorem valuation_prefix_step (M : Matrix) (v : Word)
    (htri : Triangular (M ++ [v])) :
    R.valuation M <+: R.valuation (M ++ [v]) :=
  (List.prefix_append _ _).trans (R.valuation_append_cone M v htri)

theorem valuation_prefix_append (M tail : Matrix) (htri : Triangular (M ++ tail)) :
    R.valuation M <+: R.valuation (M ++ tail) := by
  revert htri
  induction tail using List.reverseRecOn with
  | nil => intro _; simp
  | append_singleton tail v ih =>
      intro htri
      have htri' : Triangular ((M ++ tail) ++ [v]) := by
        simpa only [List.append_assoc] using htri
      have hMtail := (triangular_append_iff (M ++ tail) v).mp htri'
      simpa only [List.append_assoc] using
        (ih hMtail.1).trans (R.valuation_prefix_step (M ++ tail) v htri')

theorem valuation_prefix {M N : Matrix} (htri : Triangular N) (hp : M <+: N) :
    R.valuation M <+: R.valuation N := by
  obtain ⟨tail, rfl⟩ := hp
  exact R.valuation_prefix_append M tail htri

/-- Appending one source row fixes the entire target row at the selected height. -/
theorem valuation_new_row (M : Matrix) (v : Word) (htri : Triangular (M ++ [v])) :
    row (R.valuation (M ++ [v])) (S.level M.length) = S.valuation v := by
  have hM := ((triangular_append_iff M v).mp htri).1
  have hrow := row_eq_of_prefix (R.valuation_append_cone M v htri)
    (d := S.level M.length) (by simp [R.valuation_length M hM])
  calc
    row (R.valuation (M ++ [v])) (S.level M.length) =
        row (R.valuation M ++ [S.valuation v]) (S.level M.length) := hrow.symm
    _ = S.valuation v := by
      unfold row
      rw [← R.valuation_length M hM, List.getD_append_right _ _ _ _ le_rfl]
      simp

/-- The entire-row identity of Lemma 3.1, with actual recursively constructed maps. -/
theorem valuation_row (M : Matrix) (htri : Triangular M) (i : ℕ) (hi : i < M.length) :
    row (R.valuation M) (S.level i) = S.valuation (row M i) := by
  revert htri hi
  induction M using List.reverseRecOn with
  | nil => intros; simp_all
  | append_singleton M v ih =>
      intro htri hi
      have hM := ((triangular_append_iff M v).mp htri).1
      by_cases hiM : i < M.length
      · calc
          row (R.valuation (M ++ [v])) (S.level i) = row (R.valuation M) (S.level i) :=
            (row_eq_of_prefix (R.valuation_prefix_step M v htri)
              (by simpa [R.valuation_length M hM] using S.level_strictMono hiM)).symm
          _ = S.valuation (row M i) := ih hM hiM
          _ = S.valuation (row (M ++ [v]) i) :=
            congrArg S.valuation (row_eq_of_prefix (List.prefix_append _ _) hiM)
      · have hieq : i = M.length := by
          simp only [List.length_append, List.length_singleton] at hi
          omega
        subst i
        rw [R.valuation_new_row M v htri]
        unfold row
        rw [List.getD_append_right _ _ _ _ le_rfl]
        simp

/-- Selected entries are the literal bits of the original matrix. -/
theorem valuation_entry (M : Matrix) (htri : Triangular M) (i j : ℕ)
    (hj : j < i) (hi : i < M.length) :
    (row (R.valuation M) (S.level i)).getD (S.level j) false = (row M i).getD j false := by
  rw [R.valuation_row M htri i hi]
  apply S.valuation_bit
  have hrow := htri ⟨i, hi⟩
  have hlen : (row M i).length = i := by
    simpa [row, List.getD_eq_getElem?_getD, hi] using hrow
  simpa [hlen] using hj

/-- The matrix valuation is injective on the actual lower-triangular source tree. -/
theorem valuation_injective : Set.InjOn R.valuation {M : Matrix | Triangular M} := by
  intro M hM N hN heq
  have hlen : M.length = N.length := S.level_strictMono.injective (by
    simpa only [R.valuation_length M hM, R.valuation_length N hN] using
      congrArg List.length heq)
  apply List.ext_getElem hlen
  intro i hi hj
  have hrows := congrArg (fun A : Matrix => row A (S.level i)) heq
  rw [R.valuation_row M hM i hi, R.valuation_row N hN i hj] at hrows
  have hsource := S.valuation_injective hrows
  simpa [row, List.getD_eq_getElem?_getD, hi, hj] using hsource

end StrongMatrixTree

end RamseyCommon.SourceTrees
