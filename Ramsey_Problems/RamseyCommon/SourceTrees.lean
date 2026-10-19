import RamseyCommon.Closure
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction

/-!
# Concrete strong binary subtrees and their canonical word valuations

`StrongWordTree` is a subset-level presentation of the strong subtrees used
in Section 3. Its root may have any ambient height. A successor is specified
by the actual ambient cone above `u ++ [b]`, not by a putative valuation map.
The canonical valuation is constructed recursively from this data, and its
membership, level, prefix, bit, injectivity, and level-surjectivity properties
are proved. No Ramsey or Milliken principle is assumed.
-/

namespace RamseyCommon.SourceTrees

open RamseyCommon

/-- Actual infinite strong subtrees of the binary prefix tree. All conditions
are expressed in terms of their nodes and ambient prefix cones. -/
structure StrongWordTree where
  level : ℕ → ℕ
  level_strictMono : StrictMono level
  nodes : ℕ → Set Word
  root : Word
  root_mem : root ∈ nodes 0
  root_unique : ∀ u ∈ nodes 0, u = root
  node_length : ∀ n u, u ∈ nodes n → u.length = level n
  successor : ∀ n u, u ∈ nodes n → ∀ b : Bool,
    ∃! v : Word, v ∈ nodes (n + 1) ∧ u ++ [b] <+: v
  parent : ∀ n v, v ∈ nodes (n + 1) →
    ∃ u : Word, u ∈ nodes n ∧ u <+: v

namespace StrongWordTree

variable (S : StrongWordTree)

/-- Choose the unique next-level node in the specified ambient cone.
The fallback is irrelevant: valuation membership is established below. -/
noncomputable def next (n : ℕ) (u : Word) (b : Bool) : Word := by
  classical
  exact if hu : u ∈ S.nodes n then Classical.choose (S.successor n u hu b) else []

theorem next_mem (n : ℕ) (u : Word) (hu : u ∈ S.nodes n) (b : Bool) :
    S.next n u b ∈ S.nodes (n + 1) := by
  simp only [next, dif_pos hu]
  exact (Classical.choose_spec (S.successor n u hu b)).1.1

theorem next_cone (n : ℕ) (u : Word) (hu : u ∈ S.nodes n) (b : Bool) :
    u ++ [b] <+: S.next n u b := by
  simp only [next, dif_pos hu]
  exact (Classical.choose_spec (S.successor n u hu b)).1.2

theorem next_eq (n : ℕ) (u : Word) (hu : u ∈ S.nodes n) (b : Bool)
    (v : Word) (hv : v ∈ S.nodes (n + 1)) (hcone : u ++ [b] <+: v) :
    S.next n u b = v := by
  simp only [next, dif_pos hu]
  exact ((Classical.choose_spec (S.successor n u hu b)).2 v ⟨hv, hcone⟩).symm

/-- The word valuation from the paper, following source bits from left to
right. Right-recursion lets the recursion step append the next source bit. -/
noncomputable def valuation (w : Word) : Word :=
  List.reverseRecOn w S.root (fun w b u => S.next w.length u b)

@[simp] theorem valuation_nil : S.valuation [] = S.root := by
  simp [valuation]

@[simp] theorem valuation_append (w : Word) (b : Bool) :
    S.valuation (w ++ [b]) = S.next w.length (S.valuation w) b := by
  simp only [valuation, List.reverseRecOn_concat]

theorem valuation_mem (w : Word) : S.valuation w ∈ S.nodes w.length := by
  induction w using List.reverseRecOn with
  | nil => simpa using S.root_mem
  | append_singleton w b ih =>
      simpa only [List.length_append, List.length_singleton, valuation_append]
        using S.next_mem w.length (S.valuation w) ih b

@[simp] theorem valuation_length (w : Word) :
    (S.valuation w).length = S.level w.length :=
  S.node_length _ _ (S.valuation_mem w)

theorem valuation_append_cone (w : Word) (b : Bool) :
    S.valuation w ++ [b] <+: S.valuation (w ++ [b]) := by
  rw [valuation_append]
  exact S.next_cone _ _ (S.valuation_mem w) b

theorem valuation_prefix_step (w : Word) (b : Bool) :
    S.valuation w <+: S.valuation (w ++ [b]) :=
  (List.prefix_append _ _).trans (S.valuation_append_cone w b)

theorem valuation_prefix_append (w tail : Word) :
    S.valuation w <+: S.valuation (w ++ tail) := by
  induction tail using List.reverseRecOn with
  | nil => simp
  | append_singleton tail b ih =>
      simpa only [List.append_assoc] using ih.trans (S.valuation_prefix_step (w ++ tail) b)

theorem valuation_prefix {u v : Word} (h : u <+: v) :
    S.valuation u <+: S.valuation v := by
  obtain ⟨tail, rfl⟩ := h
  exact S.valuation_prefix_append u tail

private theorem getD_eq_of_prefix {u v : Word} (h : u <+: v) {i : ℕ}
    (hi : i < u.length) : u.getD i false = v.getD i false := by
  obtain ⟨tail, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- The next source bit appears at precisely the previous selected ambient height. -/
theorem valuation_new_bit (w : Word) (b : Bool) :
    (S.valuation (w ++ [b])).getD (S.level w.length) false = b := by
  calc
    (S.valuation (w ++ [b])).getD (S.level w.length) false =
        (S.valuation w ++ [b]).getD (S.level w.length) false :=
      (getD_eq_of_prefix (S.valuation_append_cone w b) (by simp)).symm
    _ = b := by
      rw [← S.valuation_length w, List.getD_append_right _ _ _ _ le_rfl]
      simp

/-- Every selected coordinate reads the corresponding source bit. -/
theorem valuation_bit (w : Word) (i : ℕ) (hi : i < w.length) :
    (S.valuation w).getD (S.level i) false = w.getD i false := by
  induction w using List.reverseRecOn with
  | nil => simp at hi
  | append_singleton w b ih =>
      by_cases hiw : i < w.length
      · calc
          (S.valuation (w ++ [b])).getD (S.level i) false =
              (S.valuation w).getD (S.level i) false :=
            (getD_eq_of_prefix (S.valuation_prefix_step w b)
              (by simpa using S.level_strictMono hiw)).symm
          _ = w.getD i false := ih hiw
          _ = (w ++ [b]).getD i false :=
            (List.getD_append _ _ _ _ hiw).symm
      · have hieq : i = w.length := by simp only [List.length_append, List.length_singleton] at hi; omega
        subst i
        rw [S.valuation_new_bit]
        rw [List.getD_append_right _ _ _ _ le_rfl]
        simp

/-- The recursively constructed valuation is injective, including between
different source levels. -/
theorem valuation_injective : Function.Injective S.valuation := by
  intro u v huv
  have hlen : u.length = v.length := S.level_strictMono.injective (by
    simpa only [valuation_length] using congrArg List.length huv)
  apply List.ext_getElem hlen
  intro i hi hj
  have hbits := congrArg (fun w : Word => w.getD (S.level i) false) huv
  rw [S.valuation_bit u i hi, S.valuation_bit v i hj] at hbits
  simpa [List.getD_eq_getElem?_getD, hi, hj] using hbits

/-- Every retained word at level `n` is obtained from a unique source word
of length `n`; this is the surjectivity used in exact relative envelopes. -/
theorem valuation_surjective_level (n : ℕ) (v : Word) (hv : v ∈ S.nodes n) :
    ∃ w : Word, w.length = n ∧ S.valuation w = v := by
  induction n generalizing v with
  | zero =>
      exact ⟨[], rfl, (S.valuation_nil).trans (S.root_unique v hv).symm⟩
  | succ n ih =>
      obtain ⟨u, hu, huv⟩ := S.parent n v hv
      obtain ⟨w, hwlen, hw⟩ := ih u hu
      have hlt : u.length < v.length := by
        rw [S.node_length n u hu, S.node_length (n + 1) v hv]
        exact S.level_strictMono (Nat.lt_succ_self n)
      obtain ⟨tail, rfl⟩ := huv
      cases tail with
      | nil => simp at hlt
      | cons b tail =>
          refine ⟨w ++ [b], by simp [hwlen], ?_⟩
          rw [valuation_append, hwlen, hw]
          apply S.next_eq n u hu b _ hv
          exact ⟨tail, by simp [List.append_assoc]⟩

end StrongWordTree

end RamseyCommon.SourceTrees
