import Generic3Ramsey.SourceMatrixTrees
import Mathlib.Data.Finset.Union

/-!
# Finitely branching strong prefix systems

This is a common presentation of the actual word and matrix coordinates.
The finite set of ambient successor labels is explicit. Ancestors and
extensions are proved from the successor/parent conditions. The binary and
triangular-matrix strong trees are instantiated below, including a finite
enumeration of all ambient matrix successor rows.
-/

namespace Generic3Ramsey.SourceTrees

open Generic3Ramsey

def binaryWords : ℕ → Finset Word
  | 0 => {[]}
  | n + 1 => (binaryWords n).biUnion fun w => {w ++ [false], w ++ [true]}

theorem mem_binaryWords (n : ℕ) (w : Word) : w ∈ binaryWords n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [binaryWords]
  | succ n ih =>
      constructor
      · intro hw
        obtain ⟨u, hu, hwu⟩ := Finset.mem_biUnion.mp hw
        have hulen := (ih u).mp hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hwu
        rcases hwu with rfl | rfl <;> simp [hulen]
      · intro hlen
        rcases List.eq_nil_or_concat w with rfl | ⟨u, b, rfl⟩
        · simp at hlen
        · have hulen : u.length = n := by simpa using hlen
          apply Finset.mem_biUnion.mpr
          refine ⟨u, (ih u).mpr hulen, ?_⟩
          cases b <;> simp [List.concat_eq_append]

theorem binaryWords_nonempty (n : ℕ) : (binaryWords n).Nonempty := by
  refine ⟨List.replicate n false, (mem_binaryWords n _).mpr ?_⟩
  simp

/-- A strong subtree of a prefix tree, with its actual finite ambient cones. -/
structure StrongPrefixSystem (α : Type) [DecidableEq α] where
  level : ℕ → ℕ
  level_strictMono : StrictMono level
  nodes : ℕ → Set (List α)
  root : List α
  root_mem : root ∈ nodes 0
  root_unique : ∀ u ∈ nodes 0, u = root
  node_length : ∀ n u, u ∈ nodes n → u.length = level n
  children : ℕ → Finset α
  children_nonempty : ∀ n, (children n).Nonempty
  successor : ∀ n u, u ∈ nodes n → ∀ a ∈ children n,
    ∃! v : List α, v ∈ nodes (n + 1) ∧ u ++ [a] <+: v
  parent : ∀ n v, v ∈ nodes (n + 1) →
    ∃ u : List α, u ∈ nodes n ∧ ∃ a ∈ children n, u ++ [a] <+: v

namespace StrongPrefixSystem

variable {α : Type} [DecidableEq α] (S : StrongPrefixSystem α)

theorem ancestor (n m : ℕ) (hnm : n ≤ m) (v : List α) (hv : v ∈ S.nodes m) :
    ∃ u : List α, u ∈ S.nodes n ∧ u <+: v := by
  induction m generalizing n v with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      exact ⟨v, hv, List.prefix_refl _⟩
  | succ m ih =>
      by_cases hn : n = m + 1
      · subst n
        exact ⟨v, hv, List.prefix_refl _⟩
      · have hnm' : n ≤ m := by omega
        obtain ⟨w, hw, a, ha, hcone⟩ := S.parent m v hv
        obtain ⟨u, hu, hup⟩ := ih n hnm' w hw
        exact ⟨u, hu, hup.trans ((List.prefix_append _ _).trans hcone)⟩

theorem restrict_mem (n m : ℕ) (hnm : n ≤ m) (v : List α) (hv : v ∈ S.nodes m) :
    v.take (S.level n) ∈ S.nodes n := by
  obtain ⟨u, hu, hp⟩ := S.ancestor n m hnm v hv
  have heq := List.prefix_iff_eq_take.mp hp
  rw [S.node_length n u hu] at heq
  exact heq ▸ hu

/-- Balancedness, proved by recursively taking an actual successor cone. -/
theorem extend (n m : ℕ) (hnm : n ≤ m) (u : List α) (hu : u ∈ S.nodes n) :
    ∃ v : List α, v ∈ S.nodes m ∧ u <+: v := by
  induction m, hnm using Nat.le_induction with
  | base => exact ⟨u, hu, List.prefix_refl _⟩
  | succ m hnm ih =>
      obtain ⟨v, hv, huv⟩ := ih
      obtain ⟨a, ha⟩ := S.children_nonempty m
      obtain ⟨w, ⟨hw, hcone⟩, _⟩ := S.successor m v hv a ha
      exact ⟨w, hw, huv.trans ((List.prefix_append _ _).trans hcone)⟩

theorem extend_cone (n m : ℕ) (hnm : n < m) (u : List α) (hu : u ∈ S.nodes n)
    (a : α) (ha : a ∈ S.children n) :
    ∃ v : List α, v ∈ S.nodes m ∧ u ++ [a] <+: v := by
  obtain ⟨w, ⟨hw, hcone⟩, _⟩ := S.successor n u hu a ha
  obtain ⟨v, hv, hwv⟩ := S.extend (n + 1) m hnm w hw
  exact ⟨v, hv, hcone.trans hwv⟩

end StrongPrefixSystem

noncomputable def StrongWordTree.toPrefixSystem (S : StrongWordTree) : StrongPrefixSystem Bool where
  level := S.level
  level_strictMono := S.level_strictMono
  nodes := S.nodes
  root := S.root
  root_mem := S.root_mem
  root_unique := S.root_unique
  node_length := S.node_length
  children := fun _ => {false, true}
  children_nonempty := fun _ => ⟨false, by simp⟩
  successor := fun n u hu b _ => S.successor n u hu b
  parent := by
    intro n v hv
    obtain ⟨u, hu, hup⟩ := S.parent n v hv
    have hlt : u.length < v.length := by
      rw [S.node_length n u hu, S.node_length (n + 1) v hv]
      exact S.level_strictMono (Nat.lt_succ_self n)
    obtain ⟨tail, rfl⟩ := hup
    cases tail with
    | nil => simp at hlt
    | cons b tail =>
        refine ⟨u, hu, b, ?_, tail, ?_⟩
        · cases b <;> simp
        · simp [List.append_assoc]

noncomputable def StrongMatrixTree.toPrefixSystem {S : StrongWordTree}
    (R : StrongMatrixTree S.level) : StrongPrefixSystem Word where
  level := S.level
  level_strictMono := S.level_strictMono
  nodes := R.nodes
  root := R.root
  root_mem := R.root_mem
  root_unique := R.root_unique
  node_length := R.node_length
  children := fun n => binaryWords (S.level n)
  children_nonempty := fun n => binaryWords_nonempty (S.level n)
  successor := fun n u hu v hv => R.successor n u hu v ((mem_binaryWords _ _).mp hv)
  parent := by
    intro n N hN
    obtain ⟨M, hM, hp⟩ := R.parent n N hN
    have hlt : M.length < N.length := by
      rw [R.node_length n M hM, R.node_length (n + 1) N hN]
      exact S.level_strictMono (Nat.lt_succ_self n)
    have hNtri := R.node_triangular (n + 1) N hN
    obtain ⟨tail, rfl⟩ := hp
    cases tail with
    | nil => simp at hlt
    | cons v tail =>
        have hpre : M ++ [v] <+: M ++ v :: tail := ⟨tail, by simp [List.append_assoc]⟩
        have hvlen := ((triangular_append_iff M v).mp (triangular_of_prefix hpre hNtri)).2
        refine ⟨M, hM, v, (mem_binaryWords _ _).mpr ?_, hpre⟩
        exact hvlen.trans (R.node_length n M hM)

end Generic3Ramsey.SourceTrees
