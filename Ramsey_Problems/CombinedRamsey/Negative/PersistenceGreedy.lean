import CombinedRamsey.Negative.PersistenceTypes

/-! The greedy-halt step is a genuine countable embedding construction:
if every supported finite initial embedding extends, their compatible
chosen extensions form a full self-embedding. -/

namespace CombinedRamsey.Negative

open RelationalRamsey632

variable {L : Language} (K : RelStructure L ℕ)

def initialStructure (n : ℕ) := K.pullback (Fin.val : Fin n → ℕ)

def SupportedInitial (B : Set ℕ) (n : ℕ) :=
  {e : RelEmbedding (initialStructure K n) K | ∀ i, e i ∈ B}

theorem embedding_of_initial_extensions (B : Set ℕ)
    (hext : ∀ n (e : SupportedInitial K B n),
      ∃ f : SupportedInitial K B (n + 1), ∀ i : Fin n, f.val i.castSucc = e.val i) :
    ∃ f : RelEmbedding K K, ∀ x, f x ∈ B := by
  classical
  let e0 : SupportedInitial K B 0 :=
    ⟨RelEmbedding.pullback K Fin.val Fin.val_injective, fun i => Fin.elim0 i⟩
  choose next hnext using hext
  let seq : ∀ n, SupportedInitial K B n :=
    fun n => Nat.rec e0 (fun n e => next n e) n
  have hsucc : ∀ n (i : Fin n), (seq (n + 1)).val i.castSucc = (seq n).val i := by
    intro n i
    exact hnext n (seq n) i
  have hagree : ∀ {n m : ℕ} (hnm : n ≤ m) (i : Fin n),
      (seq m).val (Fin.castLE hnm i) = (seq n).val i := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => intro i; rfl
    | succ m hnm ih =>
      intro i
      have hidx : Fin.castLE (Nat.le_succ_of_le hnm) i = (Fin.castLE hnm i).castSucc := rfl
      rw [hidx, hsucc, ih]
  let f : ℕ → ℕ := fun x => (seq (x + 1)).val ⟨x, by omega⟩
  have hf : ∀ (m : ℕ) (i : Fin m), f i.val = (seq m).val i := by
    intro m i
    exact (hagree (by omega : i.val + 1 ≤ m) ⟨i.val, by omega⟩).symm
  let g : RelEmbedding K K := {
    toFun := f
    injective := by
      intro x y hxy
      let m := max x y + 1
      let ix : Fin m := ⟨x, by dsimp [m]; omega⟩
      let iy : Fin m := ⟨y, by dsimp [m]; omega⟩
      have heq : (seq m).val ix = (seq m).val iy := (hf m ix).symm.trans (hxy.trans (hf m iy))
      exact congrArg Fin.val ((seq m).val.injective heq)
    map_rel := by
      intro r R t
      let m := Finset.univ.sup t + 1
      have hb : ∀ i, t i < m := fun i =>
        Nat.lt_succ_of_le (Finset.le_sup (f := t) (Finset.mem_univ i))
      let u : Fin r → Fin m := fun i => ⟨t i, hb i⟩
      have heq : (seq m).val ∘ u = f ∘ t := by
        funext i
        exact (hf m (u i)).symm
      have hrel := (seq m).val.map_rel R u
      change K.rel R t ↔ K.rel R ((seq m).val ∘ u) at hrel
      rw [heq] at hrel
      exact hrel }
  exact ⟨g, fun x => (seq (x + 1)).property ⟨x, by omega⟩⟩

/-- If no self-copy lies in B, an actual finite initial embedding into B
has a required next one-point type with no realization in B. -/
theorem greedy_halt (B : Set ℕ)
    (hno : ¬ ∃ f : RelEmbedding K K, ∀ x, f x ∈ B) :
    ∃ (n : ℕ) (e : SupportedInitial K B n),
      ¬ ∃ f : SupportedInitial K B (n + 1), ∀ i : Fin n, f.val i.castSucc = e.val i := by
  classical
  by_contra h
  push Not at h
  exact hno (embedding_of_initial_extensions K B h)

end CombinedRamsey.Negative

