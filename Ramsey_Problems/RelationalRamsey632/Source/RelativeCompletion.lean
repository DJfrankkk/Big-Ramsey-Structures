import RelationalRamsey632.Source.FiniteValuations
import Mathlib.Data.Fintype.Prod

/-! Constructive finite relative completion in actual source coordinates.
The prescribed-cone uniqueness condition is separated so that it can be
proved directly from meet closure in the marked-envelope module. -/

namespace RelationalRamsey632.Source

namespace StrongVector

variable {A : ℕ → Type} [∀ j, Nonempty (A j)]
    {e : ℕ → ℕ} {he : StrictMono e} (S : StrongVector A e he)

theorem extend_to_level (i n m : ℕ) (hnm : n ≤ m)
    (p : Level A i (e n)) (hp : p ∈ S.nodes i n) :
    ∃ q : Level A i (e m), q ∈ S.nodes i m ∧
      q.restrict (he.monotone hnm) = p := by
  classical
  induction m, hnm using Nat.le_induction with
  | base => exact ⟨p, hp, Level.restrict_refl p⟩
  | succ m hnm ih =>
    obtain ⟨q, hq, hqp⟩ := ih
    let a : A (i + 1) := Classical.choice inferInstance
    let v : Level A (i + 1) (e m) := Classical.choice inferInstance
    let q' := S.next i m ⟨q, hq⟩ a v
    refine ⟨q'.val, q'.property, ?_⟩
    have hh := congrArg (fun t : Level A i (e m + 1) =>
      t.restrict (Nat.le_succ (e m))) (S.next_cone i m ⟨q, hq⟩ a v)
    have hparent : q'.val.restrict (he.monotone (Nat.le_succ m)) = q := by
      simpa only [Level.restrict_restrict, Level.extend_restrict] using hh
    calc
      q'.val.restrict (he.monotone (Nat.le_trans hnm (Nat.le_succ m))) =
          (q'.val.restrict (he.monotone (Nat.le_succ m))).restrict (he.monotone hnm) := by
        simp only [Level.restrict_restrict]
      _ = p := by rw [hparent, hqp]

theorem extend_successor_cone (i n m : ℕ) (hnm : n < m)
    (p : Level A i (e n)) (hp : p ∈ S.nodes i n)
    (a : A (i + 1)) (v : Level A (i + 1) (e n)) :
    ∃ q : Level A i (e m), q ∈ S.nodes i m ∧
      q.restrict (Nat.succ_le_of_lt (he hnm)) = Level.extend p a v := by
  let q1 := S.next i n ⟨p, hp⟩ a v
  obtain ⟨q, hq, hqq1⟩ := S.extend_to_level i (n + 1) m (Nat.succ_le_of_lt hnm)
    q1.val q1.property
  refine ⟨q, hq, ?_⟩
  have hh := congrArg (fun t : Level A i (e (n + 1)) =>
    t.restrict (Nat.succ_le_of_lt (he (Nat.lt_succ_self n)))) hqq1
  have hh' : q.restrict (Nat.succ_le_of_lt (he hnm)) =
      q1.val.restrict (Nat.succ_le_of_lt (he (Nat.lt_succ_self n))) := by
    simpa only [Level.restrict_restrict] using hh
  exact hh'.trans (S.next_cone i n ⟨p, hp⟩ a v)

end StrongVector

structure PrescribedLevels {A : ℕ → Type} {e : ℕ → ℕ} {he : StrictMono e}
    (S : StrongVector A e he) (l : ℕ → ℕ) (hl : StrictMono l) (h : ℕ) where
  nodes : (i n : ℕ) → Set (Level A i (e (l n)))
  source : ∀ i n, nodes i n ⊆ S.nodes i (l n)
  root_unique : ∀ i, i < h → ∀ p ∈ nodes i 0, ∀ q ∈ nodes i 0, p = q
  parent : ∀ i, i < h → ∀ n, n + 1 < h → ∀ q ∈ nodes i (n + 1),
    q.restrict (he.monotone (hl.monotone (Nat.le_succ n))) ∈ nodes i n
  cone_unique : ∀ i, i < h → ∀ n, n + 1 < h →
    ∀ p ∈ nodes i (n + 1), ∀ q ∈ nodes i (n + 1),
      p.restrict (Nat.succ_le_of_lt (he (hl (Nat.lt_succ_self n)))) =
        q.restrict (Nat.succ_le_of_lt (he (hl (Nat.lt_succ_self n)))) → p = q

namespace PrescribedLevels

variable {A : ℕ → Type} [∀ j, Fintype (A j)] [∀ j, Nonempty (A j)]
    {e : ℕ → ℕ} {he : StrictMono e} {S : StrongVector A e he}
    {l : ℕ → ℕ} {hl : StrictMono l} {h : ℕ}
    (D : PrescribedLevels S l hl h)

private structure CompleteLevel (i n : ℕ) where
  nodes : Set (Level A i (e (l n)))
  finite : nodes.Finite
  source : nodes ⊆ S.nodes i (l n)

private noncomputable def rootChoice (i : ℕ) :
    {p : Level A i (e (l 0)) // p ∈ S.nodes i (l 0)} := by
  classical
  by_cases hd : (D.nodes i 0).Nonempty
  · exact ⟨Classical.choose hd, D.source i 0 (Classical.choose_spec hd)⟩
  · let t : Level A i (l 0) := Classical.choice inferInstance
    exact ⟨S.valuation (l 0) i t, S.valuation_mem (l 0) i t⟩

omit [∀ j, Fintype (A j)] in
private theorem rootChoice_contains (i : ℕ) (hi : i < h)
    (p : Level A i (e (l 0))) (hp : p ∈ D.nodes i 0) :
    p = (D.rootChoice i).val := by
  classical
  have hd : (D.nodes i 0).Nonempty := ⟨p, hp⟩
  unfold rootChoice
  simp only [dif_pos hd]
  exact D.root_unique i hi p hp (Classical.choose hd) (Classical.choose_spec hd)

private noncomputable def chosenExtension (i n : ℕ)
    (p : {p : Level A i (e (l n)) // p ∈ S.nodes i (l n)})
    (a : A (i + 1)) (v : Level A (i + 1) (e (l n))) :
    {q : Level A i (e (l (n + 1))) // q ∈ S.nodes i (l (n + 1)) ∧
      q.restrict (Nat.succ_le_of_lt (he (hl (Nat.lt_succ_self n)))) = Level.extend p.val a v} := by
  classical
  by_cases hd : ∃ q ∈ D.nodes i (n + 1),
      q.restrict (Nat.succ_le_of_lt (he (hl (Nat.lt_succ_self n)))) = Level.extend p.val a v
  · let q := Classical.choose hd
    have hq := Classical.choose_spec hd
    exact ⟨q, D.source i (n + 1) hq.1, hq.2⟩
  · exact ⟨Classical.choose (S.extend_successor_cone i (l n) (l (n + 1))
      (hl (Nat.lt_succ_self n)) p.val p.property a v),
      Classical.choose_spec (S.extend_successor_cone i (l n) (l (n + 1))
        (hl (Nat.lt_succ_self n)) p.val p.property a v)⟩

private theorem chosenExtension_prescribed (i : ℕ) (hi : i < h)
    (n : ℕ) (hn : n + 1 < h)
    (p : {p : Level A i (e (l n)) // p ∈ S.nodes i (l n)})
    (a : A (i + 1)) (v : Level A (i + 1) (e (l n)))
    (q : Level A i (e (l (n + 1)))) (hq : q ∈ D.nodes i (n + 1))
    (hcone : q.restrict (Nat.succ_le_of_lt (he (hl (Nat.lt_succ_self n))))
      = Level.extend p.val a v) : (D.chosenExtension i n p a v).val = q := by
  classical
  have hd : ∃ q ∈ D.nodes i (n + 1),
      q.restrict (Nat.succ_le_of_lt (he (hl (Nat.lt_succ_self n)))) = Level.extend p.val a v :=
    ⟨q, hq, hcone⟩
  unfold chosenExtension
  simp only [dif_pos hd]
  have hq' := Classical.choose_spec hd
  exact D.cone_unique i hi n hn _ hq'.1 q hq (hq'.2.trans hcone.symm)

private noncomputable def completeLevels (i : ℕ) : (n : ℕ) → CompleteLevel (S := S) (l := l) i n
  | 0 => {
      nodes := {(D.rootChoice i).val}
      finite := Set.finite_singleton _
      source := by
        intro p hp
        exact (Set.mem_singleton_iff.mp hp) ▸ (D.rootChoice i).property }
  | n + 1 => by
      classical
      let prev := completeLevels i n
      letI : Fintype prev.nodes := prev.finite.fintype
      let choices : prev.nodes × A (i + 1) × Level A (i + 1) (e (l n)) →
          Level A i (e (l (n + 1))) := fun x =>
        (D.chosenExtension i n ⟨x.1.val, prev.source x.1.property⟩ x.2.1 x.2.2).val
      exact {
        nodes := Set.range choices
        finite := by
          have hf := (Set.finite_univ : (Set.univ : Set
            (prev.nodes × A (i + 1) × Level A (i + 1) (e (l n)))).Finite).image choices
          simpa only [Set.image_univ] using hf
        source := by
          rintro q ⟨x, rfl⟩
          exact (D.chosenExtension i n ⟨x.1.val, prev.source x.1.property⟩ x.2.1 x.2.2).property.1 }

private theorem completeLevels_contains (i : ℕ) (hi : i < h) (n : ℕ) (hn : n < h) :
    D.nodes i n ⊆ (D.completeLevels i n).nodes := by
  induction n with
  | zero =>
    intro p hp
    exact Set.mem_singleton_iff.mpr (D.rootChoice_contains i hi p hp)
  | succ n ih =>
    intro q hq
    let p := q.restrict (he.monotone (hl.monotone (Nat.le_succ n)))
    have hp : p ∈ (D.completeLevels i n).nodes :=
      ih (Nat.lt_of_succ_lt hn) (D.parent i hi n hn q hq)
    let a := q.singleton (he (hl (Nat.lt_succ_self n)))
    let v := q.slice (he (hl (Nat.lt_succ_self n)))
    have hcone : q.restrict (Nat.succ_le_of_lt (he (hl (Nat.lt_succ_self n))))
        = Level.extend p a v := by
      apply Level.successor_ext
      · simp only [Level.restrict_restrict, Level.extend_restrict]
        rfl
      · simp only [Level.singleton_restrict, Level.extend_singleton]
        rfl
      · simp only [Level.slice_restrict, Level.extend_slice]
        rfl
    refine ⟨(⟨p, hp⟩, a, v), ?_⟩
    exact D.chosenExtension_prescribed i hi n hn
      ⟨p, (D.completeLevels i n).source hp⟩ a v q hq hcone

/-- The selected finite strong vector is constructed by filling every
ambient immediate successor cone and preferentially keeping its prescribed
node whenever present. -/
noncomputable def completion : FiniteStrongVector A (e ∘ l) (he.comp hl) h where
  nodes i n := (D.completeLevels i n).nodes
  root i _ := (D.rootChoice i).val
  root_mem i _ := Set.mem_singleton _
  root_unique i _ p hp := Set.mem_singleton_iff.mp hp
  successor i _ n _ p hp a v := by
    classical
    let ps : {p : Level A i (e (l n)) // p ∈ S.nodes i (l n)} :=
      ⟨p, (D.completeLevels i n).source hp⟩
    let q := D.chosenExtension i n ps a v
    refine ⟨q.val, ⟨⟨(⟨p, hp⟩, a, v), rfl⟩, q.property.2⟩, ?_⟩
    intro q' hq'
    obtain ⟨⟨p', a', v'⟩, hq'eq⟩ := hq'.1
    let qs := D.chosenExtension i n
      ⟨p'.val, (D.completeLevels i n).source p'.property⟩ a' v'
    have hc : Level.extend p'.val a' v' = Level.extend p a v :=
      qs.property.2.symm.trans ((congrArg (fun t : Level A i (e (l (n + 1))) =>
        t.restrict (Nat.succ_le_of_lt (he (hl (Nat.lt_succ_self n))))) hq'eq).trans hq'.2)
    have hp'eq : p'.val = p := by
      have hh := congrArg (fun t : Level A i (e (l n) + 1) =>
        t.restrict (Nat.le_succ (e (l n)))) hc
      exact (Level.extend_restrict _ _ _).symm.trans (hh.trans (Level.extend_restrict _ _ _))
    have ha'eq : a' = a := by
      have hh := congrArg (fun t : Level A i (e (l n) + 1) =>
        t.singleton (Nat.lt_succ_self (e (l n)))) hc
      exact (Level.extend_singleton _ _ _).symm.trans (hh.trans (Level.extend_singleton _ _ _))
    have hv'eq : v' = v := by
      have hh := congrArg (fun t : Level A i (e (l n) + 1) =>
        t.slice (Nat.lt_succ_self (e (l n)))) hc
      exact (Level.extend_slice _ _ _).symm.trans (hh.trans (Level.extend_slice _ _ _))
    have hps : p' = (⟨p, hp⟩ : (D.completeLevels i n).nodes) := Subtype.ext hp'eq
    subst p'
    subst a'
    subst v'
    exact hq'eq.symm
  parent i _ n _ q hq := by
    obtain ⟨⟨p, a, v⟩, rfl⟩ := hq
    let qs := D.chosenExtension i n
      ⟨p.val, (D.completeLevels i n).source p.property⟩ a v
    have hh := congrArg (fun t : Level A i (e (l n) + 1) =>
      t.restrict (Nat.le_succ (e (l n)))) qs.property.2
    have heq : qs.val.restrict (he.monotone (hl.monotone (Nat.le_succ n))) = p.val := by
      simpa only [Level.restrict_restrict, Level.extend_restrict] using hh
    exact heq ▸ p.property

theorem completion_contains (i : ℕ) (hi : i < h) (n : ℕ) (hn : n < h) :
    D.nodes i n ⊆ D.completion.nodes i n := D.completeLevels_contains i hi n hn

theorem completion_relative (i n : ℕ) :
    D.completion.nodes i n ⊆ S.nodes i (l n) := (D.completeLevels i n).source

theorem completion_finite_levels (i n : ℕ) :
    (D.completion.nodes i n).Finite := (D.completeLevels i n).finite

end PrescribedLevels

end RelationalRamsey632.Source
