import RelationalRamsey632.Source.Successors

/-!
# Valuations in genuine strong vectors

The successor condition quantifies over the whole ambient successor
alphabet: the singleton and the entire next-sort slice, rather than
selected-coordinate fragments. Valuations are constructed, not postulated.
-/

namespace RelationalRamsey632.Source

structure StrongVector (A : ℕ → Type) (e : ℕ → ℕ) (he : StrictMono e) where
  nodes : (i n : ℕ) → Set (Level A i (e n))
  root : (i : ℕ) → Level A i (e 0)
  root_mem : ∀ i, root i ∈ nodes i 0
  root_unique : ∀ i p, p ∈ nodes i 0 → p = root i
  successor : ∀ i n p, p ∈ nodes i n → ∀ a : A (i + 1),
    ∀ v : Level A (i + 1) (e n),
    ∃! q : Level A i (e (n + 1)),
      q ∈ nodes i (n + 1) ∧
      q.restrict (Nat.succ_le_of_lt (he (Nat.lt_succ_self n))) = Level.extend p a v
  parent : ∀ i n q, q ∈ nodes i (n + 1) →
    q.restrict (he.monotone (Nat.le_succ n)) ∈ nodes i n

namespace StrongVector

variable {A : ℕ → Type} {e : ℕ → ℕ} {he : StrictMono e}
    (S : StrongVector A e he)

noncomputable def next (i n : ℕ) (p : {p : Level A i (e n) // p ∈ S.nodes i n})
    (a : A (i + 1)) (v : Level A (i + 1) (e n)) :
    {q : Level A i (e (n + 1)) // q ∈ S.nodes i (n + 1)} :=
  ⟨Classical.choose (S.successor i n p.val p.property a v),
    (Classical.choose_spec (S.successor i n p.val p.property a v)).1.1⟩

theorem next_cone (i n : ℕ) (p : {p : Level A i (e n) // p ∈ S.nodes i n})
    (a : A (i + 1)) (v : Level A (i + 1) (e n)) :
    (S.next i n p a v).val.restrict
      (Nat.succ_le_of_lt (he (Nat.lt_succ_self n))) = Level.extend p.val a v :=
  (Classical.choose_spec (S.successor i n p.val p.property a v)).1.2

noncomputable def valuationData :
    (n i : ℕ) → Level A i n → {q : Level A i (e n) // q ∈ S.nodes i n}
  | 0, i, _ => ⟨S.root i, S.root_mem i⟩
  | n + 1, i, t =>
    S.next i n
      (valuationData n i (t.restrict (Nat.le_succ n)))
      (t.singleton (Nat.lt_succ_self n))
      (valuationData n (i + 1) (t.slice (Nat.lt_succ_self n))).val

noncomputable def valuation (n i : ℕ) (t : Level A i n) : Level A i (e n) :=
  (S.valuationData n i t).val

theorem valuation_mem (n i : ℕ) (t : Level A i n) :
    S.valuation n i t ∈ S.nodes i n :=
  (S.valuationData n i t).property

@[simp] theorem valuation_zero (i : ℕ) (t : Level A i 0) :
    S.valuation 0 i t = S.root i := rfl

theorem valuation_step_cone (n i : ℕ) (t : Level A i (n + 1)) :
    (S.valuation (n + 1) i t).restrict
        (Nat.succ_le_of_lt (he (Nat.lt_succ_self n))) =
      Level.extend
        (S.valuation n i (t.restrict (Nat.le_succ n)))
        (t.singleton (Nat.lt_succ_self n))
        (S.valuation n (i + 1) (t.slice (Nat.lt_succ_self n))) :=
  S.next_cone i n _ _ _

theorem valuation_step_restrict (n i : ℕ) (t : Level A i (n + 1)) :
    (S.valuation (n + 1) i t).restrict (he.monotone (Nat.le_succ n)) =
      S.valuation n i (t.restrict (Nat.le_succ n)) := by
  have h := congrArg (fun p : Level A i (e n + 1) =>
    p.restrict (Nat.le_succ (e n))) (S.valuation_step_cone n i t)
  simpa only [Level.restrict_restrict, Level.extend_restrict] using h

theorem valuation_step_slice (n i : ℕ) (t : Level A i (n + 1)) :
    (S.valuation (n + 1) i t).slice (he (Nat.lt_succ_self n)) =
      S.valuation n (i + 1) (t.slice (Nat.lt_succ_self n)) := by
  have h := congrArg (fun p : Level A i (e n + 1) =>
    p.slice (Nat.lt_succ_self (e n))) (S.valuation_step_cone n i t)
  simpa only [Level.slice_restrict, Level.extend_slice] using h

theorem valuation_step_singleton (n i : ℕ) (t : Level A i (n + 1)) :
    (S.valuation (n + 1) i t).singleton (he (Nat.lt_succ_self n)) =
      t.singleton (Nat.lt_succ_self n) := by
  have h := congrArg (fun p : Level A i (e n + 1) =>
    p.singleton (Nat.lt_succ_self (e n))) (S.valuation_step_cone n i t)
  simpa only [Level.singleton_restrict, Level.extend_singleton] using h

theorem valuation_restrict (n i : ℕ) (t : Level A i n)
    (m : ℕ) (hm : m ≤ n) :
    (S.valuation n i t).restrict (he.monotone hm) =
      S.valuation m i (t.restrict hm) := by
  induction n generalizing m i with
  | zero =>
    have hm0 : m = 0 := by omega
    subst m
    simp only [Level.restrict_refl]
  | succ n ih =>
    by_cases heq : m = n + 1
    · subst m
      simp only [Level.restrict_refl]
    · have hmn : m ≤ n := by omega
      calc
        (S.valuation (n + 1) i t).restrict (he.monotone hm) =
            ((S.valuation (n + 1) i t).restrict
              (he.monotone (Nat.le_succ n))).restrict (he.monotone hmn) := by
          simp only [Level.restrict_restrict]
        _ = (S.valuation n i (t.restrict (Nat.le_succ n))).restrict
            (he.monotone hmn) := by rw [S.valuation_step_restrict]
        _ = S.valuation m i (t.restrict hm) := by
          simpa only [Level.restrict_restrict] using
            ih i (t.restrict (Nat.le_succ n)) m hmn

theorem valuation_slice (n i : ℕ) (t : Level A i n)
    (m : ℕ) (hm : m < n) :
    (S.valuation n i t).slice (he hm) =
      S.valuation m (i + 1) (t.slice hm) := by
  induction n generalizing m i with
  | zero => omega
  | succ n ih =>
    by_cases heq : m = n
    · subst m
      exact S.valuation_step_slice n i t
    · have hmn : m < n := by omega
      have hs := congrArg (fun p : Level A i (e n) => p.slice (he hmn))
        (S.valuation_step_restrict n i t)
      have hi := ih i (t.restrict (Nat.le_succ n)) m hmn
      simpa only [Level.slice_restrict] using hs.trans hi

theorem valuation_singleton (n i : ℕ) (t : Level A i n)
    (m : ℕ) (hm : m < n) :
    (S.valuation n i t).singleton (he hm) = t.singleton hm := by
  have hs := S.valuation_restrict n i t (m + 1) (by omega)
  have h := congrArg (fun p : Level A i (e (m + 1)) =>
    p.singleton (he (Nat.lt_succ_self m))) hs
  rw [S.valuation_step_singleton] at h
  simpa only [Level.singleton_restrict] using h

theorem valuation_injective (n i : ℕ) : Function.Injective (S.valuation n i) := by
  induction n generalizing i with
  | zero =>
    intro s t _
    funext c
    obtain ⟨x, hx⟩ := c.property.1
    have hx' := c.property.2 hx
    simp at hx'
  | succ n ih =>
    intro s t h
    apply Level.successor_ext
    · apply ih i
      have hp := congrArg (fun p : Level A i (e (n + 1)) =>
        p.restrict (he.monotone (Nat.le_succ n))) h
      simpa only [S.valuation_step_restrict] using hp
    · have ha := congrArg (fun p : Level A i (e (n + 1)) =>
        p.singleton (he (Nat.lt_succ_self n))) h
      simpa only [S.valuation_step_singleton] using ha
    · apply ih (i + 1)
      have hv := congrArg (fun p : Level A i (e (n + 1)) =>
        p.slice (he (Nat.lt_succ_self n))) h
      simpa only [S.valuation_step_slice] using hv

/-- Distinct source successor cones are separated at the immediate ambient
level, even when the selected levels have gaps. -/
theorem valuation_immediate_injective (n i : ℕ) :
    Function.Injective (fun t : Level A i (n + 1) =>
      (S.valuation (n + 1) i t).restrict
        (Nat.succ_le_of_lt (he (Nat.lt_succ_self n)))) := by
  intro s t h
  apply Level.successor_ext
  · apply S.valuation_injective n i
    have hp := congrArg (fun p : Level A i (e n + 1) =>
      p.restrict (Nat.le_succ (e n))) h
    simpa only [Level.restrict_restrict, S.valuation_step_restrict] using hp
  · have ha := congrArg (fun p : Level A i (e n + 1) =>
      p.singleton (Nat.lt_succ_self (e n))) h
    simpa only [Level.singleton_restrict, S.valuation_step_singleton] using ha
  · apply S.valuation_injective n (i + 1)
    have hv := congrArg (fun p : Level A i (e n + 1) =>
      p.slice (Nat.lt_succ_self (e n))) h
    simpa only [Level.slice_restrict, S.valuation_step_slice] using hv

noncomputable def mapNode {i : ℕ} (t : Node A i) : Node A i :=
  ⟨e t.height, S.valuation t.height i t.table⟩

@[simp] theorem mapNode_height {i : ℕ} (t : Node A i) :
    (S.mapNode t).height = e t.height := rfl

theorem mapNode_injective (i : ℕ) : Function.Injective (S.mapNode (i := i)) := by
  intro s t h
  have hheight : e s.height = e t.height := congrArg Node.height h
  have hsource := he.injective hheight
  cases s with
  | mk n s =>
    cases t with
    | mk m t =>
      dsimp at hsource
      subst m
      have htable : HEq (S.valuation n i s) (S.valuation n i t) := by
        have table_heq : ∀ {p q : Node A i}, p = q → HEq p.table q.table := by
          intro p q hp
          cases hp
          rfl
        exact table_heq h
      have hst := S.valuation_injective n i (eq_of_heq htable)
      cases hst
      rfl

theorem mapNode_restrict {i : ℕ} (t : Node A i) (m : ℕ) (hm : m ≤ t.height) :
    (S.mapNode t).restrict (e m) (he.monotone hm) =
      S.mapNode (t.restrict m hm) := by
  cases t with
  | mk n t =>
    change Node.mk (e m) ((S.valuation n i t).restrict (he.monotone hm)) =
      Node.mk (e m) (S.valuation m i (t.restrict hm))
    rw [S.valuation_restrict]

theorem mapNode_slice {i : ℕ} (t : Node A i) (m : ℕ) (hm : m < t.height) :
    (S.mapNode t).slice (e m) (he hm) = S.mapNode (t.slice m hm) := by
  cases t with
  | mk n t =>
    change Node.mk (e m) ((S.valuation n i t).slice (he hm)) =
      Node.mk (e m) (S.valuation m (i + 1) (t.slice hm))
    rw [S.valuation_slice]

theorem mapNode_singleton {i : ℕ} (t : Node A i) (m : ℕ) (hm : m < t.height) :
    (S.mapNode t).singleton (e m) (he hm) = t.singleton m hm :=
  S.valuation_singleton t.height i t.table m hm

theorem mapNode_prefix_iff {i : ℕ} (s t : Node A i) :
    Node.Prefix (S.mapNode s) (S.mapNode t) ↔ Node.Prefix s t := by
  constructor
  · rintro ⟨hm, h⟩
    have hm' : s.height ≤ t.height := he.le_iff_le.mp hm
    refine ⟨hm', ?_⟩
    apply S.mapNode_injective i
    exact (S.mapNode_restrict t s.height hm').symm.trans h
  · rintro ⟨hm, h⟩
    refine ⟨he.monotone hm, ?_⟩
    exact (S.mapNode_restrict t s.height hm).trans (congrArg S.mapNode h)

theorem mapNode_cut_step {i : ℕ} (t : Node A i) (n : ℕ)
    (hn : n + 1 ≤ t.height) :
    (S.mapNode t).restrict (e n + 1)
        ((Nat.succ_le_of_lt (he (Nat.lt_succ_self n))).trans (he.monotone hn)) =
      (S.mapNode (t.restrict (n + 1) hn)).restrict (e n + 1)
        (Nat.succ_le_of_lt (he (Nat.lt_succ_self n))) := by
  cases t with
  | mk k t =>
    apply congrArg (fun p : Level A i (e n + 1) => (Node.mk (e n + 1) p : Node A i))
    have h := congrArg (fun p : Level A i (e (n + 1)) =>
      p.restrict (Nat.succ_le_of_lt (he (Nat.lt_succ_self n))))
      (S.valuation_restrict k i t (n + 1) hn)
    simpa only [Level.restrict_restrict, mapNode, Node.restrict] using h

theorem mapNode_meet {i : ℕ} (s t : Node A i) :
    (S.mapNode s).meet (S.mapNode t) = S.mapNode (s.meet t) := by
  classical
  by_cases hst : Node.Prefix s t
  · have hi := (S.mapNode_prefix_iff s t).mpr hst
    rw [Node.meet_eq_left_of_prefix hst, Node.meet_eq_left_of_prefix hi]
  by_cases hts : Node.Prefix t s
  · have hi := (S.mapNode_prefix_iff t s).mpr hts
    rw [Node.meet_comm s t, Node.meet_eq_left_of_prefix hts,
      Node.meet_comm (S.mapNode s) (S.mapNode t), Node.meet_eq_left_of_prefix hi]
  let c := Node.meetHeight s t
  have hcs : c + 1 ≤ s.height := by
    have h := Node.meetHeight_lt_of_incomparable hst hts
    dsimp [c]
    omega
  have hct : c + 1 ≤ t.height := by
    have h := Node.meetHeight_lt_of_incomparable hst hts
    dsimp [c]
    omega
  have hpreS := (S.mapNode_prefix_iff (s.meet t) s).mpr (Node.meet_prefix_left s t)
  have hpreT := (S.mapNode_prefix_iff (s.meet t) t).mpr (Node.meet_prefix_right s t)
  have hpre := Node.common_prefix_prefix_meet hpreS hpreT
  have hlo : e c ≤ Node.meetHeight (S.mapNode s) (S.mapNode t) :=
    Node.prefix_height_le hpre
  have hhi : Node.meetHeight (S.mapNode s) (S.mapNode t) ≤ e c := by
    by_contra hn
    have hn' : e c + 1 ≤ Node.meetHeight (S.mapNode s) (S.mapNode t) := by omega
    obtain ⟨h1, h2, hh⟩ := Node.commonHeight_downward
      (Node.commonHeight_meetHeight (S.mapNode s) (S.mapNode t)) hn'
    have hc := (S.mapNode_cut_step s c hcs).symm.trans
      (hh.trans (S.mapNode_cut_step t c hct))
    have htable :
        (S.valuation (c + 1) i (s.table.restrict hcs)).restrict
          (Nat.succ_le_of_lt (he (Nat.lt_succ_self c))) =
        (S.valuation (c + 1) i (t.table.restrict hct)).restrict
          (Nat.succ_le_of_lt (he (Nat.lt_succ_self c))) :=
      Node.mk_injective (e c + 1) hc
    have hsource := S.valuation_immediate_injective c i htable
    have hsourcNodes : s.restrict (c + 1) hcs = t.restrict (c + 1) hct :=
      congrArg (fun u : Level A i (c + 1) => (Node.mk (c + 1) u : Node A i)) hsource
    have hbad := Node.commonHeight_le_meetHeight ⟨hcs, hct, hsourcNodes⟩
    change c + 1 ≤ c at hbad
    omega
  exact (Node.prefix_eq_of_height_eq hpre (Nat.le_antisymm hlo hhi)).symm

end StrongVector

end RelationalRamsey632.Source
