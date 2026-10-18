import RelationalRamsey632.Source.Valuations

/-! Genuine finite vectors and valuations on the exact triangular domains.
No infinite vector extension is assumed to exist. -/

namespace RelationalRamsey632.Source

structure FiniteStrongVector (A : ℕ → Type) (e : ℕ → ℕ) (he : StrictMono e) (h : ℕ) where
  nodes : (i n : ℕ) → Set (Level A i (e n))
  root : ∀ i, i < h → Level A i (e 0)
  root_mem : ∀ i (hi : i < h), root i hi ∈ nodes i 0
  root_unique : ∀ i (hi : i < h) p, p ∈ nodes i 0 → p = root i hi
  successor : ∀ i, i < h → ∀ n, n + 1 < h →
    ∀ p, p ∈ nodes i n → ∀ a : A (i + 1), ∀ v : Level A (i + 1) (e n),
      ∃! q : Level A i (e (n + 1)), q ∈ nodes i (n + 1) ∧
        q.restrict (Nat.succ_le_of_lt (he (Nat.lt_succ_self n))) = Level.extend p a v
  parent : ∀ i, i < h → ∀ n, n + 1 < h → ∀ q, q ∈ nodes i (n + 1) →
    q.restrict (he.monotone (Nat.le_succ n)) ∈ nodes i n

/-- The genuine finite data seen by a finite vector coloring. Inactive
coordinates, inactive levels, and the tail of the total level map are absent. -/
abbrev FiniteVectorCore (A : ℕ → Type) (h : ℕ) :=
  (i : Fin h) → Fin h → Set (Node A i.val)

namespace StrongVector

variable {A : ℕ → Type} {e : ℕ → ℕ} {he : StrictMono e}

def finitePrefix (S : StrongVector A e he) (h : ℕ) : FiniteStrongVector A e he h where
  nodes := S.nodes
  root i _ := S.root i
  root_mem i _ := S.root_mem i
  root_unique i _ := S.root_unique i
  successor i _ n _ := S.successor i n
  parent i _ n _ := S.parent i n

end StrongVector

namespace FiniteStrongVector

variable {A : ℕ → Type} {e : ℕ → ℕ} {he : StrictMono e} {h : ℕ}
    (V : FiniteStrongVector A e he h)

def core : FiniteVectorCore A h := fun i n =>
  {t | ∃ p ∈ V.nodes i.val n.val, t = Node.mk (e n.val) p}

theorem mem_core (i n : Fin h) (p : Level A i.val (e n.val))
    (hp : p ∈ V.nodes i.val n.val) : Node.mk (e n.val) p ∈ V.core i n :=
  ⟨p, hp, rfl⟩

theorem core_height (i n : Fin h) {t : Node A i.val} (ht : t ∈ V.core i n) :
    t.height = e n.val := by
  obtain ⟨p, _, rfl⟩ := ht
  rfl

noncomputable def next (i : ℕ) (hi : i < h) (n : ℕ) (hn : n + 1 < h)
    (p : {p : Level A i (e n) // p ∈ V.nodes i n})
    (a : A (i + 1)) (v : Level A (i + 1) (e n)) :
    {q : Level A i (e (n + 1)) // q ∈ V.nodes i (n + 1)} :=
  ⟨Classical.choose (V.successor i hi n hn p.val p.property a v),
    (Classical.choose_spec (V.successor i hi n hn p.val p.property a v)).1.1⟩

theorem next_cone (i : ℕ) (hi : i < h) (n : ℕ) (hn : n + 1 < h)
    (p : {p : Level A i (e n) // p ∈ V.nodes i n})
    (a : A (i + 1)) (v : Level A (i + 1) (e n)) :
    (V.next i hi n hn p a v).val.restrict
      (Nat.succ_le_of_lt (he (Nat.lt_succ_self n))) = Level.extend p.val a v :=
  (Classical.choose_spec (V.successor i hi n hn p.val p.property a v)).1.2

noncomputable def valuationData :
    (n i : ℕ) → i + n < h → Level A i n →
      {q : Level A i (e n) // q ∈ V.nodes i n}
  | 0, i, hd, _ => ⟨V.root i (by omega), V.root_mem i (by omega)⟩
  | n + 1, i, hd, t =>
    V.next i (by omega) n (by omega)
      (valuationData n i (by omega) (t.restrict (Nat.le_succ n)))
      (t.singleton (Nat.lt_succ_self n))
      (valuationData n (i + 1) (by omega) (t.slice (Nat.lt_succ_self n))).val

noncomputable def valuation (n i : ℕ) (hd : i + n < h) (t : Level A i n) :
    Level A i (e n) := (V.valuationData n i hd t).val

theorem valuation_mem (n i : ℕ) (hd : i + n < h) (t : Level A i n) :
    V.valuation n i hd t ∈ V.nodes i n := (V.valuationData n i hd t).property

@[simp] theorem valuation_zero (i : ℕ) (hd : i + 0 < h) (t : Level A i 0) :
    V.valuation 0 i hd t = V.root i hd := rfl

theorem valuation_step_cone (n i : ℕ) (hd : i + (n + 1) < h)
    (t : Level A i (n + 1)) :
    (V.valuation (n + 1) i hd t).restrict
      (Nat.succ_le_of_lt (he (Nat.lt_succ_self n))) =
      Level.extend (V.valuation n i (by omega) (t.restrict (Nat.le_succ n)))
        (t.singleton (Nat.lt_succ_self n))
        (V.valuation n (i + 1) (by omega) (t.slice (Nat.lt_succ_self n))) :=
  V.next_cone i (by omega) n (by omega) _ _ _

theorem valuation_step_restrict (n i : ℕ) (hd : i + (n + 1) < h)
    (t : Level A i (n + 1)) :
    (V.valuation (n + 1) i hd t).restrict (he.monotone (Nat.le_succ n)) =
      V.valuation n i (by omega) (t.restrict (Nat.le_succ n)) := by
  have hh := congrArg (fun p : Level A i (e n + 1) => p.restrict (Nat.le_succ (e n)))
    (V.valuation_step_cone n i hd t)
  simpa only [Level.restrict_restrict, Level.extend_restrict] using hh

theorem valuation_step_slice (n i : ℕ) (hd : i + (n + 1) < h)
    (t : Level A i (n + 1)) :
    (V.valuation (n + 1) i hd t).slice (he (Nat.lt_succ_self n)) =
      V.valuation n (i + 1) (by omega) (t.slice (Nat.lt_succ_self n)) := by
  have hh := congrArg (fun p : Level A i (e n + 1) => p.slice (Nat.lt_succ_self (e n)))
    (V.valuation_step_cone n i hd t)
  simpa only [Level.slice_restrict, Level.extend_slice] using hh

theorem valuation_step_singleton (n i : ℕ) (hd : i + (n + 1) < h)
    (t : Level A i (n + 1)) :
    (V.valuation (n + 1) i hd t).singleton (he (Nat.lt_succ_self n))
      = t.singleton (Nat.lt_succ_self n) := by
  have hh := congrArg (fun p : Level A i (e n + 1) => p.singleton (Nat.lt_succ_self (e n)))
    (V.valuation_step_cone n i hd t)
  simpa only [Level.singleton_restrict, Level.extend_singleton] using hh

theorem valuation_restrict (n i : ℕ) (hd : i + n < h) (t : Level A i n)
    (m : ℕ) (hm : m ≤ n) :
    (V.valuation n i hd t).restrict (he.monotone hm)
      = V.valuation m i (by omega) (t.restrict hm) := by
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
        (V.valuation (n + 1) i hd t).restrict (he.monotone hm) =
            ((V.valuation (n + 1) i hd t).restrict
              (he.monotone (Nat.le_succ n))).restrict (he.monotone hmn) := by
          simp only [Level.restrict_restrict]
        _ = (V.valuation n i (by omega) (t.restrict (Nat.le_succ n))).restrict
            (he.monotone hmn) := by rw [V.valuation_step_restrict]
        _ = V.valuation m i (by omega) (t.restrict hm) := by
          simpa only [Level.restrict_restrict] using
            ih i (by omega) (t.restrict (Nat.le_succ n)) m hmn

theorem valuation_slice (n i : ℕ) (hd : i + n < h) (t : Level A i n)
    (m : ℕ) (hm : m < n) :
    (V.valuation n i hd t).slice (he hm)
      = V.valuation m (i + 1) (by omega) (t.slice hm) := by
  induction n generalizing m i with
  | zero => omega
  | succ n ih =>
    by_cases heq : m = n
    · subst m
      exact V.valuation_step_slice n i hd t
    · have hmn : m < n := by omega
      have hs := congrArg (fun p : Level A i (e n) => p.slice (he hmn))
        (V.valuation_step_restrict n i hd t)
      have hi := ih i (by omega) (t.restrict (Nat.le_succ n)) m hmn
      simpa only [Level.slice_restrict] using hs.trans hi

theorem valuation_singleton (n i : ℕ) (hd : i + n < h) (t : Level A i n)
    (m : ℕ) (hm : m < n) :
    (V.valuation n i hd t).singleton (he hm) = t.singleton hm := by
  have hs := V.valuation_restrict n i hd t (m + 1) (by omega)
  have hh := congrArg (fun p : Level A i (e (m + 1)) =>
    p.singleton (he (Nat.lt_succ_self m))) hs
  rw [V.valuation_step_singleton] at hh
  simpa only [Level.singleton_restrict] using hh

theorem valuation_injective (n i : ℕ) (hd : i + n < h) :
    Function.Injective (V.valuation n i hd) := by
  induction n generalizing i with
  | zero =>
    intro s t _
    funext c
    obtain ⟨x, hx⟩ := c.property.1
    have hx' := c.property.2 hx
    simp at hx'
  | succ n ih =>
    intro s t hs
    apply Level.successor_ext
    · apply ih i (by omega)
      have hp := congrArg (fun p : Level A i (e (n + 1)) =>
        p.restrict (he.monotone (Nat.le_succ n))) hs
      simpa only [V.valuation_step_restrict] using hp
    · have ha := congrArg (fun p : Level A i (e (n + 1)) =>
        p.singleton (he (Nat.lt_succ_self n))) hs
      simpa only [V.valuation_step_singleton] using ha
    · apply ih (i + 1) (by omega)
      have hv := congrArg (fun p : Level A i (e (n + 1)) =>
        p.slice (he (Nat.lt_succ_self n))) hs
      simpa only [V.valuation_step_slice] using hv

noncomputable def mapNode {i : ℕ} (t : Node A i) (hd : i + t.height < h) : Node A i :=
  ⟨e t.height, V.valuation t.height i hd t.table⟩

@[simp] theorem mapNode_height {i : ℕ} (t : Node A i) (hd : i + t.height < h) :
    (V.mapNode t hd).height = e t.height := rfl

theorem mapNode_restrict {i : ℕ} (t : Node A i) (hd : i + t.height < h)
    (m : ℕ) (hm : m ≤ t.height) :
    (V.mapNode t hd).restrict (e m) (he.monotone hm)
      = V.mapNode (t.restrict m hm) (by dsimp; omega) := by
  cases t with
  | mk n t =>
    change Node.mk (e m) ((V.valuation n i hd t).restrict (he.monotone hm)) = _
    rw [V.valuation_restrict]
    rfl

theorem mapNode_slice {i : ℕ} (t : Node A i) (hd : i + t.height < h)
    (m : ℕ) (hm : m < t.height) :
    (V.mapNode t hd).slice (e m) (he hm)
      = V.mapNode (t.slice m hm) (by dsimp; omega) := by
  cases t with
  | mk n t =>
    change Node.mk (e m) ((V.valuation n i hd t).slice (he hm)) = _
    rw [V.valuation_slice]
    rfl

theorem mapNode_singleton {i : ℕ} (t : Node A i) (hd : i + t.height < h)
    (m : ℕ) (hm : m < t.height) :
    (V.mapNode t hd).singleton (e m) (he hm) = t.singleton m hm :=
  V.valuation_singleton t.height i hd t.table m hm

theorem valuation_immediate_injective (n i : ℕ) (hd : i + (n + 1) < h) :
    Function.Injective (fun t : Level A i (n + 1) =>
      (V.valuation (n + 1) i hd t).restrict
        (Nat.succ_le_of_lt (he (Nat.lt_succ_self n)))) := by
  intro s t hs
  apply Level.successor_ext
  · apply V.valuation_injective n i (by omega)
    have hp := congrArg (fun p : Level A i (e n + 1) =>
      p.restrict (Nat.le_succ (e n))) hs
    simpa only [Level.restrict_restrict, V.valuation_step_restrict] using hp
  · have ha := congrArg (fun p : Level A i (e n + 1) =>
      p.singleton (Nat.lt_succ_self (e n))) hs
    simpa only [Level.singleton_restrict, V.valuation_step_singleton] using ha
  · apply V.valuation_injective n (i + 1) (by omega)
    have hv := congrArg (fun p : Level A i (e n + 1) =>
      p.slice (Nat.lt_succ_self (e n))) hs
    simpa only [Level.slice_restrict, V.valuation_step_slice] using hv

theorem mapNode_injective {i : ℕ} (s t : Node A i)
    (hs : i + s.height < h) (ht : i + t.height < h)
    (heq : V.mapNode s hs = V.mapNode t ht) : s = t := by
  have hheight : e s.height = e t.height := congrArg Node.height heq
  have hsource := he.injective hheight
  cases s with
  | mk n s =>
    cases t with
    | mk m t =>
      dsimp at hsource
      subst m
      have htable : HEq (V.valuation n i hs s) (V.valuation n i ht t) := by
        have table_heq : ∀ {p q : Node A i}, p = q → HEq p.table q.table := by
          intro p q hp
          cases hp
          rfl
        exact table_heq heq
      have hst := V.valuation_injective n i hs (eq_of_heq htable)
      cases hst
      rfl

theorem mapNode_congr {i : ℕ} (s t : Node A i)
    (hs : i + s.height < h) (ht : i + t.height < h) (heq : s = t) :
    V.mapNode s hs = V.mapNode t ht := by
  cases heq
  rfl

theorem mapNode_prefix_iff {i : ℕ} (s t : Node A i)
    (hs : i + s.height < h) (ht : i + t.height < h) :
    Node.Prefix (V.mapNode s hs) (V.mapNode t ht) ↔ Node.Prefix s t := by
  constructor
  · rintro ⟨hm, hh⟩
    have hm' : s.height ≤ t.height := he.le_iff_le.mp hm
    refine ⟨hm', ?_⟩
    apply V.mapNode_injective _ _ _ hs
    exact (V.mapNode_restrict t ht s.height hm').symm.trans hh
  · rintro ⟨hm, hh⟩
    refine ⟨he.monotone hm, ?_⟩
    have hmap : V.mapNode (t.restrict s.height hm) (by dsimp; omega) = V.mapNode s hs := by
      exact V.mapNode_congr _ _ _ _ hh
    exact (V.mapNode_restrict t ht s.height hm).trans hmap

theorem mapNode_cut_step {i : ℕ} (t : Node A i) (hd : i + t.height < h)
    (n : ℕ) (hn : n + 1 ≤ t.height) :
    (V.mapNode t hd).restrict (e n + 1)
        ((Nat.succ_le_of_lt (he (Nat.lt_succ_self n))).trans (he.monotone hn)) =
      (V.mapNode (t.restrict (n + 1) hn) (by dsimp; omega)).restrict (e n + 1)
        (Nat.succ_le_of_lt (he (Nat.lt_succ_self n))) := by
  cases t with
  | mk k t =>
    apply congrArg (fun p : Level A i (e n + 1) => (Node.mk (e n + 1) p : Node A i))
    have hh := congrArg (fun p : Level A i (e (n + 1)) =>
      p.restrict (Nat.succ_le_of_lt (he (Nat.lt_succ_self n))))
      (V.valuation_restrict k i hd t (n + 1) hn)
    simpa only [Level.restrict_restrict, mapNode, Node.restrict] using hh

theorem mapNode_meet {i : ℕ} (s t : Node A i)
    (hs : i + s.height < h) (ht : i + t.height < h) :
    (V.mapNode s hs).meet (V.mapNode t ht)
      = V.mapNode (s.meet t) (by have hh := Node.meetHeight_le_left s t; dsimp; omega) := by
  classical
  by_cases hst : Node.Prefix s t
  · have hi := (V.mapNode_prefix_iff s t hs ht).mpr hst
    rw [Node.meet_eq_left_of_prefix hi]
    have hh := Node.meet_eq_left_of_prefix hst
    exact (V.mapNode_congr _ _ _ _ hh).symm
  by_cases hts : Node.Prefix t s
  · have hi := (V.mapNode_prefix_iff t s ht hs).mpr hts
    rw [Node.meet_comm (V.mapNode s hs) (V.mapNode t ht), Node.meet_eq_left_of_prefix hi]
    have hh : s.meet t = t := (Node.meet_comm s t).trans (Node.meet_eq_left_of_prefix hts)
    exact (V.mapNode_congr _ _ _ _ hh).symm
  let c := Node.meetHeight s t
  have hcs : c + 1 ≤ s.height := by
    have hh := Node.meetHeight_lt_of_incomparable hst hts
    dsimp [c]
    omega
  have hct : c + 1 ≤ t.height := by
    have hh := Node.meetHeight_lt_of_incomparable hst hts
    dsimp [c]
    omega
  have hdmeet : i + (s.meet t).height < h := by
    have hh := Node.meetHeight_le_left s t
    dsimp
    omega
  have hpreS := (V.mapNode_prefix_iff (s.meet t) s hdmeet hs).mpr (Node.meet_prefix_left s t)
  have hpreT := (V.mapNode_prefix_iff (s.meet t) t hdmeet ht).mpr (Node.meet_prefix_right s t)
  have hpre := Node.common_prefix_prefix_meet hpreS hpreT
  have hlo : e c ≤ Node.meetHeight (V.mapNode s hs) (V.mapNode t ht) :=
    Node.prefix_height_le hpre
  have hhi : Node.meetHeight (V.mapNode s hs) (V.mapNode t ht) ≤ e c := by
    by_contra hn
    have hn' : e c + 1 ≤ Node.meetHeight (V.mapNode s hs) (V.mapNode t ht) := by omega
    obtain ⟨_, _, hh⟩ := Node.commonHeight_downward
      (Node.commonHeight_meetHeight (V.mapNode s hs) (V.mapNode t ht)) hn'
    have hc := (V.mapNode_cut_step s hs c hcs).symm.trans
      (hh.trans (V.mapNode_cut_step t ht c hct))
    have htable :
        (V.valuation (c + 1) i (by omega) (s.table.restrict hcs)).restrict
          (Nat.succ_le_of_lt (he (Nat.lt_succ_self c))) =
        (V.valuation (c + 1) i (by omega) (t.table.restrict hct)).restrict
          (Nat.succ_le_of_lt (he (Nat.lt_succ_self c))) :=
      Node.mk_injective (e c + 1) hc
    have hsource := V.valuation_immediate_injective c i (by omega) htable
    have hsourcNodes : s.restrict (c + 1) hcs = t.restrict (c + 1) hct :=
      congrArg (fun u : Level A i (c + 1) => (Node.mk (c + 1) u : Node A i)) hsource
    have hbad := Node.commonHeight_le_meetHeight ⟨hcs, hct, hsourcNodes⟩
    change c + 1 ≤ c at hbad
    omega
  exact (Node.prefix_eq_of_height_eq hpre (Nat.le_antisymm hlo hhi)).symm

end FiniteStrongVector

end RelationalRamsey632.Source
