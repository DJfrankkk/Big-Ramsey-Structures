import RelationalRamsey632.Source.FiniteNormalForms

/-! Finite valuation images depend only on the active finite vector core,
including when ambient level maps have different irrelevant tails. -/

namespace RelationalRamsey632.Source

namespace Node

variable {A : ℕ → Type} {i : ℕ}

theorem restrict_height_congr (t : Node A i) {m n : ℕ} (h : m = n)
    (hm : m ≤ t.height) (hn : n ≤ t.height) :
    t.restrict m hm = t.restrict n hn := by cases h; rfl

theorem slice_height_congr (t : Node A i) {m n : ℕ} (h : m = n)
    (hm : m < t.height) (hn : n < t.height) :
    t.slice m hm = t.slice n hn := by cases h; rfl

theorem singleton_height_congr (t : Node A i) {m n : ℕ} (h : m = n)
    (hm : m < t.height) (hn : n < t.height) :
    t.singleton m hm = t.singleton n hn := by cases h; rfl

theorem step_restriction_eq (s t : Node A i) (m : ℕ)
    (hs : m < s.height) (ht : m < t.height)
    (hp : s.restrict m hs.le = t.restrict m ht.le)
    (ha : s.singleton m hs = t.singleton m ht)
    (hv : s.slice m hs = t.slice m ht) :
    s.restrict (m + 1) (Nat.succ_le_of_lt hs) =
      t.restrict (m + 1) (Nat.succ_le_of_lt ht) := by
  cases s with
  | mk ns s =>
    cases t with
    | mk nt t =>
      apply congrArg (fun p : Level A i (m + 1) => (Node.mk (m + 1) p : Node A i))
      apply Level.successor_ext
      · simpa only [Level.restrict_restrict] using Node.mk_injective m hp
      · simpa only [Level.singleton_restrict, singleton] using ha
      · simpa only [Level.slice_restrict] using Node.mk_injective m hv

end Node

namespace Level

theorem reconstruct_step {A : ℕ → Type} {i n m : ℕ}
    (t : Level A i n) (hm : m < n) :
    extend (t.restrict hm.le) (t.singleton hm) (t.slice hm) =
      t.restrict (Nat.succ_le_of_lt hm) := by
  apply successor_ext
  · simp only [extend_restrict, restrict_restrict]
  · simp only [extend_singleton, singleton_restrict]
  · simp only [extend_slice, slice_restrict]

end Level

namespace FiniteStrongVector

variable {A : ℕ → Type} {e f : ℕ → ℕ} {he : StrictMono e} {hf : StrictMono f} {h : ℕ}
    (V : FiniteStrongVector A e he h)

theorem core_root_unique (i : ℕ) (hi : i < h)
    {s t : Node A i} (hs : s ∈ V.core ⟨i, hi⟩ ⟨0, by omega⟩)
    (ht : t ∈ V.core ⟨i, hi⟩ ⟨0, by omega⟩) : s = t := by
  obtain ⟨sp, hsp, rfl⟩ := hs
  obtain ⟨tp, htp, rfl⟩ := ht
  exact congrArg (fun p : Level A i (e 0) => (Node.mk (e 0) p : Node A i))
    ((V.root_unique i hi sp hsp).trans (V.root_unique i hi tp htp).symm)

theorem core_step_unique (i n : ℕ) (hi : i < h) (hn : n + 1 < h)
    {s t : Node A i} (hs : s ∈ V.core ⟨i, hi⟩ ⟨n + 1, hn⟩)
    (ht : t ∈ V.core ⟨i, hi⟩ ⟨n + 1, hn⟩)
    (hcut : s.restrict (e n + 1) (by
      have hheight := V.core_height ⟨i, hi⟩ ⟨n + 1, hn⟩ hs
      exact (Nat.succ_le_of_lt (he (Nat.lt_succ_self n))).trans hheight.ge) =
      t.restrict (e n + 1) (by
        have hheight := V.core_height ⟨i, hi⟩ ⟨n + 1, hn⟩ ht
        exact (Nat.succ_le_of_lt (he (Nat.lt_succ_self n))).trans hheight.ge)) :
    s = t := by
  obtain ⟨sp, hsp, rfl⟩ := hs
  obtain ⟨tp, htp, rfl⟩ := ht
  let p := sp.restrict (he.monotone (Nat.le_succ n))
  have hp : p ∈ V.nodes i n := V.parent i hi n hn sp hsp
  let a := sp.singleton (he (Nat.lt_succ_self n))
  let v := sp.slice (he (Nat.lt_succ_self n))
  have hscone : sp.restrict (Nat.succ_le_of_lt (he (Nat.lt_succ_self n))) =
      Level.extend p a v := (Level.reconstruct_step sp (he (Nat.lt_succ_self n))).symm
  have htcone : tp.restrict (Nat.succ_le_of_lt (he (Nat.lt_succ_self n))) =
      Level.extend p a v :=
    (Node.mk_injective (e n + 1) hcut).symm.trans hscone
  obtain ⟨q, _, hq⟩ := V.successor i hi n hn p hp a v
  exact congrArg (fun p : Level A i (e (n + 1)) =>
    (Node.mk (e (n + 1)) p : Node A i))
    ((hq sp ⟨hsp, hscone⟩).trans (hq tp ⟨htp, htcone⟩).symm)

theorem mapNode_mem_core {i : ℕ} (t : Node A i) (hd : i + t.height < h) :
    V.mapNode t hd ∈ V.core ⟨i, by omega⟩ ⟨t.height, by omega⟩ :=
  V.mem_core _ _ _ (V.valuation_mem t.height i hd t.table)

theorem mapNode_eq_of_core (W : FiniteStrongVector A f hf h) (hcore : V.core = W.core)
    (n i : ℕ) (hd : i + n < h) (t : Level A i n) :
    V.mapNode (Node.mk n t) hd = W.mapNode (Node.mk n t) hd := by
  induction n generalizing i with
  | zero =>
    apply V.core_root_unique i (by omega)
    · exact V.mapNode_mem_core (Node.mk 0 t) hd
    · rw [hcore]
      exact W.mapNode_mem_core (Node.mk 0 t) hd
  | succ n ih =>
    let sn : Node A i := ⟨n + 1, t⟩
    let p := sn.restrict n (Nat.le_succ n)
    let v := sn.slice n (Nat.lt_succ_self n)
    have hp := ih i (by omega) (t.restrict (Nat.le_succ n))
    have hv := ih (i + 1) (by omega) (t.slice (Nat.lt_succ_self n))
    have hlevel : e n = f n := congrArg Node.height hp
    let s := V.mapNode sn hd
    let r := W.mapNode sn hd
    have hs : e n < s.height := he (Nat.lt_succ_self n)
    have hr : e n < r.height := hlevel.symm ▸ hf (Nat.lt_succ_self n)
    have hp' : s.restrict (e n) hs.le = r.restrict (e n) hr.le := by
      calc
        _ = V.mapNode p (by dsimp [p]; omega) := V.mapNode_restrict sn hd n (Nat.le_succ n)
        _ = W.mapNode p (by dsimp [p]; omega) := hp
        _ = r.restrict (f n) (hf.monotone (Nat.le_succ n)) :=
          (W.mapNode_restrict sn hd n (Nat.le_succ n)).symm
        _ = r.restrict (e n) hr.le :=
          Node.restrict_height_congr r hlevel.symm _ _
    have ha' : s.singleton (e n) hs = r.singleton (e n) hr := by
      calc
        _ = sn.singleton n (Nat.lt_succ_self n) := V.mapNode_singleton sn hd n (Nat.lt_succ_self n)
        _ = r.singleton (f n) (hf (Nat.lt_succ_self n)) :=
          (W.mapNode_singleton sn hd n (Nat.lt_succ_self n)).symm
        _ = r.singleton (e n) hr := Node.singleton_height_congr r hlevel.symm _ _
    have hv' : s.slice (e n) hs = r.slice (e n) hr := by
      calc
        _ = V.mapNode v (by dsimp [v]; omega) := V.mapNode_slice sn hd n (Nat.lt_succ_self n)
        _ = W.mapNode v (by dsimp [v]; omega) := hv
        _ = r.slice (f n) (hf (Nat.lt_succ_self n)) :=
          (W.mapNode_slice sn hd n (Nat.lt_succ_self n)).symm
        _ = r.slice (e n) hr := Node.slice_height_congr r hlevel.symm _ _
    apply V.core_step_unique i n (by omega) (by omega) (s := s) (t := r)
    · exact Node.step_restriction_eq s r (e n) hs hr hp' ha' hv'
    · exact V.mapNode_mem_core sn hd
    · rw [hcore]
      exact W.mapNode_mem_core sn hd

theorem mapNodeDefault_eq_of_core (W : FiniteStrongVector A f hf h)
    (hcore : V.core = W.core) {i : ℕ} (t : Node A i) (hd : i + t.height < h) :
    V.mapNodeDefault t = W.mapNodeDefault t := by
  rw [V.mapNodeDefault_active t hd, W.mapNodeDefault_active t hd]
  cases t with
  | mk n t => exact V.mapNode_eq_of_core W hcore n i hd t

theorem mapVertices_eq_of_core (W : FiniteStrongVector A f hf h)
    (hcore : V.core = W.core) {U : Type} (v : U × Node A 0) (hv : v.2.height < h) :
    V.mapVertices v = W.mapVertices v := by
  apply Prod.ext
  · rfl
  · exact V.mapNodeDefault_eq_of_core W hcore v.2 (by simpa using hv)

end FiniteStrongVector

end RelationalRamsey632.Source
