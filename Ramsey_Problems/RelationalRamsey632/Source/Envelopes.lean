import RelationalRamsey632.Source.RelativeCompletion

/-! Exact marked envelopes. Prescribed cone uniqueness is proved from
actual meet closure and the absence of selected levels between consecutive
heights; it is not an oracle premise of the envelope theorem. -/

namespace RelationalRamsey632.Source

def sourceNodes {A : ℕ → Type} {e : ℕ → ℕ} {he : StrictMono e}
    (S : StrongVector A e he) (i : ℕ) : Set (Node A i) :=
  {t | ∃ n, ∃ p : Level A i (e n), p ∈ S.nodes i n ∧ Node.mk (e n) p = t}

structure SelectedDiagram {A : ℕ → Type} {e : ℕ → ℕ} {he : StrictMono e}
    (S : StrongVector A e he) (l : ℕ → ℕ) (hl : StrictMono l) (h : ℕ) where
  nodes : (i : ℕ) → Set (Node A i)
  source : ∀ i, nodes i ⊆ sourceNodes S i
  heights : ∀ i t, t ∈ nodes i → ∃ n, n < h ∧ t.height = e (l n)
  meet : ∀ i s, s ∈ nodes i → ∀ t, t ∈ nodes i → s.meet t ∈ nodes i
  restrict : ∀ i t, t ∈ nodes i → ∀ n, n < h → ∀ hn : e (l n) ≤ t.height,
    t.restrict (e (l n)) hn ∈ nodes i
  slice : ∀ i t, t ∈ nodes i → ∀ n, n < h → ∀ hn : e (l n) < t.height,
    t.slice (e (l n)) hn ∈ nodes (i + 1)

namespace SelectedDiagram

variable {A : ℕ → Type} {e : ℕ → ℕ} {he : StrictMono e}
    {S : StrongVector A e he} {l : ℕ → ℕ} {hl : StrictMono l} {h : ℕ}
    (D : SelectedDiagram S l hl h)

def prescribed : PrescribedLevels S l hl h where
  nodes i n := {p | n < h ∧ Node.mk (e (l n)) p ∈ D.nodes i}
  source i n p hp := by
    obtain ⟨k, q, hq, hnode⟩ := D.source i hp.2
    have heq : e k = e (l n) := congrArg Node.height hnode
    have hk := he.injective heq
    subst k
    have htable : q = p := Node.mk_injective (e (l n)) hnode
    exact htable ▸ hq
  root_unique i _ p hp q hq := by
    by_contra hpq
    let s : Node A i := Node.mk (e (l 0)) p
    let t : Node A i := Node.mk (e (l 0)) q
    have hst : ¬ Node.Prefix s t := by
      intro hh
      have hn := Node.prefix_eq_of_height_eq hh rfl
      exact hpq (Node.mk_injective _ hn)
    have hts : ¬ Node.Prefix t s := by
      intro hh
      have hn := Node.prefix_eq_of_height_eq hh rfl
      exact hpq (Node.mk_injective _ hn.symm)
    have hlow := Node.meetHeight_lt_of_incomparable hst hts
    have hm := D.meet i s hp.2 t hq.2
    obtain ⟨n, _, hn⟩ := D.heights i (s.meet t) hm
    have hle : e (l 0) ≤ e (l n) := (he.comp hl).monotone (Nat.zero_le n)
    change Node.meetHeight s t = e (l n) at hn
    change Node.meetHeight s t < min (e (l 0)) (e (l 0)) at hlow
    rw [min_self] at hlow
    omega
  parent i _ n hn q hq := by
    refine ⟨Nat.lt_of_succ_lt hn, ?_⟩
    exact D.restrict i (Node.mk (e (l (n + 1))) q) hq.2 n (Nat.lt_of_succ_lt hn)
      (he.monotone (hl.monotone (Nat.le_succ n)))
  cone_unique i _ n _ p hp q hq hcone := by
    by_contra hpq
    let s : Node A i := Node.mk (e (l (n + 1))) p
    let t : Node A i := Node.mk (e (l (n + 1))) q
    have hst : ¬ Node.Prefix s t := by
      intro hh
      exact hpq (Node.mk_injective _ (Node.prefix_eq_of_height_eq hh rfl))
    have hts : ¬ Node.Prefix t s := by
      intro hh
      exact hpq (Node.mk_injective _ (Node.prefix_eq_of_height_eq hh rfl).symm)
    have hlo : e (l n) + 1 ≤ Node.meetHeight s t := by
      apply Node.commonHeight_le_meetHeight
      exact ⟨Nat.succ_le_of_lt (he (hl (Nat.lt_succ_self n))),
        Nat.succ_le_of_lt (he (hl (Nat.lt_succ_self n))),
        congrArg (fun z => (Node.mk (e (l n) + 1) z : Node A i)) hcone⟩
    have hhi := Node.meetHeight_lt_of_incomparable hst hts
    have hm := D.meet i s hp.2 t hq.2
    obtain ⟨m, _, hmeq⟩ := D.heights i (s.meet t) hm
    change Node.meetHeight s t = e (l m) at hmeq
    have hlower : e (l n) < e (l m) := by omega
    have hupper : e (l m) < e (l (n + 1)) := by
      change Node.meetHeight s t < min (e (l (n + 1))) (e (l (n + 1))) at hhi
      rw [min_self] at hhi
      omega
    have hnm : n < m := (he.comp hl).lt_iff_lt.mp hlower
    have hmn : m < n + 1 := (he.comp hl).lt_iff_lt.mp hupper
    omega

variable [∀ j, Fintype (A j)] [∀ j, Nonempty (A j)]

noncomputable def envelope : FiniteStrongVector A (e ∘ l) (he.comp hl) h :=
  D.prescribed.completion

theorem envelope_contains (i n : ℕ) (hi : i < h) (hn : n < h)
    (p : Level A i (e (l n))) (hp : Node.mk (e (l n)) p ∈ D.nodes i) :
    p ∈ D.envelope.nodes i n := D.prescribed.completion_contains i hi n hn ⟨hn, hp⟩

theorem envelope_relative (i n : ℕ) : D.envelope.nodes i n ⊆ S.nodes i (l n) :=
  D.prescribed.completion_relative i n

theorem envelope_finite_levels (i n : ℕ) : (D.envelope.nodes i n).Finite :=
  D.prescribed.completion_finite_levels i n

/-- Each retained node is recovered at its exact sampled position. This
proves marked equality, rather than only containment in the chosen trees. -/
theorem envelope_marked (n i : ℕ) (hd : i + n < h)
    (p : Level A i (e (l n))) (hp : Node.mk (e (l n)) p ∈ D.nodes i) :
    D.envelope.valuation n i hd (p.sample (e ∘ l) (he.comp hl)) = p := by
  induction n generalizing i with
  | zero =>
    rw [FiniteStrongVector.valuation_zero]
    exact (D.envelope.root_unique i (by omega) p
      (D.envelope_contains i 0 (by omega) (by omega) p hp)).symm
  | succ n ih =>
    let q := p.restrict (he.monotone (hl.monotone (Nat.le_succ n)))
    let v := p.slice (he (hl (Nat.lt_succ_self n)))
    let a := p.singleton (he (hl (Nat.lt_succ_self n)))
    have hq : Node.mk (e (l n)) q ∈ D.nodes i :=
      D.restrict i (Node.mk (e (l (n + 1))) p) hp n (by omega)
        (he.monotone (hl.monotone (Nat.le_succ n)))
    have hv : Node.mk (e (l n)) v ∈ D.nodes (i + 1) :=
      D.slice i (Node.mk (e (l (n + 1))) p) hp n (by omega)
        (he (hl (Nat.lt_succ_self n)))
    have hqval := ih i (by omega) q hq
    have hvval := ih (i + 1) (by omega) v hv
    have hcone := D.envelope.valuation_step_cone n i hd
      (p.sample (e ∘ l) (he.comp hl))
    rw [Level.sample_restrict, Level.sample_singleton, Level.sample_slice] at hcone
    have hcone' : (D.envelope.valuation (n + 1) i hd (p.sample (e ∘ l) (he.comp hl))).restrict
        (Nat.succ_le_of_lt (he (hl (Nat.lt_succ_self n)))) = Level.extend q a v :=
      hcone.trans (congrArg₂ (fun q v => Level.extend q a v) hqval hvval)
    have hpcone : p.restrict (Nat.succ_le_of_lt (he (hl (Nat.lt_succ_self n))))
        = Level.extend q a v := by
      apply Level.successor_ext
      · simp only [Level.restrict_restrict, Level.extend_restrict]
        rfl
      · simp only [Level.singleton_restrict, Level.extend_singleton]
        rfl
      · simp only [Level.slice_restrict, Level.extend_slice]
        rfl
    obtain ⟨w, _, hw⟩ := D.envelope.successor i (by omega) n (by omega) q
      (D.envelope_contains i n (by omega) (by omega) q hq) a v
    have hvaleq := hw (D.envelope.valuation (n + 1) i hd (p.sample (e ∘ l) (he.comp hl)))
      ⟨D.envelope.valuation_mem _ _ _ _, hcone'⟩
    have hpeq := hw p ⟨D.envelope_contains i (n + 1) (by omega) (by omega) p hp, hpcone⟩
    exact hvaleq.trans hpeq.symm

end SelectedDiagram

def closureSelectedDiagram {A : ℕ → Type} {e : ℕ → ℕ} {he : StrictMono e}
    (S : StrongVector A e he) (X : Set (Node A 0))
    (l : ℕ → ℕ) (hl : StrictMono l) (h : ℕ)
    (hsource : ∀ i, closureNodes A X i ⊆ sourceNodes S i)
    (hlevels : closureLevels A X = Set.range (fun n : Fin h => e (l n.val))) :
    SelectedDiagram S l hl h where
  nodes := closureNodes A X
  source := hsource
  heights i t ht := by
    have hh : t.height ∈ closureLevels A X := Generated.height t ht
    rw [hlevels] at hh
    obtain ⟨n, hn⟩ := hh
    exact ⟨n.val, n.isLt, hn.symm⟩
  meet i s hs t ht := Generated.meet s t hs ht
  restrict i t ht n hn hle :=
    Generated.restrict t _ ht
      (show e (l n) ∈ closureLevels A X from by rw [hlevels]; exact ⟨⟨n, hn⟩, rfl⟩) hle
  slice i t ht n hn hlt :=
    Generated.slice t _ ht
      (show e (l n) ∈ closureLevels A X from by rw [hlevels]; exact ⟨⟨n, hn⟩, rfl⟩) hlt

theorem selected_level_rank (f : ℕ → ℕ) (hf : StrictMono f)
    (h n : ℕ) (hn : n < h) :
    levelRank ((Finset.range h).image f) (f n) = n := by
  classical
  have heq : ((Finset.range h).image f).filter (fun x => x < f n)
      = (Finset.range n).image f := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx, hlt⟩ := Finset.mem_filter.mp hx
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr (hf.lt_iff_lt.mp hlt), rfl⟩
    · intro hx
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
      have hmn := Finset.mem_range.mp hm
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr (hmn.trans hn), rfl⟩, hf hmn⟩
  unfold levelRank
  rw [heq, Finset.card_image_of_injective _ hf.injective, Finset.card_range]

theorem closure_selected_triangle {A : ℕ → Type} {X : Set (Node A 0)}
    (f : ℕ → ℕ) (hf : StrictMono f) (h : ℕ)
    (hlevels : closureLevels A X = Set.range (fun n : Fin h => f n.val))
    {i n : ℕ} (p : Level A i (f n))
    (hp : Node.mk (f n) p ∈ closureNodes A X i) : i + n < h := by
  classical
  let L := (Finset.range h).image f
  have hL : closureLevels A X ⊆ (L : Set ℕ) := by
    intro m hm
    rw [hlevels] at hm
    obtain ⟨k, rfl⟩ := hm
    exact Finset.mem_image.mpr ⟨k.val, Finset.mem_range.mpr k.isLt, rfl⟩
  have hn : n < h := by
    have hh : f n ∈ closureLevels A X := Generated.height (Node.mk (f n) p) hp
    rw [hlevels] at hh
    obtain ⟨k, hk⟩ := hh
    have hkn : k.val = n := hf.injective hk
    exact hkn ▸ k.isLt
  have hbound := closure_node_rank_bound L hL hp
  have hcard : L.card = h := by
    rw [Finset.card_image_of_injective _ hf.injective, Finset.card_range]
  have hrank : levelRank L (f n) = n := selected_level_rank f hf h n hn
  simpa only [Node.height, hcard, hrank] using hbound

/-- Actual closure-envelope existence and exact marked recovery. The two
premises are precisely containment in the infinite source vector and an
enumeration of the closure's own finite level set; meet, restriction,
slice, root, cone, and triangular conditions are all derived. -/
theorem closure_marked_envelope {A : ℕ → Type}
    [∀ j, Fintype (A j)] [∀ j, Nonempty (A j)]
    {e : ℕ → ℕ} {he : StrictMono e} (S : StrongVector A e he)
    (X : Set (Node A 0)) (l : ℕ → ℕ) (hl : StrictMono l) (h : ℕ)
    (hsource : ∀ i, closureNodes A X i ⊆ sourceNodes S i)
    (hlevels : closureLevels A X = Set.range (fun n : Fin h => e (l n.val))) :
    ∃ V : FiniteStrongVector A (e ∘ l) (he.comp hl) h,
      (∀ i n, V.nodes i n ⊆ S.nodes i (l n)) ∧
      (∀ i n, (V.nodes i n).Finite) ∧
      ∀ i n (p : Level A i (e (l n))),
        Node.mk (e (l n)) p ∈ closureNodes A X i →
          ∃ hd : i + n < h,
            p ∈ V.nodes i n ∧ V.valuation n i hd (p.sample (e ∘ l) (he.comp hl)) = p := by
  let D := closureSelectedDiagram S X l hl h hsource hlevels
  refine ⟨D.envelope, D.envelope_relative, D.envelope_finite_levels, ?_⟩
  intro i n p hp
  have hd : i + n < h := closure_selected_triangle (e ∘ l) (he.comp hl) h hlevels p hp
  exact ⟨hd, D.envelope_contains i n (by omega) (by omega) p hp, D.envelope_marked n i hd p hp⟩

end RelationalRamsey632.Source
