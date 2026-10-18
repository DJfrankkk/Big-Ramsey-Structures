import CombinedRamsey.Negative.EncodingConstruction

/-! Necessity uses an arbitrary legal completion, rather than the chosen table. -/

namespace CombinedRamsey.Negative

variable {X : Type} {k : ℕ} {H : Digraph (Fin k)} {B : Table X}
  {Y : Table (EncodedBoundary H ⊕ X)}

namespace Completion

theorem new_edge (hY : Completion H B Y) (x y : X) :
    Y.Edge (.inr x) (.inr y) ↔ B.Edge x y := by
  simp only [Table.Edge, Sum.inr.injEq, ne_eq, hY.new_binary]

theorem mixed_edge (hY : Completion H B Y) (a : EncodedBoundary H) (x : X) :
    Y.Edge (.inl a) (.inr x) := by
  exact ⟨Sum.inl_ne_inr, (hY.mixed_binary_left .E a x).mpr rfl,
    (hY.mixed_binary_right .E x a).mpr rfl⟩

theorem old_edge (hY : Completion H B Y) {a b : EncodedBoundary H} (hab : a ≠ b) :
    Y.Edge (.inl a) (.inl b) := by
  exact ⟨fun h => hab (Sum.inl.inj h), (hY.old_binary .E a b).mpr hab,
    (hY.old_binary .E b a).mpr hab.symm⟩

theorem path_complete3 (hY : Completion H B Y) (l : Fin (k+2))
    {h v : X} (hd : B.Domain h v) :
    Y.Complete3 (.inl (.inl l)) (.inr h) (.inr v) :=
  ⟨hY.mixed_edge _ _, hY.mixed_edge _ _, (hY.new_edge h v).mpr hd.1⟩

theorem old2_complete4 (hY : Completion H B Y) {a b : EncodedBoundary H}
    (hab : a ≠ b) {h v : X} (hd : B.Domain h v) :
    Y.Complete4 (.inl a) (.inl b) (.inr h) (.inr v) :=
  ⟨hY.old_edge hab, hY.mixed_edge _ _, hY.mixed_edge _ _,
    hY.mixed_edge _ _, hY.mixed_edge _ _, (hY.new_edge h v).mpr hd.1⟩

theorem old1_complete4 (hY : Completion H B Y) (a : EncodedBoundary H)
    {h v w : X} (ha : B.LocalArc h v w) :
    Y.Complete4 (.inl a) (.inr h) (.inr v) (.inr w) :=
  ⟨hY.mixed_edge _ _, hY.mixed_edge _ _, hY.mixed_edge _ _,
    (hY.new_edge h v).mpr ha.1.1, (hY.new_edge h w).mpr ha.2.1.1,
    (hY.new_edge v w).mpr ha.2.2.1⟩

theorem new_V (hY : Completion H B Y) (x : X) : Y.unary .V (.inr x) :=
  (hY.new_unary .V x).mpr ((hY.point_unary x .V).mpr rfl)

theorem path_O (hY : Completion H B Y) (l : Fin (k+2)) :
    Y.unary .O (.inl (.inl l)) := (hY.old_unary .O _).mpr trivial

theorem path_path (hY : Completion H B Y) (l : Fin (k+2)) :
    Y.unary .path (.inl (.inl l)) := (hY.old_unary .path _).mpr trivial

theorem test_O (hY : Completion H B Y) (p : Nonarc H) :
    Y.unary .O (.inl (.inr p)) := (hY.old_unary .O _).mpr trivial

theorem test_test (hY : Completion H B Y) (p : Nonarc H) :
    Y.unary .test (.inl (.inr p)) := (hY.old_unary .test _).mpr trivial

theorem path_marker (hY : Completion H B Y) (hlegal : Y.Legal)
    {h v : X} (hd : B.Domain h v) :
    ∃ i : Fin k, ∀ l : Fin (k+2), ∀ s : State,
      Y.ternary (.S s) (.inl (.inl l)) (.inr h) (.inr v) ↔ phase i l = s := by
  classical
  have q : Y.binary .Q (.inr h) (.inr v) := (hY.new_binary .Q h v).mpr hd.2
  have hp := fun l : Fin (k+2) => hlegal.states (.inl (.inl l)) (.inr h) (.inr v)
    (hY.path_complete3 l hd) (hY.path_O l) (hY.path_path l)
    (hY.new_V h) (hY.new_V v) q
  choose s hs huniq using fun l => (hp l).1
  have hequiv : ∀ l t, Y.ternary (.S t) (.inl (.inl l)) (.inr h) (.inr v) ↔ s l = t := by
    intro l t
    constructor
    · intro ht; exact (huniq l t ht).symm
    · intro ht; rw [← ht]; exact hs l
  have hf : s ⟨0, by omega⟩ = .zero := by
    apply (hequiv _ _).mp
    exact (hp ⟨0, by omega⟩).2.1 ((hY.old_unary .first _).mpr rfl)
  have hl : s ⟨k+1, by omega⟩ = .two := by
    apply (hequiv _ _).mp
    exact (hp ⟨k+1, by omega⟩).2.2 ((hY.old_unary .last _).mpr rfl)
  have ht : ∀ l : Fin (k+1), Table.Transition (s ⟨l.val, by omega⟩)
      (s ⟨l.val+1, by omega⟩) := by
    intro l
    let a : Fin (k+2) := ⟨l.val, by omega⟩
    let b : Fin (k+2) := ⟨l.val+1, by omega⟩
    have hab : (Sum.inl a : EncodedBoundary H) ≠ Sum.inl b := by
      intro he
      have hv := congrArg Fin.val (Sum.inl.inj he)
      simp [a, b] at hv
    exact hlegal.transition (.inl (.inl a)) (.inl (.inl b)) (.inr h) (.inr v)
      (hY.old2_complete4 hab hd) (hY.path_O a) (hY.path_path a)
      (hY.path_O b) (hY.path_path b) (hY.new_V h) (hY.new_V v)
      ((hY.old_binary .N _ _).mpr rfl) q _ _ (hs a) (hs b)
  obtain ⟨i, hi⟩ := finite_path_marker s hf hl ht
  refine ⟨i, ?_⟩
  intro l t
  rw [hequiv, hi l]

theorem marker_bits (hY : Completion H B Y) (hlegal : Y.Legal)
    {h v : X} (hd : B.Domain h v) {i : Fin k}
    (hi : ∀ l : Fin (k+2), ∀ s : State,
      Y.ternary (.S s) (.inl (.inl l)) (.inr h) (.inr v) ↔ phase i l = s)
    (p : Nonarc H) :
    (Y.ternary .UL (.inl (.inr p)) (.inr h) (.inr v) ↔ i = p.val.1) ∧
    (Y.ternary .UR (.inl (.inr p)) (.inr h) (.inr v) ↔ i = p.val.2) := by
  have q := (hY.new_binary .Q h v).mpr hd.2
  have base : ∀ l : Fin (k+2),
      (Y.binary .L (.inl (.inr p)) (.inl (.inl l)) →
        (Y.ternary .UL (.inl (.inr p)) (.inr h) (.inr v) ↔
          Y.ternary (.S .one) (.inl (.inl l)) (.inr h) (.inr v))) ∧
      (Y.binary .R (.inl (.inr p)) (.inl (.inl l)) →
        (Y.ternary .UR (.inl (.inr p)) (.inr h) (.inr v) ↔
          Y.ternary (.S .one) (.inl (.inl l)) (.inr h) (.inr v))) := by
    intro l
    exact hlegal.bits _ _ _ _ (hY.old2_complete4 Sum.inr_ne_inl hd)
      (hY.test_O p) (hY.test_test p) (hY.path_O l) (hY.path_path l)
      (hY.new_V h) (hY.new_V v) q
  constructor
  · let l : Fin (k+2) := ⟨p.val.1.val+1, by omega⟩
    have he := (base l).1 ((hY.old_binary .L _ _).mpr rfl)
    rw [he, hi l .one]
    simp only [phase, phaseNat_one_iff, l, Nat.add_right_cancel_iff, Fin.ext_iff]
    exact eq_comm
  · let l : Fin (k+2) := ⟨p.val.2.val+1, by omega⟩
    have he := (base l).2 ((hY.old_binary .R _ _).mpr rfl)
    rw [he, hi l .one]
    simp only [phase, phaseNat_one_iff, l, Nat.add_right_cancel_iff, Fin.ext_iff]
    exact eq_comm

theorem good_colors (hk : 0 < k) (hY : Completion H B Y) (hlegal : Y.Legal) :
    ∃ c, GoodColors B H c := by
  classical
  have hm := fun h v (hd : B.Domain h v) => hY.path_marker hlegal hd
  choose marker hmarker using hm
  let c : X → X → Fin k := fun h v =>
    if hd : B.Domain h v then marker h v hd else ⟨0, hk⟩
  refine ⟨c, ?_⟩
  intro h v w ha
  by_contra hn
  let p : Nonarc H := ⟨(c h v, c h w), hn⟩
  have hc1 : c h v = marker h v ha.1 := by simp [c, ha.1]
  have hc2 : c h w = marker h w ha.2.1 := by simp [c, ha.2.1]
  have hu := (hY.marker_bits hlegal ha.1 (hmarker h v ha.1) p).1.mpr
    (by simpa [p] using hc1.symm)
  have hr := (hY.marker_bits hlegal ha.2.1 (hmarker h w ha.2.1) p).2.mpr
    (by simpa [p] using hc2.symm)
  exact hlegal.conflict _ _ _ _ (hY.old1_complete4 (.inr p) ha)
    (hY.test_O p) (hY.test_test p) (hY.new_V h) (hY.new_V v) (hY.new_V w)
    ((hY.new_binary .Q h v).mpr ha.1.2)
    ((hY.new_binary .Q h w).mpr ha.2.1.2)
    ((hY.new_binary .G v w).mpr ha.2.2.2) ⟨hu, hr⟩

end Completion

theorem legal_completion_iff {X : Type} {k : ℕ} (hk : 0 < k)
    (H : Digraph (Fin k)) (B : Table X) :
    (∃ Y, Y.Legal ∧ Completion H B Y) ↔
      B.PureDelta ∧ ∀ h, Nonempty (Hom (B.localGraph h) H) := by
  constructor
  · rintro ⟨Y, hlegal, hY⟩
    exact ⟨hY.point_unary, (goodColors_iff_local_homs hk B H).mp
      (hY.good_colors hk hlegal)⟩
  · rintro ⟨hB, hf⟩
    obtain ⟨c, hc⟩ := (goodColors_iff_local_homs hk B H).mpr hf
    exact ⟨completionTable H B c, completionTable_legal H B c hB hc,
      completionTable_completion H B c hB⟩

end CombinedRamsey.Negative
