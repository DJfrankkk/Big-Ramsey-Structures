import CombinedRamsey.Negative.EncodingBoundary

/-! A complete relation table on the disjoint union, with every mixed value fixed. -/

namespace CombinedRamsey.Negative

variable {X : Type} {k : ℕ}

def completionTable (H : Digraph (Fin k)) (B : Table X) (c : X → X → Fin k) :
    Table (EncodedBoundary H ⊕ X) where
  unary u x := match x with
    | .inl a => (boundary H).unary u a
    | .inr x => B.unary u x
  binary r x y := match x, y with
    | .inl a, .inl b => (boundary H).binary r a b
    | .inr x, .inr y => B.binary r x y
    | _, _ => r = .E
  ternary r x y z := match x, y, z with
    | .inr h, .inr v, .inr w => B.ternary r h v w
    | .inl (.inl l), .inr h, .inr v => match r with
      | .S s => B.Domain h v ∧ phase (c h v) l = s
      | _ => False
    | .inl (.inr p), .inr h, .inr v => match r with
      | .UL => B.Domain h v ∧ c h v = p.val.1
      | .UR => B.Domain h v ∧ c h v = p.val.2
      | _ => False
    | _, _, _ => False

theorem completionTable_completion (H : Digraph (Fin k)) (B : Table X)
    (c : X → X → Fin k) (hB : B.PureDelta) :
    Completion H B (completionTable H B c) := by
  constructor
  · intro u a; rfl
  · intro u x; rfl
  · intro r a b; rfl
  · intro r x y; rfl
  · intro r a x; rfl
  · intro r x a; rfl
  · intro r a b d; simp [completionTable]
  · intro r x y z; rfl
  · exact hB
  · intro x r a b d hab had hbd
    cases a with
    | inl a =>
      cases b with
      | inl b => simp [completionTable]
      | inr b =>
        cases d with
        | inl d => simp [completionTable]
        | inr d => exact (hbd (by cases b; cases d; rfl)).elim
    | inr a =>
      cases b with
      | inl b => simp [completionTable]
      | inr b => exact (hab (by cases a; cases b; rfl)).elim

theorem constructed_old_of_O (H : Digraph (Fin k)) (B : Table X)
    (c : X → X → Fin k) (hB : B.PureDelta) (x : EncodedBoundary H ⊕ X)
    (hx : (completionTable H B c).unary .O x) :
    ∃ a, x = Sum.inl a := by
  cases x with
  | inl a => exact ⟨a, rfl⟩
  | inr x => have h := (hB x .O).mp hx; cases h

theorem constructed_new_of_V (H : Digraph (Fin k)) (B : Table X)
    (c : X → X → Fin k) (x : EncodedBoundary H ⊕ X)
    (hx : (completionTable H B c).unary .V x) :
    ∃ v, x = Sum.inr v := by
  cases x with
  | inr v => exact ⟨v, rfl⟩
  | inl a => cases a <;> simp [completionTable, boundary] at hx

theorem constructed_path_of_path (H : Digraph (Fin k)) (B : Table X)
    (c : X → X → Fin k) (hB : B.PureDelta) (x : EncodedBoundary H ⊕ X)
    (hx : (completionTable H B c).unary .path x) :
    ∃ l, x = Sum.inl (Sum.inl l) := by
  cases x with
  | inl a =>
    cases a with
    | inl l => exact ⟨l, rfl⟩
    | inr p => simp [completionTable, boundary] at hx
  | inr x => have h := (hB x .path).mp hx; cases h

theorem constructed_test_of_test (H : Digraph (Fin k)) (B : Table X)
    (c : X → X → Fin k) (hB : B.PureDelta) (x : EncodedBoundary H ⊕ X)
    (hx : (completionTable H B c).unary .test x) :
    ∃ p, x = Sum.inl (Sum.inr p) := by
  cases x with
  | inl a =>
    cases a with
    | inl l => simp [completionTable, boundary] at hx
    | inr p => exact ⟨p, rfl⟩
  | inr x => have h := (hB x .test).mp hx; cases h

theorem constructed_new_edge (H : Digraph (Fin k)) (B : Table X)
    (c : X → X → Fin k) (h v : X) :
    (completionTable H B c).Edge (.inr h) (.inr v) ↔ B.Edge h v := by
  simp [Table.Edge, completionTable]

theorem completionTable_legal (H : Digraph (Fin k)) (B : Table X)
    (c : X → X → Fin k) (hB : B.PureDelta) (hc : GoodColors B H c) :
    (completionTable H B c).Legal := by
  constructor
  · intro a h v hcomplete _ hap hhv hvv hq
    obtain ⟨l, rfl⟩ := constructed_path_of_path H B c hB a hap
    obtain ⟨h, rfl⟩ := constructed_new_of_V H B c h hhv
    obtain ⟨v, rfl⟩ := constructed_new_of_V H B c v hvv
    have hd : B.Domain h v :=
      ⟨(constructed_new_edge H B c h v).mp hcomplete.2.2, hq⟩
    refine ⟨⟨phase (c h v) l, ?_, ?_⟩, ?_, ?_⟩
    · exact ⟨hd, rfl⟩
    · intro t ht; exact ht.2.symm
    · intro hf
      refine ⟨hd, ?_⟩
      have hl : l.val = 0 := hf
      simp [phase, phaseNat, hl]
    · intro hl
      refine ⟨hd, ?_⟩
      have he : l.val = k+1 := hl
      apply (phaseNat_two_iff _ _).mpr
      omega
  · intro a b h v _ _ hap _ hbp hhv hvv hn _ s t hs ht
    obtain ⟨l, rfl⟩ := constructed_path_of_path H B c hB a hap
    obtain ⟨m, rfl⟩ := constructed_path_of_path H B c hB b hbp
    obtain ⟨h, rfl⟩ := constructed_new_of_V H B c h hhv
    obtain ⟨v, rfl⟩ := constructed_new_of_V H B c v hvv
    have hm : m.val = l.val+1 := hn
    have hs' : phase (c h v) l = s := hs.2
    have ht' : phase (c h v) m = t := ht.2
    rw [← hs', ← ht']
    simpa [phase, hm] using phaseNat_transition ((c h v).val+1) l.val
  · intro b a h v hcomplete _ hbt _ hap hhv hvv hq
    obtain ⟨p, rfl⟩ := constructed_test_of_test H B c hB b hbt
    obtain ⟨l, rfl⟩ := constructed_path_of_path H B c hB a hap
    obtain ⟨h, rfl⟩ := constructed_new_of_V H B c h hhv
    obtain ⟨v, rfl⟩ := constructed_new_of_V H B c v hvv
    have hd : B.Domain h v :=
      ⟨(constructed_new_edge H B c h v).mp hcomplete.2.2.2.2.2, hq⟩
    constructor
    · intro hl
      have he : l.val = p.val.1.val+1 := hl
      change (B.Domain h v ∧ c h v = p.val.1) ↔ (B.Domain h v ∧ phase (c h v) l = .one)
      simp only [hd, true_and, phase, phaseNat_one_iff, he, Nat.add_right_cancel_iff,
        Fin.ext_iff]
      exact eq_comm
    · intro hr
      have he : l.val = p.val.2.val+1 := hr
      change (B.Domain h v ∧ c h v = p.val.2) ↔ (B.Domain h v ∧ phase (c h v) l = .one)
      simp only [hd, true_and, phase, phaseNat_one_iff, he, Nat.add_right_cancel_iff,
        Fin.ext_iff]
      exact eq_comm
  · intro b h v w hcomplete _ hbt hhv hvv hwv hqv hqw hgvw hbits
    obtain ⟨p, rfl⟩ := constructed_test_of_test H B c hB b hbt
    obtain ⟨h, rfl⟩ := constructed_new_of_V H B c h hhv
    obtain ⟨v, rfl⟩ := constructed_new_of_V H B c v hvv
    obtain ⟨w, rfl⟩ := constructed_new_of_V H B c w hwv
    have hdv : B.Domain h v :=
      ⟨(constructed_new_edge H B c h v).mp hcomplete.2.2.2.1, hqv⟩
    have hdw : B.Domain h w :=
      ⟨(constructed_new_edge H B c h w).mp hcomplete.2.2.2.2.1, hqw⟩
    have ha : B.LocalArc h v w :=
      ⟨hdv, hdw, (constructed_new_edge H B c v w).mp hcomplete.2.2.2.2.2, hgvw⟩
    have hc' := hc h v w ha
    have hl : c h v = p.val.1 := hbits.1.2
    have hr : c h w = p.val.2 := hbits.2.2
    exact p.property (by simpa [hl, hr] using hc')

end CombinedRamsey.Negative
