import CombinedRamsey.Negative.EncodingPath

/-! The actual full boundary table; unspecified values are false. -/

namespace CombinedRamsey.Negative

variable {k : ℕ}

abbrev Nonarc (H : Digraph (Fin k)) := {p : Fin k × Fin k // ¬ H.arc p.1 p.2}
abbrev EncodedBoundary (H : Digraph (Fin k)) := Fin (k+2) ⊕ Nonarc H

def boundary (H : Digraph (Fin k)) : Table (EncodedBoundary H) where
  unary u x := match u, x with
    | .O, _ => True
    | .path, .inl _ => True
    | .test, .inr _ => True
    | .first, .inl l => l.val = 0
    | .last, .inl l => l.val = k+1
    | _, _ => False
  binary r x y := match r, x, y with
    | .E, x, y => x ≠ y
    | .N, .inl l, .inl m => m.val = l.val+1
    | .L, .inr p, .inl l => l.val = p.val.1.val+1
    | .R, .inr p, .inl l => l.val = p.val.2.val+1
    | _, _, _ => False
  ternary _ _ _ _ := False

theorem boundary_legal (H : Digraph (Fin k)) : (boundary H).Legal := by
  constructor
  · intro a h v _ _ _ hV
    cases h <;> simp [boundary] at hV
  · intro a b h v _ _ _ _ _ hV
    cases h <;> simp [boundary] at hV
  · intro b a h v _ _ _ _ _ hV
    cases h <;> simp [boundary] at hV
  · intro b h v w _ _ _ hV
    cases h <;> simp [boundary] at hV

variable {X : Type}

def typeTable (H : Digraph (Fin k)) : Table (EncodedBoundary H ⊕ Unit) where
  unary u x := match x with
    | .inl a => (boundary H).unary u a
    | .inr _ => u = .V
  binary r x y := match x, y with
    | .inl a, .inl b => (boundary H).binary r a b
    | .inr _, .inr _ => False
    | _, _ => r = .E
  ternary _ _ _ _ := False

theorem typeTable_legal (H : Digraph (Fin k)) : (typeTable H).Legal := by
  have veq : ∀ x, (typeTable H).unary .V x → x = Sum.inr () := by
    intro x hx
    cases x with
    | inl a => cases a <;> simp [typeTable, boundary] at hx
    | inr u => cases u; rfl
  constructor
  · intro a h v hc _ _ hV vV
    exact (hc.2.2.1 (by rw [veq h hV, veq v vV])).elim
  · intro a b h v hc _ _ _ _ hV vV
    exact (hc.2.2.2.2.2.1 (by rw [veq h hV, veq v vV])).elim
  · intro b a h v hc _ _ _ _ hV vV
    exact (hc.2.2.2.2.2.1 (by rw [veq h hV, veq v vV])).elim
  · intro b h v w hc _ _ hV vV
    exact (hc.2.2.2.1.1 (by rw [veq h hV, veq v vV])).elim

/- The completion condition quantifies every table entry on each one-point
   extension, including all ordered ternary tuples and repeated arguments.
   Repeated arguments are ignored by `toRel` and may canonically be false. -/
structure Completion (H : Digraph (Fin k)) (B : Table X)
    (Y : Table (EncodedBoundary H ⊕ X)) : Prop where
  old_unary : ∀ u a, Y.unary u (.inl a) ↔ (boundary H).unary u a
  new_unary : ∀ u x, Y.unary u (.inr x) ↔ B.unary u x
  old_binary : ∀ r a b, Y.binary r (.inl a) (.inl b) ↔ (boundary H).binary r a b
  new_binary : ∀ r x y, Y.binary r (.inr x) (.inr y) ↔ B.binary r x y
  mixed_binary_left : ∀ r a x, Y.binary r (.inl a) (.inr x) ↔ r = .E
  mixed_binary_right : ∀ r x a, Y.binary r (.inr x) (.inl a) ↔ r = .E
  old_ternary : ∀ r a b c, ¬ Y.ternary r (.inl a) (.inl b) (.inl c)
  new_ternary : ∀ r x y z, Y.ternary r (.inr x) (.inr y) (.inr z) ↔ B.ternary r x y z
  point_unary : B.PureDelta
  one_new_ternary : ∀ x r a b c, a ≠ b → a ≠ c → b ≠ c →
    ¬ Y.ternary r ((Sum.map id (fun _ : Unit => x)) a)
      ((Sum.map id (fun _ : Unit => x)) b) ((Sum.map id (fun _ : Unit => x)) c)

end CombinedRamsey.Negative
