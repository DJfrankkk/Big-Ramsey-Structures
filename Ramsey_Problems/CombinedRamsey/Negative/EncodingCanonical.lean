import CombinedRamsey.Negative.EncodingEmbeddings

/-! The boundary and pointed type really are injective complete relation tables. -/

namespace CombinedRamsey.Negative

variable {k : ℕ} {X : Type}

theorem boundary_canonical (H : Digraph (Fin k)) : (boundary H).Canonical := by
  constructor
  · intro r x y h
    cases r with
    | E => exact h
    | N =>
      cases x with
      | inr x => simp [boundary] at h
      | inl x =>
        cases y with
        | inr y => simp [boundary] at h
        | inl y =>
          intro he
          have hv := congrArg Fin.val (Sum.inl.inj he)
          change y.val = x.val+1 at h
          omega
    | L => cases x <;> cases y <;> simp_all [boundary]
    | R => cases x <;> cases y <;> simp_all [boundary]
    | Q => cases x <;> cases y <;> simp [boundary] at h
    | G => cases x <;> cases y <;> simp [boundary] at h
  · intro r x y z h
    exact h.elim

theorem typeTable_canonical (H : Digraph (Fin k)) : (typeTable H).Canonical := by
  constructor
  · intro r x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact fun he => (boundary_canonical H).1 r x y h (Sum.inl.inj he)
      | inr y => exact Sum.inl_ne_inr
    | inr x =>
      cases y with
      | inl y => exact Sum.inr_ne_inl
      | inr y => exact h.elim
  · intro r x y z h
    exact h.elim

theorem boundary_type_reduct (H : Digraph (Fin k)) :
    (typeTable H).toRel.pullback Sum.inl = (boundary H).toRel := by
  apply RelationalRamsey632.RelStructure.ext_rel
  intro r R t
  cases R with
  | unary u => rfl
  | binary r => simp [Table.toRel, typeTable, RelationalRamsey632.RelStructure.pullback]
  | ternary r => simp [Table.toRel, typeTable, boundary]

theorem canonical_pullback (B : Table X) (hB : B.Canonical) {Y : Type} (f : Y → X) :
    (B.pullback f).Canonical := by
  constructor
  · intro r x y h hn
    exact hB.1 r (f x) (f y) h (congrArg f hn)
  · intro r x y z h
    have hc := hB.2 r (f x) (f y) (f z) h
    exact ⟨fun hn => hc.1 (congrArg f hn), fun hn => hc.2.1 (congrArg f hn),
      fun hn => hc.2.2 (congrArg f hn)⟩

end CombinedRamsey.Negative
