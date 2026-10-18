import CombinedRamsey.Negative.EncodingNecessity
import CombinedRamsey.Negative.EncodingRelational

/-! Each table completion supplies actual full embeddings of the base and type. -/

namespace CombinedRamsey.Negative

open RelationalRamsey632

variable {X : Type} {k : ℕ} {H : Digraph (Fin k)} {B : Table X}
  {Y : Table (EncodedBoundary H ⊕ X)}

namespace Completion

def newEmbedding (hY : Completion H B Y) : RelEmbedding B.toRel Y.toRel where
  toFun := Sum.inr
  injective := Sum.inr_injective
  map_rel R t := by
    cases R with
    | unary u => exact (hY.new_unary u (t 0)).symm
    | binary r =>
      simp only [Table.toRel, Function.comp_apply, Sum.inr.injEq, ne_eq, hY.new_binary]
    | ternary r =>
      simp only [Table.toRel, Function.comp_apply, Sum.inr.injEq, ne_eq, hY.new_ternary]

def oldEmbedding (hY : Completion H B Y) : RelEmbedding (boundary H).toRel Y.toRel where
  toFun := Sum.inl
  injective := Sum.inl_injective
  map_rel R t := by
    cases R with
    | unary u => exact (hY.old_unary u (t 0)).symm
    | binary r =>
      simp only [Table.toRel, Function.comp_apply, Sum.inl.injEq, ne_eq, hY.old_binary]
    | ternary r =>
      simp [Table.toRel, boundary, hY.old_ternary]

def pointMap (x : X) : EncodedBoundary H ⊕ Unit → EncodedBoundary H ⊕ X :=
  Sum.map id (fun _ => x)

theorem pointMap_injective (x : X) : Function.Injective (pointMap (H := H) x) := by
  apply Sum.map_injective.mpr
  exact ⟨Function.injective_id, fun _ _ _ => Subsingleton.elim _ _⟩

def pointEmbedding (hY : Completion H B Y) (x : X) :
    RelEmbedding (typeTable H).toRel Y.toRel where
  toFun := pointMap x
  injective := pointMap_injective x
  map_rel R t := by
    cases R with
    | unary u =>
      cases ht : t 0 with
      | inl a => simpa [Table.toRel, typeTable, pointMap, ht] using (hY.old_unary u a).symm
      | inr a =>
        simpa [Table.toRel, typeTable, pointMap, ht] using
          ((hY.new_unary u x).trans (hY.point_unary x u)).symm
    | binary r =>
      cases h0 : t 0 with
      | inl a =>
        cases h1 : t 1 with
        | inl b =>
          simpa [Table.toRel, typeTable, pointMap, h0, h1] using
            and_congr Iff.rfl (hY.old_binary r a b).symm
        | inr b =>
          simpa [Table.toRel, typeTable, pointMap, h0, h1] using
            (hY.mixed_binary_left r a x).symm
      | inr a =>
        cases h1 : t 1 with
        | inl b =>
          simpa [Table.toRel, typeTable, pointMap, h0, h1] using
            (hY.mixed_binary_right r x b).symm
        | inr b => cases a; cases b; simp [Table.toRel, typeTable, pointMap, h0, h1]
    | ternary r =>
      constructor
      · intro ht; simp [Table.toRel, typeTable] at ht
      · intro ht
        have h01 : t 0 ≠ t 1 := fun h => ht.1 (congrArg (pointMap x) h)
        have h02 : t 0 ≠ t 2 := fun h => ht.2.1 (congrArg (pointMap x) h)
        have h12 : t 1 ≠ t 2 := fun h => ht.2.2.1 (congrArg (pointMap x) h)
        exact (hY.one_new_ternary x r (t 0) (t 1) (t 2) h01 h02 h12 ht.2.2.2).elim

end Completion

end CombinedRamsey.Negative
