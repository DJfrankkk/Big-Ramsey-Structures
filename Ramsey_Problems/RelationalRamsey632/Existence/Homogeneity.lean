import RelationalRamsey632.Existence.FiniteExtension
import Mathlib.ModelTheory.Fraisse

namespace RelationalRamsey632.Existence

open scoped FirstOrder

variable {L : Language} {X : Type}

def insertMap (F : Set X) (x : X) : F ⊕ Unit → X := Sum.elim Subtype.val (fun _ => x)

theorem insertMap_injective (F : Set X) (x : X) (hx : x ∉ F) : Function.Injective (insertMap F x) := by
  intro u v he
  cases u with
  | inl a =>
    cases v with
    | inl b => exact congrArg Sum.inl (Subtype.ext he)
    | inr b => exact False.elim (hx ((show a.val = x from he) ▸ a.property))
  | inr a =>
    cases v with
    | inl b => exact False.elim (hx ((show x = b.val from he).symm ▸ b.property))
    | inr b => exact congrArg Sum.inr (Subsingleton.elim _ _)

/-- The finite EP yields the exact extension-pair condition used by
Mathlib's proved back-and-forth theorem. -/
theorem extension_pair {inj : Bool} (K : RelStructure L X) (hK : Admissible inj K)
    (hEP : OnePointExtensionProperty inj K) :
    @FirstOrder.Language.IsExtensionPair L.toFirstOrder X X K.toFirstOrder K.toFirstOrder := by
  classical
  letI := K.toFirstOrder
  intro f x
  by_cases hx : x ∈ f.val.dom
  · exact ⟨f, hx, le_refl f⟩
  · haveI : Finite f.val.dom := f.property.finite
    let F : Set X := f.val.dom
    let B := K.pullback (insertMap F x)
    letI := B.toFirstOrder
    let old : RelEmbedding (B.pullback Sum.inl) K := {
      toFun := f.val.toEmbedding
      injective := f.val.toEmbedding.injective
      map_rel := by
        intro r R t
        exact (f.val.toEmbedding.map_rel' R t).symm }
    obtain ⟨g, hg⟩ := extend_one_point_finite K hEP B (admissible_pullback K hK (insertMap F x)) old
    let s := RelEmbedding.pullback K (insertMap F x) (insertMap_injective F x hx)
    let sf := s.toFirstOrder
    let gf := g.toFirstOrder
    let p : FirstOrder.Language.PartialEquiv L.toFirstOrder X X := {
      dom := sf.toHom.range
      cod := gf.toHom.range
      toEquiv := gf.equivRange.comp sf.equivRange.symm }
    haveI : Finite p.dom := Finite.of_equiv (F ⊕ Unit) sf.equivRange.toEquiv
    have hFG : p.dom.FG := FirstOrder.Language.Substructure.FG.of_finite
    refine ⟨⟨p, hFG⟩, ?_, ?_⟩
    · exact ⟨Sum.inr (), rfl⟩
    · change f.val ≤ p
      have hle : f.val.dom ≤ p.dom := by
        intro y hy
        exact ⟨Sum.inl ⟨y, hy⟩, rfl⟩
      refine ⟨hle, ?_⟩
      · ext y
        change ((gf.equivRange.comp sf.equivRange.symm)
          (FirstOrder.Language.Substructure.inclusion hle y)).val = (f.val.toEmbedding y)
        have hidx : sf.equivRange.symm (FirstOrder.Language.Substructure.inclusion hle y) = Sum.inl y := by
          apply sf.equivRange.injective
          rw [sf.equivRange.apply_symm_apply]
          apply Subtype.ext
          rfl
        change gf (sf.equivRange.symm (FirstOrder.Language.Substructure.inclusion hle y)) = _
        rw [hidx]
        exact hg y

theorem ultrahomogeneous_of_EP {inj : Bool} [Countable X]
    (K : RelStructure L X) (hK : Admissible inj K) (hEP : OnePointExtensionProperty inj K) :
    @FirstOrder.Language.IsUltrahomogeneous L.toFirstOrder X K.toFirstOrder := by
  letI := K.toFirstOrder
  exact (FirstOrder.Language.isUltrahomogeneous_iff_IsExtensionPair
    (FirstOrder.Language.Structure.cg_of_countable)).mpr (extension_pair K hK hEP)

end RelationalRamsey632.Existence
