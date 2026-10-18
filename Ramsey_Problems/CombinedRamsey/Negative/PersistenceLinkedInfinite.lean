import CombinedRamsey.Negative.PersistenceLinkedAge
import Mathlib.Logic.Denumerable

namespace CombinedRamsey.Negative

open RelationalRamsey632 RelationalRamsey632.Existence

variable {L : Language} {X : Type} {n : ℕ}
    {t : RelStructure L (Fin n ⊕ Unit)} {K : RelStructure L X}
    {b : RelEmbedding (t.pullback Sum.inl) K}

theorem realization_outside_finite_set (hh : FiniteEmbeddingHomogeneous K)
    (hfree : AgeSharedFree K) (hreal : (Realizations t K b).Nonempty)
    (F : Set X) (hF : F.Finite) (hFP : F ⊆ Realizations t K b) :
    ∃ x ∈ Realizations t K b, x ∉ F := by
  classical
  letI : Finite F := hF.to_subtype
  let anchorMap : Fin n ⊕ F → X := Sum.elim b Subtype.val
  have hinj : Function.Injective anchorMap := by
    apply Sum.elim_injective.mpr
    refine ⟨b.injective, Subtype.val_injective, ?_⟩
    intro a x h
    exact realizes_outside_boundary (hFP x.property) ⟨a, h⟩
  let ML := K.pullback anchorMap
  let eL : RelEmbedding ML K := RelEmbedding.pullback K anchorMap hinj
  have hbase : ML.pullback Sum.inl = t.pullback Sum.inl := eL.pullback_eq ▸ b.pullback_eq
  obtain ⟨z, p, hp, hs⟩ := hreal
  have ht : Nonempty (RelEmbedding t K) := ⟨p⟩
  let W := SharedBaseAmalgam.model ML t
  let l := SharedBaseAmalgam.leftEmbedding ML t hbase
  let r := SharedBaseAmalgam.rightEmbedding ML t hbase
  have hW : Nonempty (RelEmbedding W K) := hfree (Fin n) F Unit ML t hbase ⟨eL⟩ ht
  obtain ⟨v, hv⟩ := finite_age_extension hh l eL hW
  let x := v (r (Sum.inr ()))
  have hx : x ∈ Realizations t K b :=
    ⟨v.comp r, fun a => hv (Sum.inl a), rfl⟩
  refine ⟨x, hx, ?_⟩
  intro hxF
  have h : v (r (Sum.inr ())) = v (l (Sum.inr ⟨x, hxF⟩)) :=
    (hv (Sum.inr ⟨x, hxF⟩)).symm
  have he := v.injective h
  change Sum.inr (Sum.inr ()) = Sum.inr (Sum.inl (⟨x, hxF⟩ : F)) at he
  cases he

theorem realizations_infinite (hh : FiniteEmbeddingHomogeneous K)
    (hfree : AgeSharedFree K) (hreal : (Realizations t K b).Nonempty) :
    Infinite (Realizations t K b) := by
  classical
  by_contra hinf
  haveI : Finite (Realizations t K b) := not_infinite_iff_finite.mp hinf
  have hP : (Realizations t K b).Finite := Set.toFinite _
  obtain ⟨x, hx, hn⟩ := realization_outside_finite_set hh hfree hreal
    (Realizations t K b) hP (fun _ h => h)
  exact hn hx

theorem linked_vertices_infinite (hh : FiniteEmbeddingHomogeneous K)
    (hfree : AgeSharedFree K) (hreal : (Realizations t K b).Nonempty) :
    Infinite (LinkedVertices t K b) := by
  letI := realizations_infinite hh hfree hreal
  let f : Realizations t K b → LinkedVertices t K b := fun x =>
    ⟨⟨x.val, realizes_outside_boundary x.property⟩, x.property⟩
  exact Infinite.of_injective f (fun _ _ h => Subtype.ext (congrArg linkedValue h))

theorem linked_vertices_nat_equiv [Countable X] (hh : FiniteEmbeddingHomogeneous K)
    (hfree : AgeSharedFree K) (hreal : (Realizations t K b).Nonempty) :
    Nonempty (ℕ ≃ LinkedVertices t K b) := by
  haveI := linked_vertices_infinite hh hfree hreal
  haveI : Countable (LinkedVertices t K b) := by
    unfold LinkedVertices BaseComplement
    infer_instance
  infer_instance

end CombinedRamsey.Negative
