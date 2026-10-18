import RelationalRamsey632.Source.Envelopes
import RelationalRamsey632.Source.PatternEmbeddings
import RelationalRamsey632.Source.ValuationModel

/-! Exact finite occurrences for every tuple in a strong-vector valuation image. -/

namespace RelationalRamsey632.Source

namespace StrongVector

variable {A : ℕ → Type} [∀ j, Fintype (A j)] [∀ j, Nonempty (A j)]
    {e : ℕ → ℕ} {he : StrictMono e} (S : StrongVector A e he)

theorem marked_tuple_envelope {U : Type} {b : ℕ}
    (v : Fin b → Vertex A U) :
    ∃ V : FiniteStrongVector A
        (e ∘ levelEnumeration (tupleLevels v))
        (he.comp (levelEnumeration_strictMono (tupleLevels v))) (tupleLevels v).card,
      (∀ i n, V.nodes i n ⊆ S.nodes i (levelEnumeration (tupleLevels v) n)) ∧
      ∀ j, V.mapVertices (normalForm v j) = S.mapVertices (v j) := by
  let L := tupleLevels v
  let X := S.mapNode '' tupleProjections v
  have hSource : ∀ i, closureNodes A X i ⊆ sourceNodes S i := by
    intro i t ht
    rw [(S.closure_covariance (tupleProjections v)).1 i] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    exact ⟨u.height, S.valuation u.height i u.table, S.valuation_mem _ _ _, rfl⟩
  have hlevels :
      closureLevels A X =
        Set.range (fun n : Fin L.card => e (levelEnumeration L n.val)) := by
    rw [(S.closure_covariance (tupleProjections v)).2, ← tupleLevels_coe]
    exact (Finset.coe_image (f := e) (s := L)).symm.trans
      (levelImage_active_range (e := e) L)
  obtain ⟨V, hrelative, _, hmarked⟩ := closure_marked_envelope S X
    (levelEnumeration L) (levelEnumeration_strictMono L) L.card hSource hlevels
  refine ⟨V, hrelative, ?_⟩
  intro j
  apply Prod.ext
  · rfl
  · change V.mapNodeDefault (canonicalCompression L (v j).2) = S.mapNode (v j).2
    have hm : (v j).2.height ∈ L := marked_height_mem v j
    cases hj : (v j).2 with
    | mk a t =>
      rw [hj] at hm
      obtain ⟨n, hn⟩ := levelEnumeration_range_contains L hm
      change a = levelEnumeration L n at hn
      subst a
      let p := S.valuation (levelEnumeration L n) 0 t
      have hp : (Node.mk (e (levelEnumeration L n)) p : Node A 0) ∈
          closureNodes A X 0 :=
        Generated.generator _ ⟨Node.mk (levelEnumeration L n) t, ⟨j, hj⟩, rfl⟩
      obtain ⟨hd, _, hmark⟩ := hmarked 0 n p hp
      have hsamp : p.sample (e ∘ levelEnumeration L)
          (he.comp (levelEnumeration_strictMono L)) =
          t.sample (levelEnumeration L) (levelEnumeration_strictMono L) := by
        rw [← Level.sample_comp e (levelEnumeration L)
          he (levelEnumeration_strictMono L) 0 n p]
        exact congrArg (Level.sample (levelEnumeration L) (levelEnumeration_strictMono L))
          (S.valuation_sample _ 0 t)
      rw [hsamp] at hmark
      unfold canonicalCompression
      rw [compressOn_mk]
      rw [V.mapNodeDefault_active _ hd]
      exact congrArg (fun q : Level A 0 (e (levelEnumeration L n)) =>
        (Node.mk (e (levelEnumeration L n)) q : Node A 0)) hmark

theorem marked_tuple_envelope_height {U : Type} {b : ℕ}
    (v : Fin b → Vertex A U) (H : ℕ) (hH : (tupleLevels v).card = H) :
    ∃ V : FiniteStrongVector A
        (e ∘ levelEnumeration (tupleLevels v))
        (he.comp (levelEnumeration_strictMono (tupleLevels v))) H,
      (∀ i n, V.nodes i n ⊆ S.nodes i (levelEnumeration (tupleLevels v) n)) ∧
      ∀ j, V.mapVertices (normalForm v j) = S.mapVertices (v j) := by
  subst H
  exact S.marked_tuple_envelope v

end StrongVector

end RelationalRamsey632.Source
