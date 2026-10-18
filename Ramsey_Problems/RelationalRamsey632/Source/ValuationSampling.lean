import RelationalRamsey632.Source.Valuations
import RelationalRamsey632.Source.NormalFormCoherence
import RelationalRamsey632.Source.EnumerationAlignment
import RelationalRamsey632.Source.ImageClosure

namespace RelationalRamsey632.Source

namespace Coordinate

theorem sample_comp (e f : ℕ → ℕ) (he : StrictMono e) (hf : StrictMono f)
    {n : ℕ} (s : Coordinate n) :
    (s.sample f hf).sample e he = s.sample (e ∘ f) (he.comp hf) := by
  apply Subtype.ext
  exact Finset.image_image

end Coordinate

namespace Level

theorem sample_comp {A : ℕ → Type} (e f : ℕ → ℕ)
    (he : StrictMono e) (hf : StrictMono f) (i n : ℕ)
    (t : Level A i (e (f n))) :
    (t.sample e he).sample f hf = t.sample (e ∘ f) (he.comp hf) := by
  funext s
  apply eq_of_heq
  exact (sample_apply_heq f hf (t.sample e he) s).trans
    ((sample_apply_heq e he t (s.sample f hf)).trans
      ((apply_heq t (Coordinate.sample_comp e f he hf s)).trans
        (sample_apply_heq (e ∘ f) (he.comp hf) t s).symm))

end Level

namespace StrongVector

variable {A : ℕ → Type} {e : ℕ → ℕ} {he : StrictMono e}
    (S : StrongVector A e he)

theorem valuation_sample (n i : ℕ) (t : Level A i n) :
    (S.valuation n i t).sample e he = t := by
  induction n generalizing i with
  | zero =>
    funext c
    obtain ⟨x, hx⟩ := c.property.1
    have h := c.property.2 hx
    simp at h
  | succ n ih =>
    apply Level.successor_ext
    · simpa only [Level.sample_restrict, S.valuation_step_restrict] using
        ih i (t.restrict (Nat.le_succ n))
    · exact (Level.sample_singleton e he (S.valuation (n + 1) i t)
        (Nat.lt_succ_self n)).trans (S.valuation_step_singleton n i t)
    · simpa only [Level.sample_slice, S.valuation_step_slice] using
        ih (i + 1) (t.slice (Nat.lt_succ_self n))

theorem levelImage_active_range (L : Finset ℕ) :
    (L.image e : Set ℕ) =
      Set.range (fun n : Fin L.card => e (levelEnumeration L n.val)) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨n, hn⟩ := levelEnumeration_range_contains L ha
    have hmem : n < L.card := (levelEnumeration_mem_iff L n).mp (hn ▸ ha)
    exact ⟨⟨n, hmem⟩, congrArg e hn.symm⟩
  · rintro x ⟨n, rfl⟩
    exact Finset.mem_image.mpr
      ⟨levelEnumeration L n.val, (levelEnumeration_mem_iff L n.val).mpr n.isLt, rfl⟩

theorem canonicalCompression_mapNode (L : Finset ℕ)
    {i : ℕ} (t : Node A i) (ht : t.height ∈ L) :
    canonicalCompression (L.image e) (S.mapNode t) = canonicalCompression L t := by
  cases t with
  | mk a t =>
    obtain ⟨n, hn⟩ := levelEnumeration_range_contains L ht
    dsimp only [Node.height] at hn
    subst a
    have hnL : n < L.card := (levelEnumeration_mem_iff L n).mp ht
    have hmarked := canonicalCompression_mk_of_range (L.image e)
      (e ∘ levelEnumeration L) (he.comp (levelEnumeration_strictMono L))
      L.card (levelImage_active_range (e := e) L) i n hnL
      (S.valuation (levelEnumeration L n) i t)
    dsimp only [Function.comp_apply] at hmarked
    change canonicalCompression (L.image e)
        (Node.mk (e (levelEnumeration L n)) (S.valuation (levelEnumeration L n) i t)) = _
    rw [hmarked]
    have hs := Level.sample_comp e (levelEnumeration L)
      he (levelEnumeration_strictMono L) i n
      (S.valuation (levelEnumeration L n) i t)
    rw [← hs, S.valuation_sample]
    exact (compressOn_mk (levelEnumeration L) (levelEnumeration_strictMono L) i n t).symm

noncomputable def mapVertices {U : Type} (v : U × Node A 0) : U × Node A 0 :=
  (v.1, S.mapNode v.2)

theorem mapVertices_projections {U : Type} {b : ℕ}
    (v : Fin b → U × Node A 0) :
    tupleProjections (S.mapVertices ∘ v) = S.mapNode '' tupleProjections v := by
  apply Set.Subset.antisymm
  · rintro t ⟨j, hj⟩
    exact ⟨(v j).2, ⟨j, rfl⟩, hj⟩
  · rintro t ⟨s, ⟨j, hj⟩, hs⟩
    exact ⟨j, (congrArg S.mapNode hj).trans hs⟩

theorem mapVertices_tupleLevels {U : Type} {b : ℕ}
    (v : Fin b → U × Node A 0) :
    tupleLevels (S.mapVertices ∘ v) = (tupleLevels v).image e := by
  apply Finset.coe_injective
  rw [tupleLevels_coe, S.mapVertices_projections, (S.closure_covariance _).2,
    Finset.coe_image, tupleLevels_coe]

theorem normalForm_mapVertices {U : Type} {b : ℕ}
    (v : Fin b → U × Node A 0) :
    normalForm (S.mapVertices ∘ v) = normalForm v := by
  funext j
  apply Prod.ext
  · rfl
  · change canonicalCompression (tupleLevels (S.mapVertices ∘ v))
      (S.mapNode (v j).2) = canonicalCompression (tupleLevels v) (v j).2
    rw [S.mapVertices_tupleLevels]
    apply S.canonicalCompression_mapNode
    change (v j).2.height ∈ (tupleLevels v : Set ℕ)
    rw [tupleLevels_coe]
    exact Generated.height _ (Generated.generator _ ⟨j, rfl⟩)

end StrongVector

end RelationalRamsey632.Source
