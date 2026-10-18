import RelationalRamsey632.Source.ValuationSampling

/-! Exact subtuple coherence, including repeated node projections. -/

namespace RelationalRamsey632.Source

theorem nested_levels_active_range (L Y : Finset ℕ) (hYL : Y ⊆ L) :
    (Y : Set ℕ) = Set.range (fun r : Fin Y.card =>
      levelEnumeration L
        (levelEnumeration (Y.image (levelIndex (levelEnumeration L))) r.val)) := by
  apply Set.Subset.antisymm
  · intro a ha
    obtain ⟨r, hr⟩ := levelEnumeration_range_contains Y ha
    have hrY : r < Y.card := (levelEnumeration_mem_iff Y r).mp (hr ▸ ha)
    exact ⟨⟨r, hrY⟩, (levelEnumeration_nested L Y hYL hrY).trans hr.symm⟩
  · rintro a ⟨r, rfl⟩
    change levelEnumeration L
      (levelEnumeration (Y.image (levelIndex (levelEnumeration L))) r.val) ∈ (Y : Set ℕ)
    rw [levelEnumeration_nested L Y hYL r.isLt]
    exact (levelEnumeration_mem_iff Y r.val).mpr r.isLt

theorem canonicalCompression_nested {A : ℕ → Type} (L Y : Finset ℕ)
    (hYL : Y ⊆ L) {i : ℕ} (t : Node A i) (ht : t.height ∈ Y) :
    canonicalCompression (Y.image (levelIndex (levelEnumeration L)))
      (canonicalCompression L t) = canonicalCompression Y t := by
  cases t with
  | mk a t =>
    obtain ⟨r, hr⟩ := levelEnumeration_range_contains Y ht
    have hrY : r < Y.card := (levelEnumeration_mem_iff Y r).mp (hr ▸ ht)
    let K := Y.image (levelIndex (levelEnumeration L))
    have halign := levelEnumeration_nested L Y hYL hrY
    have harg : a = levelEnumeration L (levelEnumeration K r) := hr.trans halign.symm
    clear hr
    subst a
    have hdirect := canonicalCompression_mk_of_range Y
      (levelEnumeration L ∘ levelEnumeration K)
      ((levelEnumeration_strictMono L).comp (levelEnumeration_strictMono K))
      Y.card (nested_levels_active_range L Y hYL) i r hrY t
    dsimp only [Function.comp_apply] at hdirect
    change canonicalCompression K
        (compressOn (levelEnumeration L) (levelEnumeration_strictMono L)
          (Node.mk (levelEnumeration L (levelEnumeration K r)) t)) =
      canonicalCompression Y (Node.mk (levelEnumeration L (levelEnumeration K r)) t)
    rw [compressOn_mk, hdirect]
    change compressOn (levelEnumeration K) (levelEnumeration_strictMono K)
        (Node.mk (levelEnumeration K r)
          (t.sample (levelEnumeration L) (levelEnumeration_strictMono L))) = _
    rw [compressOn_mk]
    apply congrArg (fun p : Level A i r => (Node.mk r p : Node A i))
    exact Level.sample_comp _ _ _ _ i r t

theorem subtuple_projections_subset {A : ℕ → Type} {U : Type} {b c : ℕ}
    (v : Fin b → U × Node A 0) (q : Fin c → Fin b) :
    tupleProjections (v ∘ q) ⊆ tupleProjections v := by
  rintro t ⟨j, rfl⟩
  exact ⟨q j, rfl⟩

theorem subtuple_levels_subset {A : ℕ → Type} {U : Type} {b c : ℕ}
    (v : Fin b → U × Node A 0) (q : Fin c → Fin b) :
    tupleLevels (v ∘ q) ⊆ tupleLevels v := by
  intro n hn
  change n ∈ (tupleLevels v : Set ℕ)
  rw [tupleLevels_coe]
  have hsource : n ∈ closureLevels A (tupleProjections (v ∘ q)) := by
    rw [← tupleLevels_coe]
    exact hn
  exact generated_mono A (subtuple_projections_subset v q) _ hsource

theorem normalForm_subtuple_projections {A : ℕ → Type} {U : Type} {b c : ℕ}
    (v : Fin b → U × Node A 0) (q : Fin c → Fin b) :
    tupleProjections (normalForm v ∘ q) =
      canonicalCompression (tupleLevels v) '' tupleProjections (v ∘ q) := by
  apply Set.Subset.antisymm
  · rintro t ⟨j, hj⟩
    exact ⟨(v (q j)).2, ⟨j, rfl⟩, hj⟩
  · rintro t ⟨s, ⟨j, hj⟩, hs⟩
    exact ⟨j, (congrArg (canonicalCompression (tupleLevels v)) hj).trans hs⟩

theorem normalForm_subtuple_levels {A : ℕ → Type} {U : Type} {b c : ℕ}
    (v : Fin b → U × Node A 0) (q : Fin c → Fin b) :
    tupleLevels (normalForm v ∘ q) =
      (tupleLevels (v ∘ q)).image (levelIndex (levelEnumeration (tupleLevels v))) := by
  have hgridY : ∀ i t, t ∈ closureNodes A (tupleProjections (v ∘ q)) i →
      ∃ n, t.height = levelEnumeration (tupleLevels v) n := by
    intro i t ht
    exact closure_levels_on_grid (tupleLevels v) (tupleLevels_coe v).symm i t
      (generated_mono A (subtuple_projections_subset v q) _ ht)
  have hcov := compression_closure_covariance
    (levelEnumeration_strictMono (tupleLevels v)) hgridY
  apply Finset.coe_injective
  rw [tupleLevels_coe, normalForm_subtuple_projections]
  change closureLevels A
      (compressOn (levelEnumeration (tupleLevels v))
        (levelEnumeration_strictMono (tupleLevels v)) '' tupleProjections (v ∘ q)) = _
  rw [hcov.2, Finset.coe_image, tupleLevels_coe]

/-- Compressing a tuple first and then selecting a subtuple has the same
normal form as selecting that subtuple first. No distinct-projection
assumption is imposed. -/
theorem normalForm_subtuple {A : ℕ → Type} {U : Type} {b c : ℕ}
    (v : Fin b → U × Node A 0) (q : Fin c → Fin b) :
    normalForm (normalForm v ∘ q) = normalForm (v ∘ q) := by
  funext j
  apply Prod.ext
  · rfl
  · change canonicalCompression (tupleLevels (normalForm v ∘ q))
        (canonicalCompression (tupleLevels v) (v (q j)).2) =
      canonicalCompression (tupleLevels (v ∘ q)) (v (q j)).2
    rw [normalForm_subtuple_levels]
    apply canonicalCompression_nested (tupleLevels v) (tupleLevels (v ∘ q))
      (subtuple_levels_subset v q)
    change (v (q j)).2.height ∈ (tupleLevels (v ∘ q) : Set ℕ)
    rw [tupleLevels_coe]
    exact Generated.height _ (Generated.generator _ ⟨j, rfl⟩)

end RelationalRamsey632.Source
