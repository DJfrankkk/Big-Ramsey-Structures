import RelationalRamsey632.Source.Compression
import RelationalRamsey632.Source.LevelIndex

namespace RelationalRamsey632.Source

theorem levelEnumeration_image (L : Finset ℕ) (e : ℕ → ℕ) (he : StrictMono e)
    {r : ℕ} (hr : r < L.card) :
    levelEnumeration (L.image e) r = e (levelEnumeration L r) := by
  classical
  have hc : (L.image e).card = L.card := Finset.card_image_of_injective L he.injective
  let f : Fin L.card → ℕ := fun n => e (L.orderEmbOfFin rfl n)
  have hf : f = (L.image e).orderEmbOfFin hc :=
    Finset.orderEmbOfFin_unique hc
      (fun n => Finset.mem_image.mpr ⟨_, L.orderEmbOfFin_mem rfl n, rfl⟩)
      (he.comp (L.orderEmbOfFin rfl).strictMono)
  rw [levelEnumeration_initial _ (hc ▸ hr), levelEnumeration_initial _ hr]
  have hh := congrFun hf ⟨r, hr⟩
  have hsame : (L.image e).orderEmbOfFin hc ⟨r, hr⟩
      = (L.image e).orderEmbOfFin rfl ⟨r, hc ▸ hr⟩ := by
    exact Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr rfl
  exact (hh.trans hsame).symm

/-- Any increasing enumeration of the exact finite retained level set
agrees with the canonical enumeration on every active index. -/
theorem levelEnumeration_eq_of_range (L : Finset ℕ) (f : ℕ → ℕ) (hf : StrictMono f)
    (h : ℕ) (hL : (L : Set ℕ) = Set.range (fun n : Fin h => f n.val)) :
    L.card = h ∧ ∀ r, r < h → levelEnumeration L r = f r := by
  classical
  have hrange : (Finset.univ.image (fun n : Fin h => f n.val)) = L := by
    apply Finset.coe_injective
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact hL.symm
  have hc : L.card = h := by
    have hinj : Function.Injective (fun n : Fin h => f n.val) := hf.injective.comp Fin.val_injective
    rw [← hrange, Finset.card_image_of_injective _ hinj,
      Finset.card_univ, Fintype.card_fin]
  have henum : (fun n : Fin h => f n.val) = L.orderEmbOfFin hc :=
    Finset.orderEmbOfFin_unique hc
      (fun n => show f n.val ∈ (L : Set ℕ) from by rw [hL]; exact ⟨n, rfl⟩)
      (hf.comp (fun _ _ hn => hn))
  refine ⟨hc, ?_⟩
  intro r hr
  rw [levelEnumeration_initial _ (hc ▸ hr)]
  have hh := congrFun henum ⟨r, hr⟩
  have hsame : L.orderEmbOfFin hc ⟨r, hr⟩ = L.orderEmbOfFin rfl ⟨r, hc ▸ hr⟩ := by
    exact Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr rfl
  exact (hh.trans hsame).symm

private def coordinateCast {m n : ℕ} (h : m = n) (s : Coordinate m) : Coordinate n := h ▸ s

@[simp] private theorem coordinateCast_val {m n : ℕ} (h : m = n) (s : Coordinate m) :
    (coordinateCast h s).val = s.val := by cases h; rfl

private theorem castLevel_apply_heq {A : ℕ → Type} {i m n : ℕ}
    (h : m = n) (t : Level A i m) (s : Coordinate m) :
    HEq ((cast (congrArg (Level A i) h) t) (coordinateCast h s)) (t s) := by
  cases h
  rfl

private theorem nodeCast_eq {A : ℕ → Type} {i m n : ℕ}
    (h : m = n) (t : Level A i m) :
    Node.mk m t = (Node.mk n (cast (congrArg (Level A i) h) t) : Node A i) := by
  cases h
  rfl

/-- Sampling depends only on the level map up to the sampled node height;
neither a canonical enumeration tail nor phantom vector data can matter. -/
theorem sample_eq_of_initial {A : ℕ → Type} (f g : ℕ → ℕ)
    (hf : StrictMono f) (hg : StrictMono g) (i n : ℕ)
    (hfg : ∀ k, k ≤ n → f k = g k) (t : Level A i (f n)) :
    t.sample f hf =
      (cast (congrArg (Level A i) (hfg n le_rfl)) t).sample g hg := by
  classical
  funext s
  apply eq_of_heq
  let hn := hfg n le_rfl
  have hc : coordinateCast hn (s.sample f hf) = s.sample g hg := by
    apply Subtype.ext
    rw [coordinateCast_val]
    change s.val.image f = s.val.image g
    apply Finset.image_congr
    intro k hk
    exact hfg k (Nat.le_of_lt (Finset.mem_range.mp (s.property.2 hk)))
  have heval : HEq
      ((cast (congrArg (Level A i) hn) t) (s.sample g hg)) (t (s.sample f hf)) := by
    rw [← hc]
    exact castLevel_apply_heq hn t (s.sample f hf)
  exact (Level.sample_apply_heq f hf t s).trans
    (heval.symm.trans (Level.sample_apply_heq g hg _ s).symm)

/-- Canonical compression agrees, node for node, with sampling along any
increasing enumeration of the same finite retained levels. -/
theorem canonicalCompression_mk_of_range {A : ℕ → Type}
    (L : Finset ℕ) (f : ℕ → ℕ) (hf : StrictMono f) (h : ℕ)
    (hL : (L : Set ℕ) = Set.range (fun k : Fin h => f k.val))
    (i n : ℕ) (hn : n < h) (t : Level A i (f n)) :
    canonicalCompression L (Node.mk (f n) t) = Node.mk n (t.sample f hf) := by
  classical
  have heq := (levelEnumeration_eq_of_range L f hf h hL).2
  have hfg : ∀ k, k ≤ n → f k = levelEnumeration L k :=
    fun k hk => (heq k (hk.trans_lt hn)).symm
  let t' : Level A i (levelEnumeration L n) := cast (congrArg (Level A i) (hfg n le_rfl)) t
  have hnode : Node.mk (f n) t = Node.mk (levelEnumeration L n) t' :=
    nodeCast_eq (hfg n le_rfl) t
  unfold canonicalCompression
  rw [hnode, compressOn_mk]
  exact congrArg (fun q : Level A i n => (Node.mk n q : Node A i))
    (sample_eq_of_initial f (levelEnumeration L) hf (levelEnumeration_strictMono L) i n hfg t).symm

/-- Nested compression enumerates the retained sublevels in the same
order, so forgetting vertices cannot change a normal form through a
different choice of level ranks. -/
theorem levelEnumeration_nested (L Y : Finset ℕ) (hYL : Y ⊆ L)
    {r : ℕ} (hr : r < Y.card) :
    levelEnumeration L
      (levelEnumeration (Y.image (levelIndex (levelEnumeration L))) r)
        = levelEnumeration Y r := by
  classical
  let f := levelEnumeration L
  let K := Y.image (levelIndex f)
  have hre : ∀ m ∈ Y, f (levelIndex f m) = m := by
    intro m hm
    exact (levelIndex_spec f (levelEnumeration_range_contains L (hYL hm))).symm
  have hinj : Set.InjOn (levelIndex f) (Y : Set ℕ) := by
    intro m hm n hn heq
    exact (hre m hm).symm.trans ((congrArg f heq).trans (hre n hn))
  have hcard : K.card = Y.card := Finset.card_image_iff.mpr hinj
  have himage : K.image f = Y := by
    change (Y.image (levelIndex f)).image f = Y
    rw [Finset.image_image]
    calc
      Y.image (fun m => f (levelIndex f m)) = Y.image id := by
        apply Finset.image_congr
        intro m hm
        exact hre m hm
      _ = Y := Finset.image_id
  have hh := levelEnumeration_image K f (levelEnumeration_strictMono L) (hcard ▸ hr)
  rw [himage] at hh
  exact hh.symm

end RelationalRamsey632.Source
