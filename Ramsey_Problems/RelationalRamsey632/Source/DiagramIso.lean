import RelationalRamsey632.Source.MarkedSampling
import Mathlib.Order.Hom.Set

/-!
# Actual marked intrinsic closure diagrams

An isomorphism consists of an increasing bijection of the retained levels and
sort-preserving bijections of the actual retained nodes.  It preserves height,
prefix, meet, restriction, full slice, and singleton values.  Normal-form
equality is a theorem about this record, not its definition.
-/

namespace RelationalRamsey632.Source

variable {A : ℕ → Type}

abbrev DiagramLevel (X : Set (Node A 0)) := {n : ℕ // n ∈ closureLevels A X}
abbrev DiagramNode (X : Set (Node A 0)) (i : ℕ) := {t : Node A i // t ∈ closureNodes A X i}

def diagramHeight {X : Set (Node A 0)} {i : ℕ} (t : DiagramNode X i) :
    DiagramLevel X := ⟨t.val.height, Generated.height _ t.property⟩

structure ClosureDiagramIso (X Y : Set (Node A 0)) where
  levels : DiagramLevel X ≃o DiagramLevel Y
  nodes : ∀ i, DiagramNode X i ≃ DiagramNode Y i
  height_eq : ∀ i (t : DiagramNode X i), (nodes i t).val.height = (levels (diagramHeight t)).val
  prefix_iff : ∀ i (s t : DiagramNode X i), Node.Prefix (nodes i s).val (nodes i t).val ↔
    Node.Prefix s.val t.val
  meet_eq : ∀ i (s t : DiagramNode X i),
    (nodes i ⟨s.val.meet t.val, Generated.meet _ _ s.property t.property⟩).val =
      (nodes i s).val.meet (nodes i t).val
  restrict_eq : ∀ i (t : DiagramNode X i) (n : DiagramLevel X) (h : n.val ≤ t.val.height)
      (h' : (levels n).val ≤ (nodes i t).val.height),
    (nodes i ⟨t.val.restrict n.val h,
      Generated.restrict _ _ t.property n.property h⟩).val =
      (nodes i t).val.restrict (levels n).val h'
  slice_eq : ∀ i (t : DiagramNode X i) (n : DiagramLevel X) (h : n.val < t.val.height)
      (h' : (levels n).val < (nodes i t).val.height),
    (nodes (i + 1) ⟨t.val.slice n.val h,
      Generated.slice _ _ t.property n.property h⟩).val =
      (nodes i t).val.slice (levels n).val h'
  singleton_eq : ∀ i (t : DiagramNode X i) (n : DiagramLevel X) (h : n.val < t.val.height)
      (h' : (levels n).val < (nodes i t).val.height),
    (nodes i t).val.singleton (levels n).val h' = t.val.singleton n.val h

namespace ClosureDiagramIso

variable {X Y Z : Set (Node A 0)}

theorem map_le (f : ClosureDiagramIso X Y) {i : ℕ} (t : DiagramNode X i)
    (n : DiagramLevel X) (h : n.val ≤ t.val.height) :
    (f.levels n).val ≤ (f.nodes i t).val.height := by
  rw [f.height_eq]
  exact f.levels.monotone h

theorem map_lt (f : ClosureDiagramIso X Y) {i : ℕ} (t : DiagramNode X i)
    (n : DiagramLevel X) (h : n.val < t.val.height) :
    (f.levels n).val < (f.nodes i t).val.height := by
  rw [f.height_eq]
  exact f.levels.strictMono h

def refl (X : Set (Node A 0)) : ClosureDiagramIso X X where
  levels := OrderIso.refl _
  nodes := fun _ => Equiv.refl _
  height_eq := fun _ _ => rfl
  prefix_iff := fun _ _ _ => Iff.rfl
  meet_eq := fun _ _ _ => rfl
  restrict_eq := fun _ _ _ _ _ => rfl
  slice_eq := fun _ _ _ _ _ => rfl
  singleton_eq := fun _ _ _ _ _ => rfl

def trans (f : ClosureDiagramIso X Y) (g : ClosureDiagramIso Y Z) :
    ClosureDiagramIso X Z where
  levels := f.levels.trans g.levels
  nodes := fun i => (f.nodes i).trans (g.nodes i)
  height_eq := by
    intro i t
    change (g.nodes i (f.nodes i t)).val.height = _
    rw [g.height_eq]
    congr 1
    exact congrArg g.levels (Subtype.ext (f.height_eq i t))
  prefix_iff := by
    intro i s t
    exact (g.prefix_iff i _ _).trans (f.prefix_iff i s t)
  meet_eq := by
    intro i s t
    change (g.nodes i (f.nodes i _)).val = _
    have hf : f.nodes i ⟨s.val.meet t.val, Generated.meet _ _ s.property t.property⟩ =
        ⟨(f.nodes i s).val.meet (f.nodes i t).val,
          Generated.meet _ _ (f.nodes i s).property (f.nodes i t).property⟩ :=
      Subtype.ext (f.meet_eq i s t)
    rw [hf]
    exact g.meet_eq i _ _
  restrict_eq := by
    intro i t n h h'
    change (g.nodes i (f.nodes i _)).val = _
    have hf : f.nodes i ⟨t.val.restrict n.val h,
        Generated.restrict _ _ t.property n.property h⟩ =
        ⟨(f.nodes i t).val.restrict (f.levels n).val (f.map_le t n h),
          Generated.restrict _ _ (f.nodes i t).property (f.levels n).property _⟩ :=
      Subtype.ext (f.restrict_eq i t n h (f.map_le t n h))
    rw [hf]
    exact g.restrict_eq i (f.nodes i t) (f.levels n) _ h'
  slice_eq := by
    intro i t n h h'
    change (g.nodes (i + 1) (f.nodes (i + 1) _)).val = _
    have hf : f.nodes (i + 1) ⟨t.val.slice n.val h,
        Generated.slice _ _ t.property n.property h⟩ =
        ⟨(f.nodes i t).val.slice (f.levels n).val (f.map_lt t n h),
          Generated.slice _ _ (f.nodes i t).property (f.levels n).property _⟩ :=
      Subtype.ext (f.slice_eq i t n h (f.map_lt t n h))
    rw [hf]
    exact g.slice_eq i (f.nodes i t) (f.levels n) _ h'
  singleton_eq := by
    intro i t n h h'
    exact (g.singleton_eq i (f.nodes i t) (f.levels n) (f.map_lt t n h) h').trans
      (f.singleton_eq i t n h (f.map_lt t n h))

end ClosureDiagramIso

namespace ClosureDiagramIso

variable {X Y : Set (Node A 0)}

theorem inverse_height (f : ClosureDiagramIso X Y) (i : ℕ) (t : DiagramNode Y i) :
    ((f.nodes i).symm t).val.height = (f.levels.symm (diagramHeight t)).val := by
  have hh : f.levels (diagramHeight ((f.nodes i).symm t)) = diagramHeight t := by
    apply Subtype.ext
    simpa only [Equiv.apply_symm_apply, diagramHeight] using
      (f.height_eq i ((f.nodes i).symm t)).symm
  have h := congrArg f.levels.symm hh
  simpa only [OrderIso.symm_apply_apply, diagramHeight] using congrArg Subtype.val h

def symm (f : ClosureDiagramIso X Y) : ClosureDiagramIso Y X where
  levels := f.levels.symm
  nodes := fun i => (f.nodes i).symm
  height_eq := f.inverse_height
  prefix_iff := by
    intro i s t
    have h : Node.Prefix s.val t.val ↔
        Node.Prefix ((f.nodes i).symm s).val ((f.nodes i).symm t).val := by
      simpa only [Equiv.apply_symm_apply] using
        (f.prefix_iff i ((f.nodes i).symm s) ((f.nodes i).symm t))
    exact h.symm
  meet_eq := by
    intro i s t
    let q : DiagramNode X i := ⟨((f.nodes i).symm s).val.meet ((f.nodes i).symm t).val,
      Generated.meet _ _ ((f.nodes i).symm s).property ((f.nodes i).symm t).property⟩
    have hq : f.nodes i q = ⟨s.val.meet t.val, Generated.meet _ _ s.property t.property⟩ := by
      apply Subtype.ext
      simpa only [Equiv.apply_symm_apply] using
        f.meet_eq i ((f.nodes i).symm s) ((f.nodes i).symm t)
    exact congrArg Subtype.val ((f.nodes i).symm_apply_eq.mpr hq.symm)
  restrict_eq := by
    intro i t n h h'
    let q : DiagramNode X i := ⟨((f.nodes i).symm t).val.restrict (f.levels.symm n).val h',
      Generated.restrict _ _ ((f.nodes i).symm t).property (f.levels.symm n).property h'⟩
    have h'' : (f.levels (f.levels.symm n)).val ≤
        (f.nodes i ((f.nodes i).symm t)).val.height := by simpa using h
    have hq : f.nodes i q = ⟨t.val.restrict n.val h,
        Generated.restrict _ _ t.property n.property h⟩ := by
      apply Subtype.ext
      simpa only [Equiv.apply_symm_apply, OrderIso.apply_symm_apply] using
        f.restrict_eq i ((f.nodes i).symm t) (f.levels.symm n) h' h''
    exact congrArg Subtype.val ((f.nodes i).symm_apply_eq.mpr hq.symm)
  slice_eq := by
    intro i t n h h'
    let q : DiagramNode X (i + 1) := ⟨((f.nodes i).symm t).val.slice (f.levels.symm n).val h',
      Generated.slice _ _ ((f.nodes i).symm t).property (f.levels.symm n).property h'⟩
    have h'' : (f.levels (f.levels.symm n)).val <
        (f.nodes i ((f.nodes i).symm t)).val.height := by simpa using h
    have hq : f.nodes (i + 1) q = ⟨t.val.slice n.val h,
        Generated.slice _ _ t.property n.property h⟩ := by
      apply Subtype.ext
      simpa only [Equiv.apply_symm_apply, OrderIso.apply_symm_apply] using
        f.slice_eq i ((f.nodes i).symm t) (f.levels.symm n) h' h''
    exact congrArg Subtype.val ((f.nodes (i + 1)).symm_apply_eq.mpr hq.symm)
  singleton_eq := by
    intro i t n h h'
    have h'' : (f.levels (f.levels.symm n)).val <
        (f.nodes i ((f.nodes i).symm t)).val.height := by simpa using h
    simpa only [Equiv.apply_symm_apply, OrderIso.apply_symm_apply] using
      (f.singleton_eq i ((f.nodes i).symm t) (f.levels.symm n) h' h'').symm

end ClosureDiagramIso

theorem diagramLevel_mem {X : Set (Node A 0)} (L : Finset ℕ)
    (hL : closureLevels A X = (L : Set ℕ)) (n : DiagramLevel X) : n.val ∈ L := by
  change n.val ∈ (L : Set ℕ)
  rw [← hL]
  exact n.property

theorem compression_restrict {X : Set (Node A 0)} (L : Finset ℕ)
    (hL : closureLevels A X = (L : Set ℕ)) {i : ℕ} (t : DiagramNode X i)
    (n : DiagramLevel X) (h : n.val ≤ t.val.height)
    (h' : levelIndex (levelEnumeration L) n.val ≤ (canonicalCompression L t.val).height) :
    canonicalCompression L (t.val.restrict n.val h) =
      (canonicalCompression L t.val).restrict (levelIndex (levelEnumeration L) n.val) h' := by
  obtain ⟨k, hk⟩ := levelEnumeration_range_contains L (diagramLevel_mem L hL n)
  obtain ⟨m, hm⟩ := closure_levels_on_grid L hL i t.val t.property
  rcases t with ⟨⟨a, p⟩, ht⟩
  dsimp only [Node.height] at hm
  subst a
  rcases n with ⟨z, hz⟩
  change z = levelEnumeration L k at hk
  subst z
  have hkm : k ≤ m := (levelEnumeration_strictMono L).le_iff_le.mp h
  simp only [levelIndex_apply _ (levelEnumeration_strictMono L)] at h' ⊢
  simpa only [canonicalCompression, compressOn_mk] using
    compressOn_restrict_mk (levelEnumeration L) (levelEnumeration_strictMono L) i m k p hkm

theorem compression_slice {X : Set (Node A 0)} (L : Finset ℕ)
    (hL : closureLevels A X = (L : Set ℕ)) {i : ℕ} (t : DiagramNode X i)
    (n : DiagramLevel X) (h : n.val < t.val.height)
    (h' : levelIndex (levelEnumeration L) n.val < (canonicalCompression L t.val).height) :
    canonicalCompression L (t.val.slice n.val h) =
      (canonicalCompression L t.val).slice (levelIndex (levelEnumeration L) n.val) h' := by
  obtain ⟨k, hk⟩ := levelEnumeration_range_contains L (diagramLevel_mem L hL n)
  obtain ⟨m, hm⟩ := closure_levels_on_grid L hL i t.val t.property
  rcases t with ⟨⟨a, p⟩, ht⟩
  dsimp only [Node.height] at hm
  subst a
  rcases n with ⟨z, hz⟩
  change z = levelEnumeration L k at hk
  subst z
  have hkm : k < m := (levelEnumeration_strictMono L).lt_iff_lt.mp h
  simp only [levelIndex_apply _ (levelEnumeration_strictMono L)] at h' ⊢
  simpa only [canonicalCompression, compressOn_mk] using
    compressOn_slice_mk (levelEnumeration L) (levelEnumeration_strictMono L) i m k p hkm

theorem compression_singleton {X : Set (Node A 0)} (L : Finset ℕ)
    (hL : closureLevels A X = (L : Set ℕ)) {i : ℕ} (t : DiagramNode X i)
    (n : DiagramLevel X) (h : n.val < t.val.height)
    (h' : levelIndex (levelEnumeration L) n.val < (canonicalCompression L t.val).height) :
    (canonicalCompression L t.val).singleton (levelIndex (levelEnumeration L) n.val) h' =
      t.val.singleton n.val h := by
  obtain ⟨k, hk⟩ := levelEnumeration_range_contains L (diagramLevel_mem L hL n)
  obtain ⟨m, hm⟩ := closure_levels_on_grid L hL i t.val t.property
  rcases t with ⟨⟨a, p⟩, ht⟩
  dsimp only [Node.height] at hm
  subst a
  rcases n with ⟨z, hz⟩
  change z = levelEnumeration L k at hk
  subst z
  have hkm : k < m := (levelEnumeration_strictMono L).lt_iff_lt.mp h
  simp only [levelIndex_apply _ (levelEnumeration_strictMono L)] at h' ⊢
  simpa only [canonicalCompression, compressOn_mk] using
    compressOn_singleton_mk (levelEnumeration L) (levelEnumeration_strictMono L) i m k p hkm

noncomputable def compressionLevelIso {X Y : Set (Node A 0)} (L : Finset ℕ)
    (hL : closureLevels A X = (L : Set ℕ))
    (hY : Y = canonicalCompression L '' X) : DiagramLevel X ≃o DiagramLevel Y := by
  have hcov : closureLevels A Y = levelIndex (levelEnumeration L) '' closureLevels A X := by
    rw [hY]
    exact (compression_closure_covariance (levelEnumeration_strictMono L)
      (closure_levels_on_grid L hL)).2
  let f : DiagramLevel X → DiagramLevel Y := fun n =>
    ⟨levelIndex (levelEnumeration L) n.val, hcov ▸ ⟨n.val, n.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro m n h
      apply Subtype.ext
      have hmn := congrArg Subtype.val h
      have hm := levelIndex_spec (levelEnumeration L)
        (levelEnumeration_range_contains L (diagramLevel_mem L hL m))
      have hn := levelIndex_spec (levelEnumeration L)
        (levelEnumeration_range_contains L (diagramLevel_mem L hL n))
      exact hm.trans ((congrArg (levelEnumeration L) hmn).trans hn.symm)
    · intro n
      have hn : n.val ∈ levelIndex (levelEnumeration L) '' closureLevels A X := by
        rw [← hcov]
        exact n.property
      obtain ⟨m, hm, hmn⟩ := hn
      exact ⟨⟨m, hm⟩, Subtype.ext hmn⟩
  exact
    { toEquiv := Equiv.ofBijective f hf
      map_rel_iff' := by
        intro m n
        exact levelIndex_compare _ (levelEnumeration_strictMono L)
          (levelEnumeration_range_contains L (diagramLevel_mem L hL m))
          (levelEnumeration_range_contains L (diagramLevel_mem L hL n)) }

@[simp] theorem compressionLevelIso_apply {X Y : Set (Node A 0)} (L : Finset ℕ)
    (hL : closureLevels A X = (L : Set ℕ))
    (hY : Y = canonicalCompression L '' X) (n : DiagramLevel X) :
    (compressionLevelIso L hL hY n).val = levelIndex (levelEnumeration L) n.val := rfl

noncomputable def compressionNodeIso {X Y : Set (Node A 0)} (L : Finset ℕ)
    (hL : closureLevels A X = (L : Set ℕ))
    (hY : Y = canonicalCompression L '' X) (i : ℕ) : DiagramNode X i ≃ DiagramNode Y i := by
  have hcov : closureNodes A Y i = canonicalCompression L '' closureNodes A X i := by
    rw [hY]
    exact (canonical_compression_closure L hL).1 i
  let f : DiagramNode X i → DiagramNode Y i := fun t =>
    ⟨canonicalCompression L t.val, hcov ▸ ⟨t.val, t.property, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro s t h
    apply Subtype.ext
    exact canonicalCompression_injective_on_closure L hL i s.property t.property
      (congrArg Subtype.val h)
  · intro t
    have ht : t.val ∈ canonicalCompression L '' closureNodes A X i := by
      rw [← hcov]
      exact t.property
    obtain ⟨s, hs, hst⟩ := ht
    exact ⟨⟨s, hs⟩, Subtype.ext hst⟩

@[simp] theorem compressionNodeIso_apply {X Y : Set (Node A 0)} (L : Finset ℕ)
    (hL : closureLevels A X = (L : Set ℕ))
    (hY : Y = canonicalCompression L '' X) (i : ℕ) (t : DiagramNode X i) :
    (compressionNodeIso L hL hY i t).val = canonicalCompression L t.val := rfl

noncomputable def compressionDiagramIso {X Y : Set (Node A 0)} (L : Finset ℕ)
    (hL : closureLevels A X = (L : Set ℕ))
    (hY : Y = canonicalCompression L '' X) : ClosureDiagramIso X Y where
  levels := compressionLevelIso L hL hY
  nodes := compressionNodeIso L hL hY
  height_eq := by
    intro i t
    simpa only [compressionNodeIso_apply, compressionLevelIso_apply, diagramHeight,
      canonicalCompression] using
      compressOn_height _ (levelEnumeration_strictMono L) t.val
        (closure_levels_on_grid L hL i t.val t.property)
  prefix_iff := by
    intro i s t
    change Node.Prefix (canonicalCompression L s.val) (canonicalCompression L t.val) ↔ _
    have hc := compressOn_meet (levelEnumeration_strictMono L)
      (closureNodes A X) (closureLevels A X) (generatedClosure_closed A X)
      (closure_levels_on_grid L hL) s.property t.property
    change canonicalCompression L (s.val.meet t.val) =
      (canonicalCompression L s.val).meet (canonicalCompression L t.val) at hc
    constructor
    · intro h
      have hm := canonicalCompression_injective_on_closure L hL i
        (Generated.meet _ _ s.property t.property) s.property
        (hc.trans (Node.meet_eq_left_of_prefix h))
      simpa only [hm] using Node.meet_prefix_right s.val t.val
    · intro h
      have hm : (canonicalCompression L s.val).meet (canonicalCompression L t.val) =
          canonicalCompression L s.val := hc.symm.trans
        (congrArg (canonicalCompression L) (Node.meet_eq_left_of_prefix h))
      simpa only [hm] using
        Node.meet_prefix_right (canonicalCompression L s.val) (canonicalCompression L t.val)
  meet_eq := by
    intro i s t
    exact compressOn_meet (levelEnumeration_strictMono L)
      (closureNodes A X) (closureLevels A X) (generatedClosure_closed A X)
      (closure_levels_on_grid L hL) s.property t.property
  restrict_eq := by
    intro i t n h h'
    simp only [compressionNodeIso_apply, compressionLevelIso_apply] at h' ⊢
    exact compression_restrict L hL t n h h'
  slice_eq := by
    intro i t n h h'
    simp only [compressionNodeIso_apply, compressionLevelIso_apply] at h' ⊢
    exact compression_slice L hL t n h h'
  singleton_eq := by
    intro i t n h h'
    simp only [compressionNodeIso_apply, compressionLevelIso_apply] at h' ⊢
    exact compression_singleton L hL t n h h'

variable {U : Type} {b : ℕ}

structure MarkedDiagramIso (v w : Fin b → U × Node A 0)
    extends ClosureDiagramIso (tupleProjections v) (tupleProjections w) where
  labels_eq : ∀ j, (v j).1 = (w j).1
  marks_eq : ∀ j,
    (nodes 0 ⟨(v j).2, Generated.generator _ ⟨j, rfl⟩⟩).val = (w j).2

namespace MarkedDiagramIso

variable {v w z : Fin b → U × Node A 0}

def refl (v : Fin b → U × Node A 0) : MarkedDiagramIso v v where
  toClosureDiagramIso := ClosureDiagramIso.refl _
  labels_eq := fun _ => rfl
  marks_eq := fun _ => rfl

def trans (f : MarkedDiagramIso v w) (g : MarkedDiagramIso w z) :
    MarkedDiagramIso v z where
  toClosureDiagramIso := f.toClosureDiagramIso.trans g.toClosureDiagramIso
  labels_eq := fun j => (f.labels_eq j).trans (g.labels_eq j)
  marks_eq := by
    intro j
    change (g.nodes 0 (f.nodes 0 _)).val = _
    have hf : f.nodes 0 ⟨(v j).2, Generated.generator _ ⟨j, rfl⟩⟩ =
        ⟨(w j).2, Generated.generator _ ⟨j, rfl⟩⟩ := Subtype.ext (f.marks_eq j)
    rw [hf]
    exact g.marks_eq j

def symm (f : MarkedDiagramIso v w) : MarkedDiagramIso w v where
  toClosureDiagramIso := f.toClosureDiagramIso.symm
  labels_eq := fun j => (f.labels_eq j).symm
  marks_eq := by
    intro j
    have hf : f.nodes 0 ⟨(v j).2, Generated.generator _ ⟨j, rfl⟩⟩ =
        ⟨(w j).2, Generated.generator _ ⟨j, rfl⟩⟩ := Subtype.ext (f.marks_eq j)
    exact congrArg Subtype.val ((f.nodes 0).symm_apply_eq.mpr hf.symm)

noncomputable def compression (v : Fin b → U × Node A 0) :
    MarkedDiagramIso v (normalForm v) where
  toClosureDiagramIso := compressionDiagramIso (tupleLevels v) (tupleLevels_coe v).symm
    (normalForm_projections v)
  labels_eq := fun _ => rfl
  marks_eq := fun _ => rfl

/-- Ordered marks force the image of every retained node and level through
the actual derivations of the least closure. -/
theorem maps_unique (f g : MarkedDiagramIso v w) :
    (∀ i t, (f.nodes i t).val = (g.nodes i t).val) ∧
      (∀ n, (f.levels n).val = (g.levels n).val) := by
  have hu : ∀ x (hx : Generated A (tupleProjections v) x),
      match x with
      | .inl ⟨i, t⟩ => (f.nodes i ⟨t, hx⟩).val = (g.nodes i ⟨t, hx⟩).val
      | .inr n => (f.levels ⟨n, hx⟩).val = (g.levels ⟨n, hx⟩).val := by
    intro x hx
    induction hx with
    | generator t ht =>
      obtain ⟨j, rfl⟩ := ht
      exact (f.marks_eq j).trans (g.marks_eq j).symm
    | height t ht ih =>
      exact (f.height_eq _ ⟨t, ht⟩).symm.trans
        ((congrArg Node.height ih).trans (g.height_eq _ ⟨t, ht⟩))
    | meet s t hs ht ihs iht =>
      exact (f.meet_eq _ ⟨s, hs⟩ ⟨t, ht⟩).trans
        ((congrArg₂ Node.meet ihs iht).trans (g.meet_eq _ ⟨s, hs⟩ ⟨t, ht⟩).symm)
    | restrict t n ht hn h iht ihn =>
      dsimp only at iht ihn ⊢
      rw [f.restrict_eq _ ⟨t, ht⟩ ⟨n, hn⟩ h (f.toClosureDiagramIso.map_le _ _ h),
        g.restrict_eq _ ⟨t, ht⟩ ⟨n, hn⟩ h (g.toClosureDiagramIso.map_le _ _ h)]
      simp only [iht, ihn]
    | slice t n ht hn h iht ihn =>
      dsimp only at iht ihn ⊢
      rw [f.slice_eq _ ⟨t, ht⟩ ⟨n, hn⟩ h (f.toClosureDiagramIso.map_lt _ _ h),
        g.slice_eq _ ⟨t, ht⟩ ⟨n, hn⟩ h (g.toClosureDiagramIso.map_lt _ _ h)]
      simp only [iht, ihn]
  exact ⟨fun i t => hu _ t.property, fun n => hu _ n.property⟩

theorem unique (f g : MarkedDiagramIso v w) : f = g := by
  have hn : f.nodes = g.nodes := by
    funext i
    apply Equiv.ext
    intro t
    exact Subtype.ext ((maps_unique f g).1 i t)
  have hl : f.levels = g.levels := by
    apply OrderIso.ext
    funext n
    exact Subtype.ext ((maps_unique f g).2 n)
  cases f
  cases g
  rename_i fc fl fm gc gl gm
  cases fc
  cases gc
  simp_all only

end MarkedDiagramIso

noncomputable def consecutiveLevelIso {X : Set (Node A 0)} (H : ℕ)
    (hX : closureLevels A X = (Finset.range H : Set ℕ)) : DiagramLevel X ≃o Fin H where
  toFun n := ⟨n.val, by
    have hn : n.val ∈ (Finset.range H : Set ℕ) := by rw [← hX]; exact n.property
    exact Finset.mem_range.mp hn⟩
  invFun n := ⟨n.val, hX.symm ▸ Finset.mem_range.mpr n.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem consecutive_iso_levels {X Y : Set (Node A 0)} {H K : ℕ}
    (hX : closureLevels A X = (Finset.range H : Set ℕ))
    (hY : closureLevels A Y = (Finset.range K : Set ℕ)) (f : ClosureDiagramIso X Y) :
    H = K ∧ ∀ n, (f.levels n).val = n.val := by
  let e := ((consecutiveLevelIso H hX).symm.trans f.levels).trans
    (consecutiveLevelIso K hY)
  have hHK : H = K := by
    simpa only [Fintype.card_fin] using Fintype.card_congr e.toEquiv
  subst K
  refine ⟨rfl, ?_⟩
  have hsets : closureLevels A X = closureLevels A Y := hX.trans hY.symm
  let g : DiagramLevel X ≃o DiagramLevel Y := OrderIso.setCongr _ _ hsets
  have hfg : f.levels = g := Subsingleton.elim _ _
  intro n
  rw [hfg]
  rfl

theorem node_successor_ext {i n : ℕ} (s t : Node A i)
    (hs : s.height = n + 1) (ht : t.height = n + 1)
    (hp : s.restrict n (by omega) = t.restrict n (by omega))
    (ha : s.singleton n (by omega) = t.singleton n (by omega))
    (hv : s.slice n (by omega) = t.slice n (by omega)) : s = t := by
  cases s with
  | mk a s =>
    cases t with
    | mk b t =>
      dsimp only [Node.height] at hs ht
      subst a
      subst b
      exact congrArg (Node.mk (n + 1)) (Level.successor_ext s t
        (Node.mk_injective n hp) ha (Node.mk_injective n hv))

/-- On consecutive retained levels, the preservation of predecessor, full
slice, and singleton values forces every node to be fixed literally. -/
theorem consecutive_iso_nodes {X Y : Set (Node A 0)} {H : ℕ}
    (hX : closureLevels A X = (Finset.range H : Set ℕ)) (f : ClosureDiagramIso X Y)
    (hl : ∀ n, (f.levels n).val = n.val) :
    ∀ i t, (f.nodes i t).val = t.val := by
  have hh : ∀ i t, (f.nodes i t).val.height = t.val.height := by
    intro i t
    exact (f.height_eq i t).trans (hl (diagramHeight t))
  have hu : ∀ n i (t : DiagramNode X i), t.val.height = n → (f.nodes i t).val = t.val := by
    intro n
    induction n with
    | zero =>
      intro i t ht
      exact (Node.height_zero_unique ((f.nodes i t).val) ((hh i t).trans ht)).trans
        (Node.height_zero_unique t.val ht).symm
    | succ n ih =>
      intro i t ht
      have hnH : n < H := by
        have hn : t.val.height ∈ (Finset.range H : Set ℕ) :=
          hX ▸ (Generated.height _ t.property)
        have hlt := Finset.mem_range.mp hn
        omega
      let k : DiagramLevel X := ⟨n, hX.symm ▸ Finset.mem_range.mpr hnH⟩
      have hle : n ≤ t.val.height := by omega
      have hlt : n < t.val.height := by omega
      let p : DiagramNode X i := ⟨t.val.restrict n hle,
        Generated.restrict _ _ t.property k.property hle⟩
      let q : DiagramNode X (i + 1) := ⟨t.val.slice n hlt,
        Generated.slice _ _ t.property k.property hlt⟩
      have hp := ih i p rfl
      have hq := ih (i + 1) q rfl
      have hp' : (f.nodes i t).val.restrict n (by rw [hh]; exact hle) =
          t.val.restrict n hle := by
        have hr : (f.nodes i p).val = (f.nodes i t).val.restrict n
            (by rw [hh]; exact hle) := by
          simpa only [hl] using f.restrict_eq i t k hle (f.map_le t k hle)
        exact hr.symm.trans hp
      have hq' : (f.nodes i t).val.slice n (by rw [hh]; exact hlt) =
          t.val.slice n hlt := by
        have hr : (f.nodes (i + 1) q).val = (f.nodes i t).val.slice n
            (by rw [hh]; exact hlt) := by
          simpa only [hl] using f.slice_eq i t k hlt (f.map_lt t k hlt)
        exact hr.symm.trans hq
      have ha : (f.nodes i t).val.singleton n (by rw [hh]; exact hlt) =
          t.val.singleton n hlt := by
        simpa only [hl] using f.singleton_eq i t k hlt (f.map_lt t k hlt)
      exact node_successor_ext _ _ ((hh i t).trans ht) ht hp' ha hq'
  exact fun i t => hu t.val.height i t rfl

namespace MarkedDiagramIso

variable {v w : Fin b → U × Node A 0}

theorem normalForm_eq (f : MarkedDiagramIso v w) : normalForm v = normalForm w := by
  let g := ((compression v).symm.trans f).trans (compression w)
  have hx : closureLevels A (tupleProjections (normalForm v)) =
      (Finset.range (tupleLevels v).card : Set ℕ) := by
    rw [← tupleLevels_coe, tupleLevels_normalForm]
  have hy : closureLevels A (tupleProjections (normalForm w)) =
      (Finset.range (tupleLevels w).card : Set ℕ) := by
    rw [← tupleLevels_coe, tupleLevels_normalForm]
  have hl := (consecutive_iso_levels hx hy g.toClosureDiagramIso).2
  have hn := consecutive_iso_nodes hx g.toClosureDiagramIso hl
  funext j
  apply Prod.ext
  · exact g.labels_eq j
  · exact (hn 0 ⟨(normalForm v j).2, Generated.generator _ ⟨j, rfl⟩⟩).symm.trans
      (g.marks_eq j)

noncomputable def ofNormalFormEq (h : normalForm v = normalForm w) :
    MarkedDiagramIso v w :=
  (compression v).trans ((h ▸ compression w).symm)

end MarkedDiagramIso

/-- Literal normal forms classify actual marked intrinsic closure diagrams.
No finiteness assumption on the alphabets or on the label set is needed. -/
theorem marked_diagram_iso_iff_normalForm_eq (v w : Fin b → U × Node A 0) :
    Nonempty (MarkedDiagramIso v w) ↔ normalForm v = normalForm w := by
  constructor
  · rintro ⟨f⟩
    exact f.normalForm_eq
  · intro h
    exact ⟨MarkedDiagramIso.ofNormalFormEq h⟩

theorem marked_diagram_iso_existsUnique (v w : Fin b → U × Node A 0)
    (h : normalForm v = normalForm w) : ∃! _f : MarkedDiagramIso v w, True :=
  ⟨MarkedDiagramIso.ofNormalFormEq h, trivial, fun f _ => MarkedDiagramIso.unique f _⟩

end RelationalRamsey632.Source




