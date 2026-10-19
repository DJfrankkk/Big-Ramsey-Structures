import RelationalRamsey632.Transfer.BigRamsey

namespace RelationalRamsey632.Transfer

open RelStructure

variable {L S : Language} {A X : Type}

def paletteAction {a : RelStructure L A} {K : RelStructure L X}
    (Y : RelStructure S X) (σ : automorphismGroup a) (p : palette a K Y) :
    palette a K Y := by
  refine ⟨p.val.pullback σ.val.symm, ?_⟩
  obtain ⟨e, he⟩ := p.property
  exact ⟨e.comp (automorphismEmbedding σ⁻¹), congrArg (fun z => z.pullback σ.val.symm) he⟩

instance paletteMulAction {a : RelStructure L A} {K : RelStructure L X}
    (Y : RelStructure S X) : MulAction (automorphismGroup a) (palette a K Y) where
  smul := paletteAction Y
  one_smul p := by
    apply Subtype.ext
    exact pullback_id p.val
  mul_smul σ τ p := by
    apply Subtype.ext
    rfl

instance embeddingMulAction {a : RelStructure L A} {K : RelStructure L X} :
    MulAction (automorphismGroup a) (RelEmbedding a K) where
  smul σ e := e.comp (automorphismEmbedding σ⁻¹)
  one_smul e := by
    ext x
    rfl
  mul_smul σ τ e := by
    ext x
    rfl

theorem palette_type_equivariant {a : RelStructure L A} {K : RelStructure L X}
    (Y : RelStructure S X) (σ : automorphismGroup a) (e : RelEmbedding a K) :
    (⟨Y.pullback (σ • e : RelEmbedding a K), ⟨σ • e, rfl⟩⟩ : palette a K Y)
      = σ • (⟨Y.pullback e, ⟨e, rfl⟩⟩ : palette a K Y) := rfl

theorem palette_action_free {a : RelStructure L A} {K : RelStructure L X}
    (Y : RelStructure S X) (hr : ∀ p ∈ palette a K Y, Rigid p) :
    ∀ (σ : automorphismGroup a) (p : palette a K Y), σ • p = p → σ = 1 := by
  intro σ p h
  have hh : p.val.pullback σ.val.symm = p.val := congrArg Subtype.val h
  have hi := hr p.val p.property σ.val.symm hh
  apply Subtype.ext
  exact inv_eq_one.mp hi

theorem palette_orbit_card [Finite A]
    {a : RelStructure L A} {K : RelStructure L X}
    (Y : RelStructure S X) (hfin : (palette a K Y).Finite)
    (hr : ∀ p ∈ palette a K Y, Rigid p) :
    Nat.card (MulAction.orbitRel.Quotient (automorphismGroup a) (palette a K Y))
      = (palette a K Y).ncard / Nat.card (automorphismGroup a) := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype (palette a K Y) := hfin.fintype
  letI : Fintype (automorphismGroup a) := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card, Set.fintypeCard_eq_ncard] using
    RamseyCommon.OrbitCounting.free_action_orbit_card_div (palette_action_free Y hr)

def Copies (a : RelStructure L A) (K : RelStructure L X) : Type :=
  Set.range (fun e : RelEmbedding a K => Set.range e)

def copyOf {a : RelStructure L A} {K : RelStructure L X} (e : RelEmbedding a K) :
    Copies a K := ⟨Set.range e, ⟨e, rfl⟩⟩

noncomputable def copyWitness {a : RelStructure L A} {K : RelStructure L X}
    (F : Copies a K) : RelEmbedding a K := Classical.choose F.property

theorem copyWitness_range {a : RelStructure L A} {K : RelStructure L X}
    (F : Copies a K) : Set.range (copyWitness F) = F.val := Classical.choose_spec F.property

theorem copyOf_witness {a : RelStructure L A} {K : RelStructure L X}
    (F : Copies a K) : copyOf (copyWitness F) = F := Subtype.ext (copyWitness_range F)

noncomputable def copyMap {a : RelStructure L A} {K : RelStructure L X}
    (g : RelEmbedding K K) (F : Copies a K) : Copies a K :=
  copyOf (g.comp (copyWitness F))

/-- Equality of copy images is exactly a relabelling by an actual base
automorphism. No finiteness of the base language is used. -/
theorem same_range_automorphism {a : RelStructure L A} {K : RelStructure L X}
    (e f : RelEmbedding a K) (h : Set.range e = Set.range f) :
    ∃ σ : automorphismGroup a, e.comp (automorphismEmbedding σ) = f := by
  classical
  have hex : ∀ x, ∃ y, e y = f x := by
    intro x
    have hx : f x ∈ Set.range e := h ▸ ⟨x, rfl⟩
    exact hx
  let s : A → A := fun x => Classical.choose (hex x)
  have hs : ∀ x, e (s x) = f x := fun x => Classical.choose_spec (hex x)
  have hinj : Function.Injective s := by
    intro x y hxy
    apply f.injective
    exact (hs x).symm.trans ((congrArg e hxy).trans (hs y))
  have hsurj : Function.Surjective s := by
    intro y
    have hy : e y ∈ Set.range f := h ▸ ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, e.injective ((hs x).trans hx)⟩
  let σ := Equiv.ofBijective s ⟨hinj, hsurj⟩
  have hσ : a.pullback σ = a := by
    apply RelStructure.ext_rel
    intro r R t
    have heq : e ∘ σ ∘ t = f ∘ t := by
      funext j
      exact hs (t j)
    exact (e.map_rel R (σ ∘ t)).trans (heq ▸ (f.map_rel R t).symm)
  refine ⟨⟨σ, hσ⟩, ?_⟩
  ext x
  exact hs x

theorem precompose_range {a : RelStructure L A} {K : RelStructure L X}
    (σ : automorphismGroup a) (e : RelEmbedding a K) :
    Set.range (σ • e) = Set.range e := by
  apply Set.ext
  intro x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨σ.val.symm y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨σ.val y, by simp [HSMul.hSMul, SMul.smul, automorphismEmbedding]⟩

theorem copyMap_of {a : RelStructure L A} {K : RelStructure L X}
    (g : RelEmbedding K K) (e : RelEmbedding a K) :
    copyMap g (copyOf e) = copyOf (g.comp e) := by
  apply Subtype.ext
  change Set.range (g.comp (copyWitness (copyOf e))) = Set.range (g.comp e)
  have hw := copyWitness_range (copyOf e)
  have hr (v : RelEmbedding a K) : Set.range (g.comp v) = g '' Set.range v := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨v y, ⟨y, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, rfl⟩
  rw [hr, hr, hw]
  rfl

def CopyDegreeBound (a : RelStructure L A) (K : RelStructure L X) (t : ℕ) : Prop :=
  RamseyCommon.Palette.DegreeBound
    (fun (g : RelEmbedding K K) (F : Copies a K) => copyMap g F) t

def ExactCopyDegree (a : RelStructure L A) (K : RelStructure L X) (t : ℕ) : Prop :=
  CopyDegreeBound a K t ∧ ∀ s, CopyDegreeBound a K s → t ≤ s

theorem copy_degree_bound_of_embedding_bound {a : RelStructure L A} {K : RelStructure L X}
    {t : ℕ} (h : EmbeddingDegreeBound a K t) : CopyDegreeBound a K t := by
  intro D _ c
  obtain ⟨g, colors, hcard, hcolors⟩ := h D (fun e => c (copyOf e))
  exact ⟨g, colors, hcard, fun F => hcolors (copyWitness F)⟩

def orbitOf {a : RelStructure L A} {K : RelStructure L X}
    (Y : RelStructure S X) (e : RelEmbedding a K) :
    MulAction.orbitRel.Quotient (automorphismGroup a) (palette a K Y) :=
  Quotient.mk'' (⟨Y.pullback e, ⟨e, rfl⟩⟩ : palette a K Y)

theorem same_range_orbit {a : RelStructure L A} {K : RelStructure L X}
    (Y : RelStructure S X) (e f : RelEmbedding a K)
    (h : Set.range e = Set.range f) : orbitOf Y e = orbitOf Y f := by
  obtain ⟨σ, hσ⟩ := same_range_automorphism e f h
  have ht : (⟨Y.pullback f, ⟨f, rfl⟩⟩ : palette a K Y)
      = σ⁻¹ • (⟨Y.pullback e, ⟨e, rfl⟩⟩ : palette a K Y) := by
    rw [← hσ]
    rfl
  apply Eq.symm
  apply Quotient.sound
  exact MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨σ⁻¹, ht.symm⟩)

noncomputable def copyType {a : RelStructure L A} {K : RelStructure L X}
    (Y : RelStructure S X) (F : Copies a K) :
    MulAction.orbitRel.Quotient (automorphismGroup a) (palette a K Y) :=
  orbitOf Y (copyWitness F)

theorem copyType_of {a : RelStructure L A} {K : RelStructure L X}
    (Y : RelStructure S X) (e : RelEmbedding a K) :
    copyType Y (copyOf e) = orbitOf Y e :=
  same_range_orbit Y (copyWitness (copyOf e)) e (copyWitness_range (copyOf e))

theorem copy_type_surjective {a : RelStructure L A} {K : RelStructure L X}
    (Y : RelStructure S X) (hu : Unavoidable a K Y) (g : RelEmbedding K K) :
    Function.Surjective (fun F : Copies a K => copyType Y (copyMap g F)) := by
  intro q
  induction q using Quotient.inductionOn' with
  | h p =>
    obtain ⟨e, he⟩ := type_coloring_surjective Y hu g p
    refine ⟨copyOf e, ?_⟩
    change copyType Y (copyMap g (copyOf e)) = Quotient.mk'' p
    rw [copyMap_of, copyType_of]
    exact congrArg Quotient.mk'' he

/-- Canonization on actual labelled types gives canonization on actual
finite subsets after quotienting by base automorphisms. -/
theorem copy_canonization {a : RelStructure L A} {K : RelStructure L X}
    (Y : RelStructure S X)
    (hcanon : ∀ (D : Type) [Fintype D] (c : RelEmbedding a K → D),
      ∃ g : RelEmbedding K K, ∃ d : palette a K Y → D,
        ∀ e, c (g.comp e) = d ⟨Y.pullback e, ⟨e, rfl⟩⟩)
    (D : Type) [Fintype D] (c : Copies a K → D) :
    ∃ g : RelEmbedding K K,
      ∃ d : MulAction.orbitRel.Quotient (automorphismGroup a) (palette a K Y) → D,
        ∀ F, c (copyMap g F) = d (copyType Y F) := by
  classical
  let typeOf : RelEmbedding a K → palette a K Y :=
    fun e => ⟨Y.pullback e, ⟨e, rfl⟩⟩
  obtain ⟨g, d, hd⟩ := hcanon D (fun e => c (copyOf e))
  have hsurj : Function.Surjective typeOf := by
    intro p
    obtain ⟨e, he⟩ := p.property
    exact ⟨e, Subtype.ext he⟩
  have hequiv : ∀ σ e, typeOf (σ • e) = σ • typeOf e :=
    palette_type_equivariant Y
  let color : RelEmbedding a K → D := fun e => c (copyOf (g.comp e))
  have hcopy : ∀ (σ : automorphismGroup a) e, color (σ • e) = color e := by
    intro σ e
    apply congrArg c
    exact Subtype.ext (precompose_range σ (g.comp e))
  have hinv := RamseyCommon.OrbitCounting.canonical_constants_orbit_invariant
    typeOf color d hsurj hequiv hcopy hd
  obtain ⟨dbar, hbar⟩ :=
    RamseyCommon.OrbitCounting.invariant_descends_to_orbit_quotient d hinv
  refine ⟨g, dbar, ?_⟩
  intro F
  exact (hd (copyWitness F)).trans (hbar (typeOf (copyWitness F))).symm

/-- The exact copy degree is the number of unavoidable expanded copy
orbits. Rigidity then identifies it with exact division by |Aut(A)|. -/
theorem exact_copy_degree [Finite A]
    {a : RelStructure L A} {K : RelStructure L X}
    (Y : RelStructure S X) (hfin : (palette a K Y).Finite)
    (hu : Unavoidable a K Y) (hr : ∀ p ∈ palette a K Y, Rigid p)
    (hcanon : ∀ (D : Type) [Fintype D] (c : RelEmbedding a K → D),
      ∃ g : RelEmbedding K K, ∃ d : palette a K Y → D,
        ∀ e, c (g.comp e) = d ⟨Y.pullback e, ⟨e, rfl⟩⟩) :
    ExactCopyDegree a K
      (Nat.card (MulAction.orbitRel.Quotient (automorphismGroup a) (palette a K Y))) ∧
      Nat.card (MulAction.orbitRel.Quotient (automorphismGroup a) (palette a K Y))
        = (palette a K Y).ncard / Nat.card (automorphismGroup a) := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype (palette a K Y) := hfin.fintype
  letI : Fintype (automorphismGroup a) := Fintype.ofFinite _
  let Q := MulAction.orbitRel.Quotient (automorphismGroup a) (palette a K Y)
  letI : Fintype Q := Fintype.ofFinite Q
  have h := RamseyCommon.Palette.exact_degree_of_canonicalization
    (fun (g : RelEmbedding K K) (F : Copies a K) => copyMap g F)
    (copyType Y) (copy_type_surjective Y hu)
    (fun D _ c => copy_canonization Y hcanon D c)
  refine ⟨?_, palette_orbit_card Y hfin hr⟩
  simpa only [ExactCopyDegree, CopyDegreeBound, Nat.card_eq_fintype_card] using h

/-- The complete degree conclusion of countable stabilization, including
actual finite-copy colorings and the free automorphism quotient. The source
Ramsey condition remains the explicit premise of the source transfer. -/
theorem countable_big_ramsey_degrees {M : Type}
    (ι : LanguageInclusion L S) [Countable X] [Countable M]
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (hN : N.reduct ι = B) {ψ : M → X} (hψ : Approximate K B ψ)
    (φ : RelEmbedding K B) (hsource : PrecompactSource N φ) :
    ∃ Y : RelStructure S X, Y.reduct ι = K ∧
      ∀ (F : Type) [Finite F] (a : RelStructure L F)
        (_ha : Nonempty (RelEmbedding a K)),
        (palette a K Y).Finite ∧ Unavoidable a K Y ∧
        ExactEmbeddingDegree a K (palette a K Y).ncard ∧
        ExactCopyDegree a K
          (Nat.card (MulAction.orbitRel.Quotient (automorphismGroup a) (palette a K Y))) ∧
        (Nat.card (MulAction.orbitRel.Quotient (automorphismGroup a) (palette a K Y))
          = (palette a K Y).ncard / Nat.card (automorphismGroup a)) ∧
        (∀ η : RelEmbedding K K,
          (palette a K Y).ncard ≤ (palette a K (N.pullback (φ.comp η))).ncard) ∧
        (∃ η : RelEmbedding K K,
          (palette a K Y).ncard = (palette a K (N.pullback (φ.comp η))).ncard) ∧
        (∀ p ∈ palette a K Y, Rigid p) ∧
        ∀ (D : Type) [Fintype D] (c : RelEmbedding a K → D),
          ∃ g : RelEmbedding K K, ∃ d : palette a K Y → D,
            ∀ e, c (g.comp e) = d ⟨Y.pullback e, ⟨e, rfl⟩⟩ := by
  obtain ⟨Y, hY, hall⟩ := countable_big_ramsey_expansion ι hN hψ φ hsource
  refine ⟨Y, hY, ?_⟩
  intro F _ a ha
  obtain ⟨hfin, hu, hemb, hmin, hatt, hr, hcanon⟩ := hall F a ha
  obtain ⟨hcopy, hdiv⟩ := exact_copy_degree Y hfin hu hr hcanon
  exact ⟨hfin, hu, hemb, hcopy, hdiv, hmin, hatt, hr, hcanon⟩

end RelationalRamsey632.Transfer
