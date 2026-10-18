import RelationalRamsey632.Coding.ExpandedSource
import RelationalRamsey632.Transfer.BigRamsey
import RelationalRamsey632.Existence.Homogeneity

/-! Intrinsic ordered normal-form codes are exactly the full labelled
pullback types. Subembedding maps act on the codes themselves. -/

namespace RelationalRamsey632.Intrinsic

open Source RelStructure
open scoped FirstOrder

variable {L S : Language} {X F G H : Type} {A : ℕ → Type} {U : Type}

noncomputable def code [Fintype F] (φ : X → Vertex A U)
    (a : RelStructure L F) (K : RelStructure L X) (e : RelEmbedding a K) :
    Fin (Fintype.card F) → Vertex A U :=
  normalForm (φ ∘ e ∘ (Fintype.equivFin F).symm)

def codeRange [Fintype F] (φ : X → Vertex A U)
    (a : RelStructure L F) (K : RelStructure L X) :
    Set (Fin (Fintype.card F) → Vertex A U) := Set.range (code φ a K)

theorem code_eq_iff_pullback [Fintype F]
    (N : RelStructure S (Vertex A U))
    (ι : LanguageInclusion (normalFormLanguage A U) S)
    (hNF : N.reduct ι = normalFormStructure A U)
    (hNorm : ∀ n (t : Fin n → Vertex A U), Function.Injective t →
      N.pullback (normalForm t) = N.pullback t)
    (φ : X → Vertex A U) (hφ : Function.Injective φ)
    (a : RelStructure L F) (K : RelStructure L X) (e f : RelEmbedding a K) :
    code φ a K e = code φ a K f ↔
      (N.pullback φ).pullback e = (N.pullback φ).pullback f := by
  classical
  let E := Fintype.equivFin F
  let te := φ ∘ e ∘ E.symm
  let tf := φ ∘ f ∘ E.symm
  have hie : Function.Injective te := hφ.comp (e.injective.comp E.symm.injective)
  have hif : Function.Injective tf := hφ.comp (f.injective.comp E.symm.injective)
  constructor
  · intro h
    apply Transfer.pullback_injective_of_surjective E.symm E.symm.surjective
    change N.pullback te = N.pullback tf
    exact (hNorm _ te hie).symm.trans
      ((congrArg N.pullback h).trans (hNorm _ tf hif))
  · intro hp
    by_cases hn : 0 < Fintype.card F
    · let R : (normalFormLanguage A U).Rel (Fintype.card F) := ⟨code φ a K e, hn⟩
      have he : N.rel (ι.relMap _ R) te := by
        change (N.reduct ι).rel R te
        rw [hNF]
        exact ⟨hie, rfl⟩
      have htables := congrArg (fun p : RelStructure S F => p.rel (ι.relMap _ R) E.symm) hp
      have hf : N.rel (ι.relMap _ R) tf := htables ▸ he
      change (N.reduct ι).rel R tf at hf
      rw [hNF] at hf
      exact hf.2.symm
    · haveI : IsEmpty F := Fintype.card_eq_zero_iff.mp (by omega)
      have hef : e = f := RelEmbedding.ext (fun x => isEmptyElim x)
      exact congrArg (code φ a K) hef

noncomputable def paletteCodeMap [Fintype F]
    (N : RelStructure S (Vertex A U)) (φ : X → Vertex A U)
    (a : RelStructure L F) (K : RelStructure L X)
    (p : palette a K (N.pullback φ)) : codeRange φ a K :=
  ⟨code φ a K (Classical.choose p.property), ⟨Classical.choose p.property, rfl⟩⟩

theorem paletteCodeMap_of_embedding [Fintype F]
    (N : RelStructure S (Vertex A U))
    (ι : LanguageInclusion (normalFormLanguage A U) S)
    (hNF : N.reduct ι = normalFormStructure A U)
    (hNorm : ∀ n (t : Fin n → Vertex A U), Function.Injective t →
      N.pullback (normalForm t) = N.pullback t)
    (φ : X → Vertex A U) (hφ : Function.Injective φ)
    (a : RelStructure L F) (K : RelStructure L X)
    (p : palette a K (N.pullback φ)) (e : RelEmbedding a K)
    (he : (N.pullback φ).pullback e = p.val) :
    (paletteCodeMap N φ a K p).val = code φ a K e :=
  (code_eq_iff_pullback N ι hNF hNorm φ hφ a K _ e).mpr
    ((Classical.choose_spec p.property).trans he.symm)

noncomputable def paletteCodeEquiv [Fintype F]
    (N : RelStructure S (Vertex A U))
    (ι : LanguageInclusion (normalFormLanguage A U) S)
    (hNF : N.reduct ι = normalFormStructure A U)
    (hNorm : ∀ n (t : Fin n → Vertex A U), Function.Injective t →
      N.pullback (normalForm t) = N.pullback t)
    (φ : X → Vertex A U) (hφ : Function.Injective φ)
    (a : RelStructure L F) (K : RelStructure L X) :
    palette a K (N.pullback φ) ≃ codeRange φ a K :=
  Equiv.ofBijective (paletteCodeMap N φ a K) (by
    constructor
    · intro p q hpq
      apply Subtype.ext
      have hc := congrArg Subtype.val hpq
      have hpb := (code_eq_iff_pullback N ι hNF hNorm φ hφ a K _ _).mp hc
      exact (Classical.choose_spec p.property).symm.trans
        (hpb.trans (Classical.choose_spec q.property))
    · rintro τ
      obtain ⟨e, he⟩ := τ.property
      let p : palette a K (N.pullback φ) := ⟨(N.pullback φ).pullback e, ⟨e, rfl⟩⟩
      refine ⟨p, Subtype.ext ?_⟩
      exact (paletteCodeMap_of_embedding N ι hNF hNorm φ hφ a K p e rfl).trans he)

theorem palette_code_card [Fintype F]
    (N : RelStructure S (Vertex A U))
    (ι : LanguageInclusion (normalFormLanguage A U) S)
    (hNF : N.reduct ι = normalFormStructure A U)
    (hNorm : ∀ n (t : Fin n → Vertex A U), Function.Injective t →
      N.pullback (normalForm t) = N.pullback t)
    (φ : X → Vertex A U) (hφ : Function.Injective φ)
    (a : RelStructure L F) (K : RelStructure L X) :
    (palette a K (N.pullback φ)).ncard = (codeRange φ a K).ncard :=
  Nat.card_congr (paletteCodeEquiv N ι hNF hNorm φ hφ a K)

noncomputable def restrictionCode [Fintype F] [Fintype G]
    {a : RelStructure L F} {b : RelStructure L G} (u : RelEmbedding a b)
    (τ : Fin (Fintype.card G) → Vertex A U) : Fin (Fintype.card F) → Vertex A U :=
  normalForm (τ ∘ (Fintype.equivFin G) ∘ u ∘ (Fintype.equivFin F).symm)

theorem restrictionCode_code [Fintype F] [Fintype G]
    (φ : X → Vertex A U) {a : RelStructure L F} {b : RelStructure L G}
    (K : RelStructure L X) (u : RelEmbedding a b) (e : RelEmbedding b K) :
    restrictionCode u (code φ b K e) = code φ a K (e.comp u) := by
  let q := (Fintype.equivFin G) ∘ u ∘ (Fintype.equivFin F).symm
  have h := normalForm_subtuple (φ ∘ e ∘ (Fintype.equivFin G).symm) q
  have hcomp : (φ ∘ e ∘ (Fintype.equivFin G).symm) ∘ q =
      φ ∘ e.comp u ∘ (Fintype.equivFin F).symm := by
    funext i
    exact congrArg (φ ∘ e) ((Fintype.equivFin G).symm_apply_apply
      (u ((Fintype.equivFin F).symm i)))
  exact h.trans (congrArg normalForm hcomp)

noncomputable def restrictionMap [Fintype F] [Fintype G]
    (φ : X → Vertex A U) {a : RelStructure L F} {b : RelStructure L G}
    (K : RelStructure L X) (u : RelEmbedding a b) : codeRange φ b K → codeRange φ a K :=
  fun τ => ⟨restrictionCode u τ.val, by
    obtain ⟨e, he⟩ := τ.property
    exact ⟨e.comp u, (restrictionCode_code φ K u e).symm.trans (congrArg (restrictionCode u) he)⟩⟩

@[simp] theorem restrictionMap_apply [Fintype F] [Fintype G]
    (φ : X → Vertex A U) {a : RelStructure L F} {b : RelStructure L G}
    (K : RelStructure L X) (u : RelEmbedding a b) (e : RelEmbedding b K) :
    restrictionMap φ K u ⟨code φ b K e, ⟨e, rfl⟩⟩ =
      ⟨code φ a K (e.comp u), ⟨e.comp u, rfl⟩⟩ :=
  Subtype.ext (restrictionCode_code φ K u e)

theorem restrictionCode_comp [Fintype F] [Fintype G] [Fintype H]
    {a : RelStructure L F} {b : RelStructure L G} {d : RelStructure L H}
    (u : RelEmbedding a b) (v : RelEmbedding b d)
    (τ : Fin (Fintype.card H) → Vertex A U) :
    restrictionCode u (restrictionCode v τ) = restrictionCode (v.comp u) τ := by
  let qu := (Fintype.equivFin G) ∘ u ∘ (Fintype.equivFin F).symm
  let qv := (Fintype.equivFin H) ∘ v ∘ (Fintype.equivFin G).symm
  have hn := normalForm_subtuple (τ ∘ qv) qu
  have hc : (τ ∘ qv) ∘ qu =
      τ ∘ (Fintype.equivFin H) ∘ v.comp u ∘ (Fintype.equivFin F).symm := by
    funext i
    simp only [qu, qv, Function.comp_apply, RelEmbedding.comp_apply, Equiv.symm_apply_apply]
  exact hn.trans (congrArg normalForm hc)

theorem restrictionMap_comp [Fintype F] [Fintype G] [Fintype H]
    (φ : X → Vertex A U) {a : RelStructure L F} {b : RelStructure L G}
    {d : RelStructure L H} (K : RelStructure L X) (u : RelEmbedding a b) (v : RelEmbedding b d) :
    restrictionMap φ K u ∘ restrictionMap φ K v = restrictionMap φ K (v.comp u) := by
  funext τ
  exact Subtype.ext (restrictionCode_comp u v τ.val)

theorem restrictionMap_identity [Fintype F] (φ : X → Vertex A U)
    (a : RelStructure L F) (K : RelStructure L X) :
    restrictionMap φ K (RelEmbedding.refl a) = id := by
  funext τ
  obtain ⟨e, he⟩ := τ.property
  apply Subtype.ext
  have hτ : normalForm τ.val = τ.val := by
    rw [← he]
    exact normalForm_idempotent _
  have hq : (Fintype.equivFin F) ∘ RelEmbedding.refl a ∘ (Fintype.equivFin F).symm = id := by
    funext i
    exact (Fintype.equivFin F).apply_symm_apply i
  change restrictionCode (RelEmbedding.refl a) τ.val = τ.val
  unfold restrictionCode
  rw [hq, Function.comp_id]
  exact hτ

theorem embedding_extension [Finite F] [Countable X]
    (K : RelStructure L X) (hK : K.InjectiveRelations)
    (hEP : Existence.OnePointExtensionProperty true K)
    {a : RelStructure L F} {b : RelStructure L G}
    (u : RelEmbedding a b) (e : RelEmbedding a K) (hb : Nonempty (RelEmbedding b K)) :
    ∃ g : RelEmbedding b K, g.comp u = e := by
  classical
  letI := a.toFirstOrder
  letI := b.toFirstOrder
  letI := K.toFirstOrder
  letI : Nonempty (G ↪[L.toFirstOrder] X) := ⟨(Classical.choice hb).toFirstOrder⟩
  have hhom := Existence.ultrahomogeneous_of_EP K (fun _ => hK) hEP
  obtain ⟨g, hg⟩ := hhom.extend_embedding
    (FirstOrder.Language.Structure.FG.of_finite : FirstOrder.Language.Structure.FG L.toFirstOrder F)
    e.toFirstOrder u.toFirstOrder
  refine ⟨RelEmbedding.ofFirstOrder g, ?_⟩
  apply RelEmbedding.ext
  intro x
  have hx := congrArg (fun z : F ↪[L.toFirstOrder] X => z x) hg
  exact hx.symm

/-- Every code on A is the restriction of a code on B, using actual EP
extension of the underlying embedding, not a palette-surjectivity premise. -/
theorem restrictionMap_surjective [Fintype F] [Fintype G] [Countable X]
    (φ : X → Vertex A U) {a : RelStructure L F} {b : RelStructure L G}
    (K : RelStructure L X) (hK : K.InjectiveRelations)
    (hEP : Existence.OnePointExtensionProperty true K)
    (u : RelEmbedding a b) (hb : Nonempty (RelEmbedding b K)) :
    Function.Surjective (restrictionMap φ K u) := by
  intro τ
  obtain ⟨e, he⟩ := τ.property
  obtain ⟨g, hg⟩ := embedding_extension K hK hEP u e hb
  refine ⟨⟨code φ b K g, ⟨g, rfl⟩⟩, Subtype.ext ?_⟩
  exact (restrictionCode_code φ K u g).trans ((congrArg (code φ a K) hg).trans he)

theorem exact_embedding_degree_unique {a : RelStructure L F} {K : RelStructure L X}
    {s t : ℕ} (hs : Transfer.ExactEmbeddingDegree a K s)
    (ht : Transfer.ExactEmbeddingDegree a K t) : s = t :=
  Nat.le_antisymm (hs.2 t ht.1) (ht.2 s hs.1)

theorem code_card_values_nonempty [Fintype F] (φ : X → Vertex A U)
    (a : RelStructure L F) (K : RelStructure L X) :
    ∃ n : ℕ, ∃ η : RelEmbedding K K, (codeRange (φ ∘ η) a K).ncard = n :=
  ⟨_, RelEmbedding.refl K, rfl⟩

noncomputable def codeMinimum [Fintype F] (φ : X → Vertex A U)
    (a : RelStructure L F) (K : RelStructure L X) : ℕ := by
  classical
  exact Nat.find (code_card_values_nonempty φ a K)

theorem codeMinimum_attained [Fintype F] (φ : X → Vertex A U)
    (a : RelStructure L F) (K : RelStructure L X) :
    ∃ η : RelEmbedding K K, (codeRange (φ ∘ η) a K).ncard = codeMinimum φ a K := by
  classical
  exact Nat.find_spec (code_card_values_nonempty φ a K)

theorem codeMinimum_le [Fintype F] (φ : X → Vertex A U)
    (a : RelStructure L F) (K : RelStructure L X) (η : RelEmbedding K K) :
    codeMinimum φ a K ≤ (codeRange (φ ∘ η) a K).ncard := by
  classical
  exact Nat.find_min' (code_card_values_nonempty φ a K) ⟨η, rfl⟩

theorem codeMinimum_eq [Fintype F] (φ : X → Vertex A U)
    (a : RelStructure L F) (K : RelStructure L X) (t : ℕ)
    (hmin : ∀ η : RelEmbedding K K, t ≤ (codeRange (φ ∘ η) a K).ncard)
    (hatt : ∃ η : RelEmbedding K K, (codeRange (φ ∘ η) a K).ncard = t) :
    codeMinimum φ a K = t := by
  obtain ⟨η, hη⟩ := hatt
  obtain ⟨β, hβ⟩ := codeMinimum_attained φ a K
  exact Nat.le_antisymm ((codeMinimum_le φ a K η).trans_eq hη)
    (hβ ▸ hmin β)

/-- The code minimum is the original-language embedding degree for every
allowed compatible precompact source, not just the chosen digit family. -/
theorem exact_codeMinimum_of_source [Fintype F] [Countable X]
    [∀ j, Fintype (A j)] [Countable U]
    (N : RelStructure S (Vertex A U))
    (ιNF : LanguageInclusion (normalFormLanguage A U) S)
    (hNF : N.reduct ιNF = normalFormStructure A U)
    (hNorm : ∀ n (t : Fin n → Vertex A U), Function.Injective t →
      N.pullback (normalForm t) = N.pullback t)
    (ιBase : LanguageInclusion L S)
    (Base : RelStructure L (Vertex A U)) (hBase : N.reduct ιBase = Base)
    (K : RelStructure L X) (ψ : Vertex A U → X)
    (hψ : Transfer.Approximate K Base ψ) (φ : RelEmbedding K Base)
    (hsource : Transfer.PrecompactSource N φ)
    (a : RelStructure L F) (ha : Nonempty (RelEmbedding a K)) :
    Transfer.ExactEmbeddingDegree a K (codeMinimum φ a K) := by
  classical
  haveI := vertexCountable A U
  obtain ⟨Y, _, hY⟩ := Transfer.countable_big_ramsey_expansion ιBase hBase hψ φ hsource
  obtain ⟨_, _, hexact, hmin, hatt, _, _⟩ := hY F a ha
  let t := (palette a K Y).ncard
  have hCodeMin : codeMinimum φ a K = t := by
    apply codeMinimum_eq φ a K t
    · intro η
      have hcard := palette_code_card N ιNF hNF hNorm
        (φ ∘ η) (φ.injective.comp η.injective) a K
      exact (hmin η).trans_eq hcard
    · obtain ⟨η, hη⟩ := hatt
      have hcard := palette_code_card N ιNF hNF hNorm
        (φ ∘ η) (φ.injective.comp η.injective) a K
      exact ⟨η, hcard.symm.trans hη.symm⟩
  exact hCodeMin.symm ▸ hexact

/-- Any two permitted auxiliary representations have the same minimum,
because both are the proved exact original-language degree. -/
theorem coding_choice_independence [Fintype F]
    {A' : ℕ → Type} {U' : Type} (φ : X → Vertex A U) (φ' : X → Vertex A' U')
    (a : RelStructure L F) (K : RelStructure L X)
    (hφ : Transfer.ExactEmbeddingDegree a K (codeMinimum φ a K))
    (hφ' : Transfer.ExactEmbeddingDegree a K (codeMinimum φ' a K)) :
    codeMinimum φ a K = codeMinimum φ' a K :=
  exact_embedding_degree_unique hφ hφ'

/-- Full-table stabilization on one Y implies pointwise stabilization of
the literal gamma functions, at the same size-indexed stages. -/
theorem codes_stabilize_of_full_types [Fintype F]
    (N : RelStructure S (Vertex A U))
    (ιNF : LanguageInclusion (normalFormLanguage A U) S)
    (hNF : N.reduct ιNF = normalFormStructure A U)
    (hNorm : ∀ n (t : Fin n → Vertex A U), Function.Injective t →
      N.pullback (normalForm t) = N.pullback t)
    (φ : X → Vertex A U) (hφ : Function.Injective φ)
    (a : RelStructure L F) (K : RelStructure L X) (Y : RelStructure S X)
    (η : ℕ → RelEmbedding K K) (m : ℕ)
    (htypes : ∀ n, m ≤ n → ∀ e : RelEmbedding a K,
      Y.pullback e = (N.pullback (φ ∘ η n)).pullback e)
    (n p : ℕ) (hn : m ≤ n) (hp : m ≤ p) (e : RelEmbedding a K) :
    code φ a K ((η n).comp e) = code φ a K ((η p).comp e) := by
  apply (code_eq_iff_pullback N ιNF hNF hNorm φ hφ a K _ _).mpr
  exact (htypes n hn e).symm.trans (htypes p hp e)

theorem code_ranges_stabilize_of_full_types [Fintype F]
    (N : RelStructure S (Vertex A U))
    (ιNF : LanguageInclusion (normalFormLanguage A U) S)
    (hNF : N.reduct ιNF = normalFormStructure A U)
    (hNorm : ∀ n (t : Fin n → Vertex A U), Function.Injective t →
      N.pullback (normalForm t) = N.pullback t)
    (φ : X → Vertex A U) (hφ : Function.Injective φ)
    (a : RelStructure L F) (K : RelStructure L X) (Y : RelStructure S X)
    (η : ℕ → RelEmbedding K K) (m : ℕ)
    (htypes : ∀ n, m ≤ n → ∀ e : RelEmbedding a K,
      Y.pullback e = (N.pullback (φ ∘ η n)).pullback e)
    (n p : ℕ) (hn : m ≤ n) (hp : m ≤ p) :
    codeRange (φ ∘ η n) a K = codeRange (φ ∘ η p) a K := by
  apply congrArg Set.range
  funext e
  exact codes_stabilize_of_full_types N ιNF hNF hNorm φ hφ a K Y η m htypes n p hn hp e

section Concrete

variable (L : Language) [∀ r, Fintype (L.Rel r)]

theorem expanded_code_eq_iff [Fintype F]
    (φ : X → Coding.DecoderVertex L) (hφ : Function.Injective φ)
    (a : RelStructure L F) (K : RelStructure L X) (e f : RelEmbedding a K) :
    code φ a K e = code φ a K f ↔
      ((Coding.expandedSource L).pullback φ).pullback e =
        ((Coding.expandedSource L).pullback φ).pullback f :=
  code_eq_iff_pullback (Coding.expandedSource L) (Coding.nfInclusion L)
    (Coding.expandedSource_nf L)
    (fun _ t ht => Coding.expandedSource_normalForm_pullback L t ht) φ hφ a K e f

noncomputable def expanded_paletteCodeEquiv [Fintype F]
    (φ : X → Coding.DecoderVertex L) (hφ : Function.Injective φ)
    (a : RelStructure L F) (K : RelStructure L X) :
    palette a K ((Coding.expandedSource L).pullback φ) ≃ codeRange φ a K :=
  paletteCodeEquiv (Coding.expandedSource L) (Coding.nfInclusion L)
    (Coding.expandedSource_nf L)
    (fun _ t ht => Coding.expandedSource_normalForm_pullback L t ht) φ hφ a K

end Concrete

end RelationalRamsey632.Intrinsic
