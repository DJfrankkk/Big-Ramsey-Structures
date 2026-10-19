import RelationalRamsey632.Source.IntrinsicPalettes
import RelationalRamsey632.Transfer.CopyDegrees

/-! Literal [m]={0,...,m-1} gamma codes and restriction maps. No hidden
finite-domain enumeration is used by these definitions. -/

namespace RelationalRamsey632.Source

theorem normalForm_surjective_reindex {A : ℕ → Type} {U : Type} {m n : ℕ}
    (v : Fin n → Vertex A U) (q : Fin m → Fin n) (hq : Function.Surjective q) :
    normalForm (v ∘ q) = normalForm v ∘ q := by
  have hp : tupleProjections (v ∘ q) = tupleProjections v := by
    apply Set.Subset.antisymm
    · rintro t ⟨i, rfl⟩
      exact ⟨q i, rfl⟩
    · rintro t ⟨j, hj⟩
      obtain ⟨i, rfl⟩ := hq j
      exact ⟨i, hj⟩
  have hl : tupleLevels (v ∘ q) = tupleLevels v := by
    apply Finset.coe_injective
    rw [tupleLevels_coe, tupleLevels_coe, hp]
  funext i
  simp only [normalForm, hl, Function.comp_apply]

end RelationalRamsey632.Source

namespace RelationalRamsey632.Intrinsic

open Source RelStructure

variable {L S : Language} {X : Type} {A : ℕ → Type} {U : Type}

noncomputable def codeFin {m : ℕ} (φ : X → Vertex A U)
    (a : RelStructure L (Fin m)) (K : RelStructure L X) (e : RelEmbedding a K) :
    Fin m → Vertex A U := normalForm (φ ∘ e)

def codeRangeFin {m : ℕ} (φ : X → Vertex A U)
    (a : RelStructure L (Fin m)) (K : RelStructure L X) :
    Set (Fin m → Vertex A U) := Set.range (codeFin φ a K)

theorem code_chosen_to_fin {m : ℕ} (φ : X → Vertex A U)
    (a : RelStructure L (Fin m)) (K : RelStructure L X) (e : RelEmbedding a K) :
    code φ a K e ∘ (Fintype.equivFin (Fin m)) = codeFin φ a K e := by
  let E := Fintype.equivFin (Fin m)
  have hn := normalForm_surjective_reindex (φ ∘ e ∘ E.symm) E E.surjective
  have hcomp : (φ ∘ e ∘ E.symm) ∘ E = φ ∘ e := by
    funext i
    exact congrArg (φ ∘ e) (E.symm_apply_apply i)
  exact hn.symm.trans (congrArg normalForm hcomp)

noncomputable def chosenCodeFinEquiv {m : ℕ} (φ : X → Vertex A U)
    (a : RelStructure L (Fin m)) (K : RelStructure L X) :
    codeRange φ a K ≃ codeRangeFin φ a K :=
  Equiv.ofBijective
    (fun τ => ⟨τ.val ∘ Fintype.equivFin (Fin m), by
      obtain ⟨e, he⟩ := τ.property
      exact ⟨e, (code_chosen_to_fin φ a K e).symm.trans
        (congrArg (fun t => t ∘ Fintype.equivFin (Fin m)) he)⟩⟩)
    (by
      constructor
      · intro τ σ h
        apply Subtype.ext
        funext j
        obtain ⟨i, rfl⟩ := (Fintype.equivFin (Fin m)).surjective j
        exact congrArg (fun t : codeRangeFin φ a K => t.val i) h
      · intro τ
        obtain ⟨e, he⟩ := τ.property
        exact ⟨⟨code φ a K e, ⟨e, rfl⟩⟩,
          Subtype.ext ((code_chosen_to_fin φ a K e).trans he)⟩)

theorem code_fin_card {m : ℕ} (φ : X → Vertex A U)
    (a : RelStructure L (Fin m)) (K : RelStructure L X) :
    (codeRange φ a K).ncard = (codeRangeFin φ a K).ncard :=
  Nat.card_congr (chosenCodeFinEquiv φ a K)

noncomputable def paletteCodeFinEquiv {m : ℕ}
    (N : RelStructure S (Vertex A U))
    (ιNF : LanguageInclusion (normalFormLanguage A U) S)
    (hNF : N.reduct ιNF = normalFormStructure A U)
    (hNorm : ∀ n (t : Fin n → Vertex A U), Function.Injective t →
      N.pullback (normalForm t) = N.pullback t)
    (φ : X → Vertex A U) (hφ : Function.Injective φ)
    (a : RelStructure L (Fin m)) (K : RelStructure L X) :
    palette a K (N.pullback φ) ≃ codeRangeFin φ a K :=
  (paletteCodeEquiv N ιNF hNF hNorm φ hφ a K).trans (chosenCodeFinEquiv φ a K)

theorem paletteCodeFinEquiv_of_embedding {m : ℕ}
    (N : RelStructure S (Vertex A U))
    (ιNF : LanguageInclusion (normalFormLanguage A U) S)
    (hNF : N.reduct ιNF = normalFormStructure A U)
    (hNorm : ∀ n (t : Fin n → Vertex A U), Function.Injective t →
      N.pullback (normalForm t) = N.pullback t)
    (φ : X → Vertex A U) (hφ : Function.Injective φ)
    (a : RelStructure L (Fin m)) (K : RelStructure L X)
    (p : palette a K (N.pullback φ)) (e : RelEmbedding a K)
    (he : (N.pullback φ).pullback e = p.val) :
    (paletteCodeFinEquiv N ιNF hNF hNorm φ hφ a K p).val = codeFin φ a K e := by
  change (paletteCodeMap N φ a K p).val ∘ Fintype.equivFin (Fin m) = _
  rw [paletteCodeMap_of_embedding N ιNF hNF hNorm φ hφ a K p e he]
  exact code_chosen_to_fin φ a K e

theorem codeFin_eq_iff_pullback {m : ℕ}
    (N : RelStructure S (Vertex A U))
    (ιNF : LanguageInclusion (normalFormLanguage A U) S)
    (hNF : N.reduct ιNF = normalFormStructure A U)
    (hNorm : ∀ n (t : Fin n → Vertex A U), Function.Injective t →
      N.pullback (normalForm t) = N.pullback t)
    (φ : X → Vertex A U) (hφ : Function.Injective φ)
    (a : RelStructure L (Fin m)) (K : RelStructure L X) (e f : RelEmbedding a K) :
    codeFin φ a K e = codeFin φ a K f ↔
      (N.pullback φ).pullback e = (N.pullback φ).pullback f := by
  have hc : codeFin φ a K e = codeFin φ a K f ↔ code φ a K e = code φ a K f := by
    rw [← code_chosen_to_fin φ a K e, ← code_chosen_to_fin φ a K f]
    exact (Fintype.equivFin (Fin m)).surjective.injective_comp_right.eq_iff
  exact hc.trans (code_eq_iff_pullback N ιNF hNF hNorm φ hφ a K e f)

noncomputable def restrictionCodeFin {m n : ℕ}
    {a : RelStructure L (Fin m)} {b : RelStructure L (Fin n)}
    (u : RelEmbedding a b) (τ : Fin n → Vertex A U) : Fin m → Vertex A U :=
  normalForm (τ ∘ u)

theorem restrictionCodeFin_code {m n : ℕ} (φ : X → Vertex A U)
    {a : RelStructure L (Fin m)} {b : RelStructure L (Fin n)}
    (K : RelStructure L X) (u : RelEmbedding a b) (e : RelEmbedding b K) :
    restrictionCodeFin u (codeFin φ b K e) = codeFin φ a K (e.comp u) :=
  normalForm_subtuple (φ ∘ e) u

noncomputable def restrictionMapFin {m n : ℕ}
    (φ : X → Vertex A U) {a : RelStructure L (Fin m)} {b : RelStructure L (Fin n)}
    (K : RelStructure L X) (u : RelEmbedding a b) : codeRangeFin φ b K → codeRangeFin φ a K :=
  fun τ => ⟨restrictionCodeFin u τ.val, by
    obtain ⟨e, he⟩ := τ.property
    exact ⟨e.comp u, (restrictionCodeFin_code φ K u e).symm.trans
      (congrArg (restrictionCodeFin u) he)⟩⟩

theorem restrictionMapFin_comp {m n r : ℕ}
    (φ : X → Vertex A U) {a : RelStructure L (Fin m)} {b : RelStructure L (Fin n)}
    {d : RelStructure L (Fin r)} (K : RelStructure L X)
    (u : RelEmbedding a b) (v : RelEmbedding b d) :
    restrictionMapFin φ K u ∘ restrictionMapFin φ K v = restrictionMapFin φ K (v.comp u) := by
  funext τ
  exact Subtype.ext (normalForm_subtuple (τ.val ∘ v) u)

theorem restrictionMapFin_identity {m : ℕ} (φ : X → Vertex A U)
    (a : RelStructure L (Fin m)) (K : RelStructure L X) :
    restrictionMapFin φ K (RelEmbedding.refl a) = id := by
  funext τ
  apply Subtype.ext
  obtain ⟨e, he⟩ := τ.property
  change normalForm (τ.val ∘ id) = τ.val
  rw [Function.comp_id, ← he]
  exact normalForm_idempotent _

theorem restrictionMapFin_surjective {m n : ℕ} [Countable X]
    (φ : X → Vertex A U) {a : RelStructure L (Fin m)} {b : RelStructure L (Fin n)}
    (K : RelStructure L X) (hK : K.InjectiveRelations)
    (hEP : Existence.OnePointExtensionProperty true K)
    (u : RelEmbedding a b) (hb : Nonempty (RelEmbedding b K)) :
    Function.Surjective (restrictionMapFin φ K u) := by
  intro τ
  obtain ⟨e, he⟩ := τ.property
  obtain ⟨g, hg⟩ := embedding_extension K hK hEP u e hb
  exact ⟨⟨codeFin φ b K g, ⟨g, rfl⟩⟩,
    Subtype.ext ((restrictionCodeFin_code φ K u g).trans ((congrArg (codeFin φ a K) hg).trans he))⟩

noncomputable def codeMinimumFin {m : ℕ} (φ : X → Vertex A U)
    (a : RelStructure L (Fin m)) (K : RelStructure L X) : ℕ :=
  codeMinimum φ a K

theorem codeMinimumFin_attained {m : ℕ} (φ : X → Vertex A U)
    (a : RelStructure L (Fin m)) (K : RelStructure L X) :
    ∃ η : RelEmbedding K K, (codeRangeFin (φ ∘ η) a K).ncard = codeMinimumFin φ a K := by
  obtain ⟨η, hη⟩ := codeMinimum_attained φ a K
  exact ⟨η, (code_fin_card (φ ∘ η) a K).symm.trans hη⟩

theorem codeMinimumFin_le {m : ℕ} (φ : X → Vertex A U)
    (a : RelStructure L (Fin m)) (K : RelStructure L X) (η : RelEmbedding K K) :
    codeMinimumFin φ a K ≤ (codeRangeFin (φ ∘ η) a K).ncard :=
  (codeMinimum_le φ a K η).trans_eq (code_fin_card (φ ∘ η) a K)

noncomputable def codeActionFin {m : ℕ} (φ : X → Vertex A U)
    (a : RelStructure L (Fin m)) (K : RelStructure L X)
    (σ : Transfer.automorphismGroup a) (τ : codeRangeFin φ a K) : codeRangeFin φ a K :=
  ⟨τ.val ∘ σ.val.symm, by
    obtain ⟨e, he⟩ := τ.property
    refine ⟨e.comp (Transfer.automorphismEmbedding σ⁻¹), ?_⟩
    have h := normalForm_surjective_reindex (φ ∘ e) σ.val.symm σ.val.symm.surjective
    exact h.trans (congrArg (fun q => q ∘ σ.val.symm) he)⟩

noncomputable instance codeMulActionFin {m : ℕ} (φ : X → Vertex A U)
    (a : RelStructure L (Fin m)) (K : RelStructure L X) :
    MulAction (Transfer.automorphismGroup a) (codeRangeFin φ a K) where
  smul := codeActionFin φ a K
  one_smul τ := Subtype.ext (Function.comp_id τ.val)
  mul_smul _ _ _ := Subtype.ext rfl

theorem code_action_free {m : ℕ} (φ : X → Vertex A U) (hφ : Function.Injective φ)
    (a : RelStructure L (Fin m)) (K : RelStructure L X) :
    ∀ σ : Transfer.automorphismGroup a, ∀ τ : codeRangeFin φ a K, σ • τ = τ → σ = 1 := by
  intro σ τ h
  obtain ⟨e, he⟩ := τ.property
  have hτ : Function.Injective τ.val := he ▸ normalForm_injective (φ ∘ e) (hφ.comp e.injective)
  have hp : τ.val ∘ σ.val.symm = τ.val := congrArg Subtype.val h
  have hσ : σ.val.symm = 1 := by
    apply Equiv.ext
    intro i
    exact hτ (congrFun hp i)
  apply Subtype.ext
  exact inv_eq_one.mp hσ

theorem code_orbit_card {m : ℕ} (φ : X → Vertex A U) (hφ : Function.Injective φ)
    (a : RelStructure L (Fin m)) (K : RelStructure L X)
    (hfin : (codeRangeFin φ a K).Finite) :
    Nat.card (MulAction.orbitRel.Quotient (Transfer.automorphismGroup a) (codeRangeFin φ a K)) =
      (codeRangeFin φ a K).ncard / Nat.card (Transfer.automorphismGroup a) := by
  classical
  letI := hfin.fintype
  letI := Fintype.ofFinite (Transfer.automorphismGroup a)
  simpa only [Nat.card_eq_fintype_card, Set.fintypeCard_eq_ncard] using
    RamseyCommon.OrbitCounting.free_action_orbit_card_div (code_action_free φ hφ a K)

end RelationalRamsey632.Intrinsic
