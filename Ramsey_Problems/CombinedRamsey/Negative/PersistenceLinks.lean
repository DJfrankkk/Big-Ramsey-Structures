import CombinedRamsey.Negative.PersistenceWeak

/-! A literal relational language for all links to a finite named base.
Every new variable occurs in a link template. This is essential for free
amalgamation; templates with repeated old entries merely name false relations
under the injective convention. -/

namespace CombinedRamsey.Negative

open RelationalRamsey632

variable {L : Language} {A X F : Type}

def LinkSymbol (L : Language) (A : Type) (r : ℕ) :=
  Σ p : (Σ n, L.Rel n),
    {t : Fin p.1 → A ⊕ Fin r | ∀ i : Fin r, ∃ j, t j = Sum.inr i}

def LinkLanguage (L : Language) (A : Type) : Language where
  Rel := LinkSymbol L A

def BaseComplement {a : RelStructure L A} {K : RelStructure L X}
    (b : RelEmbedding a K) := {x : X // x ∉ Set.range b}

def linkTuple {a : RelStructure L A} {K : RelStructure L X}
    (b : RelEmbedding a K) {r : ℕ} (p : LinkSymbol L A r)
    (t : Fin r → BaseComplement b) : Fin p.1.1 → X :=
  Sum.elim b (Subtype.val ∘ t) ∘ p.2.val

def linkModel {a : RelStructure L A} {K : RelStructure L X}
    (b : RelEmbedding a K) : RelStructure (LinkLanguage L A) (BaseComplement b) where
  rel p t := K.rel p.1.2 (linkTuple b p t)

theorem linkModel_injective {a : RelStructure L A} {K : RelStructure L X}
    (b : RelEmbedding a K) (hK : K.InjectiveRelations) : (linkModel b).InjectiveRelations := by
  intro r p t _ ht i j hij
  obtain ⟨u, hu⟩ := p.2.property i
  obtain ⟨v, hv⟩ := p.2.property j
  have hsize : 0 < p.1.1 := Nat.pos_of_ne_zero (by
    intro h
    have hlt := u.isLt
    omega)
  have heq : linkTuple b p t u = linkTuple b p t v := by
    simp only [linkTuple, Function.comp_apply, hu, hv, Sum.elim_inr, hij]
  have hslots := hK p.1.1 p.1.2 (linkTuple b p t) hsize ht heq
  exact Sum.inr_injective ((hu.symm.trans (congrArg p.2.val hslots)).trans hv)

theorem finite_link_symbols [Finite A] [Finite (Σ n, L.Rel n)] (r : ℕ) :
    Finite ((LinkLanguage L A).Rel r) := by
  unfold LinkLanguage LinkSymbol
  infer_instance

theorem link_arity_le {r : ℕ} (p : LinkSymbol L A r) : r ≤ p.1.1 := by
  classical
  choose slots hslots using p.2.property
  have hi : Function.Injective slots := by
    intro i j h
    exact Sum.inr_injective ((hslots i).symm.trans ((congrArg p.2.val h).trans (hslots j)))
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective slots hi

theorem finite_total_link_language [Finite A] [Finite (Σ n, L.Rel n)] :
    Finite (Σ r, (LinkLanguage L A).Rel r) := by
  classical
  let T := Σ p : (Σ n, L.Rel n), Σ r : Fin (p.1 + 1), Fin p.1 → A ⊕ Fin r.val
  haveI : Finite T := by unfold T; infer_instance
  let into : (Σ r, (LinkLanguage L A).Rel r) → T := fun z =>
    ⟨z.2.1, ⟨z.1, Nat.lt_succ_of_le (link_arity_le z.2)⟩, z.2.2.val⟩
  let recover : T → Option (Σ r, (LinkLanguage L A).Rel r) := fun z =>
    if h : ∀ i : Fin z.2.1.val, ∃ j, z.2.2 j = Sum.inr i then
      some ⟨z.2.1.val, z.1, z.2.2, h⟩ else none
  have hrecover : ∀ z, recover (into z) = some z := by
    rintro ⟨r, p, template, ht⟩
    dsimp only [recover, into]
    have ht' : ∀ i : Fin r, ∃ j, template j = Sum.inr i := ht
    simp only [dif_pos ht']
  apply Finite.of_injective into
  intro z w h
  have heq := congrArg recover h
  rw [hrecover z, hrecover w] at heq
  exact Option.some.inj heq

theorem link_faithfulness {a : RelStructure L A} {K : RelStructure L X}
    (b : RelEmbedding a K) (e f : F → BaseComplement b)
    (heq : (linkModel b).pullback e = (linkModel b).pullback f) :
    K.pullback (Sum.elim b (Subtype.val ∘ e)) =
      K.pullback (Sum.elim b (Subtype.val ∘ f)) := by
  classical
  apply RelStructure.ext_rel
  intro n R t
  let U : Set F := {z | ∃ j, t j = Sum.inr z}
  have hU : U.Finite := by
    have hr : (Set.range t).Finite := Set.finite_range t
    have he : U = Sum.inr ⁻¹' Set.range t := by
      ext z
      simp only [U, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_range]
    rw [he]
    exact hr.preimage Sum.inr_injective.injOn
  letI : Fintype U := hU.fintype
  let en : Fin (Fintype.card U) ≃ U := (Fintype.equivFin U).symm
  let args : Fin (Fintype.card U) → F := fun i => (en i).val
  have hargs : Function.Injective args := Subtype.val_injective.comp en.injective
  have hex : ∀ j, ∃ z : A ⊕ Fin (Fintype.card U), Sum.map id args z = t j := by
    intro j
    cases hj : t j with
    | inl z => exact ⟨Sum.inl z, rfl⟩
    | inr z =>
      refine ⟨Sum.inr (en.symm ⟨z, j, hj⟩), ?_⟩
      exact congrArg Sum.inr (congrArg Subtype.val (en.apply_symm_apply ⟨z, j, hj⟩))
  choose template htemplate using hex
  have hdecode : Sum.map id args ∘ template = t := funext htemplate
  have hnew : ∀ i : Fin (Fintype.card U), ∃ j, template j = Sum.inr i := by
    intro i
    obtain ⟨j, hj⟩ := (en i).property
    refine ⟨j, ?_⟩
    apply (Sum.map_injective.mpr ⟨Function.injective_id, hargs⟩)
    exact (htemplate j).trans hj
  let p : LinkSymbol L A (Fintype.card U) := ⟨⟨n, R⟩, template, hnew⟩
  have hlink := congrArg (fun z => z.rel p args) heq
  change K.rel R (Sum.elim b (Subtype.val ∘ e ∘ args) ∘ template) =
    K.rel R (Sum.elim b (Subtype.val ∘ f ∘ args) ∘ template) at hlink
  have hdec (u : F → BaseComplement b) :
      Sum.elim b (Subtype.val ∘ u ∘ args) ∘ template =
        Sum.elim b (Subtype.val ∘ u) ∘ t := by
    rw [← hdecode]
    funext j
    change Sum.elim b (Subtype.val ∘ u ∘ args) (template j) =
      Sum.elim b (Subtype.val ∘ u) (Sum.map id args (template j))
    cases template j <;> rfl
  rw [hdec e, hdec f] at hlink
  exact Iff.of_eq hlink

theorem link_congruence {a : RelStructure L A} {K : RelStructure L X}
    (b : RelEmbedding a K) (e f : F → BaseComplement b)
    (heq : K.pullback (Sum.elim b (Subtype.val ∘ e)) =
      K.pullback (Sum.elim b (Subtype.val ∘ f))) :
    (linkModel b).pullback e = (linkModel b).pullback f := by
  apply RelStructure.ext_rel
  intro r p t
  have he := congrArg (fun z => z.rel p.1.2 (Sum.map id t ∘ p.2.val)) heq
  have hcomp (u : F → BaseComplement b) :
      Sum.elim b (Subtype.val ∘ u) ∘ Sum.map id t ∘ p.2.val =
        linkTuple b p (u ∘ t) := by
    funext j
    change Sum.elim b (Subtype.val ∘ u) (Sum.map id t (p.2.val j)) =
      Sum.elim b (Subtype.val ∘ u ∘ t) (p.2.val j)
    cases p.2.val j <;> rfl
  change K.rel p.1.2 (Sum.elim b (Subtype.val ∘ e) ∘ Sum.map id t ∘ p.2.val) =
    K.rel p.1.2 (Sum.elim b (Subtype.val ∘ f) ∘ Sum.map id t ∘ p.2.val) at he
  rw [hcomp e, hcomp f] at he
  exact Iff.of_eq he

def LinkedVertices {n : ℕ} (t : RelStructure L (Fin n ⊕ Unit))
    (K : RelStructure L X) (b : RelEmbedding (t.pullback Sum.inl) K) :=
  {x : BaseComplement b // x.val ∈ Realizations t K b}

def linkedModel {n : ℕ} (t : RelStructure L (Fin n ⊕ Unit))
    (K : RelStructure L X) (b : RelEmbedding (t.pullback Sum.inl) K) :
    RelStructure (LinkLanguage L (Fin n)) (LinkedVertices t K b) :=
  (linkModel b).pullback Subtype.val

def linkedValue {n : ℕ} {t : RelStructure L (Fin n ⊕ Unit)}
    {K : RelStructure L X} {b : RelEmbedding (t.pullback Sum.inl) K}
    (x : LinkedVertices t K b) : X := x.val.val

def linkedSelfEmbedding {n : ℕ} (t : RelStructure L (Fin n ⊕ Unit))
    (K : RelStructure L X) (b : RelEmbedding (t.pullback Sum.inl) K)
    (g : RelEmbedding K K) (hg : ∀ a, g (b a) = b a) :
    RelEmbedding (linkedModel t K b) (linkedModel t K b) where
  toFun x := ⟨⟨g x.val.val, by
      rintro ⟨a, ha⟩
      have h : g x.val.val = g (b a) := ha.symm.trans (hg a).symm
      exact x.val.property ⟨a, (g.injective h).symm⟩⟩, by
      obtain ⟨p, hp, hs⟩ := x.property
      exact ⟨g.comp p, fun a => (congrArg g (hp a)).trans (hg a), congrArg g hs⟩⟩
  injective := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact g.injective (congrArg linkedValue h)
  map_rel := by
    intro r p v
    have heq : g ∘ linkTuple b p (Subtype.val ∘ v) =
        linkTuple b p (Subtype.val ∘ (fun x : LinkedVertices t K b =>
          (⟨⟨g x.val.val, by
            rintro ⟨a, ha⟩
            exact x.val.property ⟨a, (g.injective (ha.symm.trans (hg a).symm)).symm⟩⟩,
            by
              obtain ⟨u, hu, hs⟩ := x.property
              exact ⟨g.comp u, fun a => (congrArg g (hu a)).trans (hg a), congrArg g hs⟩⟩ :
            LinkedVertices t K b)) ∘ v) := by
      funext j
      change g (Sum.elim b (linkedValue ∘ v) (p.2.val j)) =
        Sum.elim b (g ∘ linkedValue ∘ v) (p.2.val j)
      cases p.2.val j with
      | inl a => exact hg a
      | inr a => rfl
    exact (g.map_rel p.1.2 (linkTuple b p (Subtype.val ∘ v))).trans (Iff.of_eq
      (congrArg (K.rel p.1.2) heq))

theorem linked_finite_homogeneous {n : ℕ} (t : RelStructure L (Fin n ⊕ Unit))
    (K : RelStructure L X) (b : RelEmbedding (t.pullback Sum.inl) K)
    (hh : FiniteEmbeddingHomogeneous K) : FiniteEmbeddingHomogeneous (linkedModel t K b) := by
  intro F _ a e f
  let ec : F → BaseComplement b := Subtype.val ∘ e
  let fc : F → BaseComplement b := Subtype.val ∘ f
  have hlink : (linkModel b).pullback ec = (linkModel b).pullback fc :=
    e.pullback_eq.trans f.pullback_eq.symm
  have hlift := link_faithfulness b ec fc hlink
  let E : Fin n ⊕ F → X := Sum.elim b (linkedValue ∘ e)
  let F' : Fin n ⊕ F → X := Sum.elim b (linkedValue ∘ f)
  have hinj (u : RelEmbedding a (linkedModel t K b)) :
      Function.Injective (Sum.elim b (linkedValue ∘ u)) := by
    apply Sum.elim_injective.mpr
    refine ⟨b.injective, ?_, ?_⟩
    · exact (Subtype.val_injective.comp Subtype.val_injective).comp u.injective
    · intro i j h
      exact (u j).val.property ⟨i, h⟩
  let old := K.pullback E
  let ee : RelEmbedding old K := RelEmbedding.pullback K E (hinj e)
  let ff : RelEmbedding old K := {
    toFun := F'
    injective := hinj f
    map_rel R v := Iff.of_eq (congrArg (fun z => z.rel R v) hlift) }
  obtain ⟨g, hg⟩ := hh (Fin n ⊕ F) old ee ff
  let hfix : ∀ i, g (b i) = b i := fun i => hg (Sum.inl i)
  refine ⟨linkedSelfEmbedding t K b g hfix, ?_⟩
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact hg (Sum.inr x)

theorem linked_singleton_types {n : ℕ} (t : RelStructure L (Fin n ⊕ Unit))
    (K : RelStructure L X) (b : RelEmbedding (t.pullback Sum.inl) K)
    (x y : LinkedVertices t K b) :
    (linkedModel t K b).pullback (fun _ : Fin 1 => x) =
      (linkedModel t K b).pullback (fun _ : Fin 1 => y) := by
  have hlift (z : LinkedVertices t K b) :
      K.pullback (Sum.elim b (fun _ : Fin 1 => linkedValue z)) =
        t.pullback (Sum.map id (fun _ : Fin 1 => ())) := by
    obtain ⟨e, he, hs⟩ := z.property
    have hfun : e ∘ Sum.map id (fun _ : Fin 1 => ()) =
        Sum.elim b (fun _ : Fin 1 => linkedValue z) := by
      funext a
      cases a with
      | inl a => exact he a
      | inr a => exact hs
    have h := congrArg (fun u => u.pullback (Sum.map id (fun _ : Fin 1 => ()))) e.pullback_eq
    rw [RelStructure.pullback_comp, hfun] at h
    exact h
  exact link_congruence b (fun _ : Fin 1 => x.val) (fun _ : Fin 1 => y.val)
    ((hlift x).trans (hlift y).symm)

def originalLinkInclusion (L : Language) (A : Type) : LanguageInclusion L (LinkLanguage L A) where
  relMap r R := ⟨⟨r, R⟩, Sum.inr, fun i => ⟨i, rfl⟩⟩
  relInjective r := by
    intro R T h
    have hp := congrArg Sigma.fst h
    exact eq_of_heq (Sigma.mk.inj hp).2

theorem linked_original_reduct {n : ℕ} (t : RelStructure L (Fin n ⊕ Unit))
    (K : RelStructure L X) (b : RelEmbedding (t.pullback Sum.inl) K) :
    (linkedModel t K b).reduct (originalLinkInclusion L (Fin n)) =
      K.pullback linkedValue := by
  apply RelStructure.ext_rel
  intro r R v
  rfl

end CombinedRamsey.Negative

