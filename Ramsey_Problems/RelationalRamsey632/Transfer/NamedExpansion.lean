import RelationalRamsey632.Transfer.CopyDegrees
import RelationalRamsey632.Transfer.Determination
import Mathlib.Data.Countable.Basic

/-!
Actual relational predicates naming whole finite pullbacks.  The names
carry no extra assumption of finite determination.  The palette and
embedding comparisons below are proved from their truth tables.
-/

namespace RelationalRamsey632.Transfer.Named

open RelStructure

variable {L S : Language} {X J : Type} {n : J → ℕ}

def Symbols (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X) (r : ℕ) :=
  Σ j : {j : J // n j = r ∧ 0 < r}, palette (a j.val) K Y

def language (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X) : Language where
  Rel r := L.Rel r ⊕ Symbols a K Y r

def inclusion (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X) : LanguageInclusion L (language a K Y) where
  relMap _ := Sum.inl
  relInjective _ := Sum.inl_injective

def onStructure (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X)
    {F : Type} (b : RelStructure L F) (p : RelStructure S F) :
    RelStructure (language a K Y) F where
  rel R t := match R with
    | Sum.inl R => b.rel R t
    | Sum.inr ⟨j, q⟩ =>
      Function.Injective (t ∘ Fin.cast j.property.1) ∧
      b.pullback (t ∘ Fin.cast j.property.1) = a j.val ∧
      p.pullback (t ∘ Fin.cast j.property.1) = q.val

abbrev expansion (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X) := onStructure a K Y K Y

@[simp] theorem reduct (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X)
    {F : Type} (b : RelStructure L F) (p : RelStructure S F) :
    (onStructure a K Y b p).reduct (inclusion a K Y) = b := rfl

theorem onStructure_pullback (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X)
    {F G : Type} (b : RelStructure L G) (p : RelStructure S G)
    (f : F → G) (hf : Function.Injective f) :
    (onStructure a K Y b p).pullback f =
      onStructure a K Y (b.pullback f) (p.pullback f) := by
  apply RelStructure.ext_rel
  intro r R t
  cases R with
  | inl R => rfl
  | inr R =>
    rcases R with ⟨j, q⟩
    change (Function.Injective (f ∘ t ∘ Fin.cast j.property.1) ∧ _ ∧ _) ↔
      (Function.Injective (t ∘ Fin.cast j.property.1) ∧ _ ∧ _)
    exact and_congr (hf.of_comp_iff _) Iff.rfl

theorem pullback_of_baseEmbedding (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X)
    {F : Type} {b : RelStructure L F} (e : RelEmbedding b K) :
    (expansion a K Y).pullback e = onStructure a K Y b (Y.pullback e) := by
  rw [onStructure_pullback a K Y K Y e e.injective, e.pullback_eq]

noncomputable def paletteMap (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X)
    {F : Type} (b : RelStructure L F) :
    palette b K Y → palette b K (expansion a K Y) := fun p =>
  ⟨onStructure a K Y b p.val, by
    obtain ⟨e, he⟩ := p.property
    exact ⟨e, (pullback_of_baseEmbedding a K Y e).trans
      (congrArg (onStructure a K Y b) he)⟩⟩

theorem paletteMap_surjective (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X)
    {F : Type} (b : RelStructure L F) :
    Function.Surjective (paletteMap a K Y b) := by
  rintro ⟨p, e, rfl⟩
  refine ⟨⟨Y.pullback e, ⟨e, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  exact (pullback_of_baseEmbedding a K Y e).symm

theorem countable_symbols (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X) [Countable J]
    (hfin : ∀ j, (palette (a j) K Y).Finite) (r : ℕ) :
    Countable (Symbols a K Y r) := by
  letI : ∀ j, Finite (palette (a j) K Y) := fun j => (hfin j).to_subtype
  unfold Symbols
  infer_instance

theorem finite_symbols (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X)
    (hfin : ∀ j, (palette (a j) K Y).Finite) (r : ℕ)
    [Finite {j : J // n j = r}] : Finite (Symbols a K Y r) := by
  letI : ∀ j, Finite (palette (a j) K Y) := fun j => (hfin j).to_subtype
  haveI : Finite {j : J // n j = r ∧ 0 < r} :=
    Finite.of_injective (fun j => (⟨j.val, j.property.1⟩ : {j : J // n j = r}))
      (by
        intro j k h
        apply Subtype.ext
        exact congrArg (fun z : {j : J // n j = r} => z.val) h)
  unfold Symbols
  infer_instance

theorem no_nullary_names (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X) : IsEmpty (Symbols a K Y 0) :=
  ⟨fun ⟨j, _⟩ => (Nat.lt_irrefl 0) j.property.2⟩

theorem eq_on_empty {F : Type} [IsEmpty F] [IsEmpty (S.Rel 0)]
    (p q : RelStructure S F) : p = q := by
  apply RelStructure.ext_rel
  intro r R t
  cases r with
  | zero => exact isEmptyElim R
  | succ r => exact isEmptyElim (t ⟨0, Nat.zero_lt_succ r⟩)

def name (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X) (j : J)
    (hj : 0 < n j) (p : palette (a j) K Y) :
    (language a K Y).Rel (n j) := Sum.inr ⟨⟨j, rfl, hj⟩, p⟩

@[simp] theorem name_rel (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X)
    {F : Type} (b : RelStructure L F) (p : RelStructure S F)
    (j : J) (hj : 0 < n j) (q : palette (a j) K Y) (t : Fin (n j) → F) :
    (onStructure a K Y b p).rel (name a K Y j hj q) t ↔
      Function.Injective t ∧ b.pullback t = a j ∧ p.pullback t = q.val := by
  rfl

def restrictedType (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X)
    {F : Type} {b : RelStructure L F} (p : palette b K Y)
    (j : J) (u : RelEmbedding (a j) b) : palette (a j) K Y :=
  ⟨p.val.pullback u, by
    obtain ⟨e, he⟩ := p.property
    exact ⟨e.comp u, congrArg (fun z => z.pullback u) he⟩⟩

theorem names_determine_restrictions (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X) [IsEmpty (S.Rel 0)]
    {F : Type} {b : RelStructure L F} (p q : palette b K Y)
    (h : onStructure a K Y b p.val = onStructure a K Y b q.val) :
    ∀ j (u : RelEmbedding (a j) b), p.val.pullback u = q.val.pullback u := by
  intro j u
  by_cases hj : 0 < n j
  · let pt := restrictedType a K Y p j u
    have hp : (onStructure a K Y b p.val).rel (name a K Y j hj pt) u :=
      (name_rel a K Y b p.val j hj pt u).mpr ⟨u.injective, u.pullback_eq, rfl⟩
    have hq := h ▸ hp
    exact ((name_rel a K Y b q.val j hj pt u).mp hq).2.2.symm
  · have hn : n j = 0 := by omega
    haveI : IsEmpty (Fin (n j)) := hn ▸ (inferInstance : IsEmpty (Fin 0))
    exact eq_on_empty _ _

theorem paletteMap_injective (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X) [IsEmpty (S.Rel 0)]
    (hD : Determines a K Y) {F : Type} [Finite F]
    (b : RelStructure L F) (hb : Nonempty (RelEmbedding b K)) :
    Function.Injective (paletteMap a K Y b) := by
  intro p q h
  apply Subtype.ext
  exact hD F b hb p.val p.property q.val q.property
    (names_determine_restrictions a K Y p q (congrArg Subtype.val h))

noncomputable def paletteEquiv (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X) [IsEmpty (S.Rel 0)]
    (hD : Determines a K Y) {F : Type} [Finite F]
    (b : RelStructure L F) (hb : Nonempty (RelEmbedding b K)) :
    palette b K Y ≃ palette b K (expansion a K Y) :=
  Equiv.ofBijective (paletteMap a K Y b)
    ⟨paletteMap_injective a K Y hD b hb, paletteMap_surjective a K Y b⟩

theorem cover_determines (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X)
    (hcover : ∀ (F : Type) [Finite F] (b : RelStructure L F),
      Nonempty (RelEmbedding b K) →
        ∃ j, ∃ u : RelEmbedding (a j) b, Function.Surjective u) : Determines a K Y := by
  intro F _ b hb p _ q _ h
  obtain ⟨j, u, hu⟩ := hcover F b hb
  exact pullback_injective_of_surjective u hu (h j u)

theorem embedding_iff_preservesFamily (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X) [IsEmpty (S.Rel 0)]
    (g : RelEmbedding K K) :
    IsEmbeddingMap (expansion a K Y) (expansion a K Y) g ↔ PreservesFamily a K Y g := by
  constructor
  · intro h j e
    by_cases hj : 0 < n j
    · let p : palette (a j) K Y := ⟨Y.pullback e, ⟨e, rfl⟩⟩
      have hp : (expansion a K Y).rel (name a K Y j hj p) e :=
        (name_rel a K Y K Y j hj p e).mpr ⟨e.injective, e.pullback_eq, rfl⟩
      exact ((name_rel a K Y K Y j hj p (g ∘ e)).mp
        ((h.2 _ _ e).mp hp)).2.2
    · have hn : n j = 0 := by omega
      haveI : IsEmpty (Fin (n j)) := hn ▸ (inferInstance : IsEmpty (Fin 0))
      exact eq_on_empty _ _
  · intro h
    refine ⟨g.injective, ?_⟩
    intro r R t
    cases R with
    | inl R => exact g.map_rel R t
    | inr R =>
      rcases R with ⟨j, q⟩
      let u := t ∘ Fin.cast j.property.1
      have hinj : Function.Injective (g ∘ u) ↔ Function.Injective u := g.injective.of_comp_iff u
      have hb : K.pullback (g ∘ u) = K.pullback u := by
        change (K.pullback g).pullback u = K.pullback u
        rw [g.pullback_eq]
      change (Function.Injective u ∧ K.pullback u = a j.val ∧ Y.pullback u = q.val) ↔
        (Function.Injective (g ∘ u) ∧ K.pullback (g ∘ u) = a j.val ∧
          Y.pullback (g ∘ u) = q.val)
      rw [hinj, hb]
      by_cases hi : Function.Injective u
      · by_cases hk : K.pullback u = a j.val
        · let e : RelEmbedding (a j.val) K := {
            toFun := u
            injective := hi
            map_rel := fun R t => by
              have he := congrArg (fun z => z.rel R t) hk
              exact he.symm.to_iff }
          have he := h j.val e
          change Y.pullback (g ∘ u) = Y.pullback u at he
          rw [he]
        · simp only [hk, false_and, and_false]
      · simp only [hi, false_and]

theorem embedding_iff_full (ι : LanguageInclusion L S)
    (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X) [IsEmpty (S.Rel 0)]
    (hYK : Y.reduct ι = K) (hD : Determines a K Y) (f : X → X) :
    IsEmbeddingMap (expansion a K Y) (expansion a K Y) f ↔ IsEmbeddingMap Y Y f := by
  constructor
  · intro hf
    let g : RelEmbedding K K := {
      toFun := f
      injective := hf.1
      map_rel := fun R t => hf.2 _ (Sum.inl R) t }
    exact preserves_family_full_embedding a K Y hD g
      ((embedding_iff_preservesFamily a K Y g).mp hf)
  · intro hf
    let y := embeddingOfMap f hf
    let g := toBaseEmbedding ι hYK hYK y
    apply (embedding_iff_preservesFamily a K Y g).mpr
    intro j e
    change (Y.pullback y).pullback e = Y.pullback e
    rw [y.pullback_eq]

theorem names_covariant (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X)
    {F G : Type} {b : RelStructure L F} {c : RelStructure L G}
    (u : RelEmbedding b c) (p : RelStructure S G) :
    (onStructure a K Y c p).pullback u = onStructure a K Y b (p.pullback u) := by
  rw [onStructure_pullback a K Y c p u u.injective, u.pullback_eq]

theorem names_unavoidable (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X)
    {F : Type} (b : RelStructure L F) (h : Unavoidable b K Y) :
    Unavoidable b K (expansion a K Y) := by
  intro α
  apply Set.Subset.antisymm (palette_pullback_subset b K (expansion a K Y) α)
  rintro p ⟨e, rfl⟩
  have hp : Y.pullback e ∈ palette b K (Y.pullback α) := by
    rw [h α]
    exact ⟨e, rfl⟩
  obtain ⟨v, hv⟩ := hp
  refine ⟨v, ?_⟩
  change (expansion a K Y).pullback (α.comp v) = (expansion a K Y).pullback e
  rw [pullback_of_baseEmbedding, pullback_of_baseEmbedding]
  exact congrArg (onStructure a K Y b) hv

theorem names_rigid (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X) [IsEmpty (S.Rel 0)]
    (hD : Determines a K Y) {F : Type} [Finite F] (b : RelStructure L F)
    (hb : Nonempty (RelEmbedding b K))
    (hr : ∀ p ∈ palette b K Y, Rigid p) :
    ∀ p ∈ palette b K (expansion a K Y), Rigid p := by
  intro c hc σ hσ
  obtain ⟨e, he⟩ := hc
  let p : palette b K Y := ⟨Y.pullback e, ⟨e, rfl⟩⟩
  have hcp : c = onStructure a K Y b p.val :=
    he.symm.trans (pullback_of_baseEmbedding a K Y e)
  rw [hcp] at hσ
  have hbσ : b.pullback σ = b := by
    have hred := congrArg (fun z => z.reduct (inclusion a K Y)) hσ
    exact hred
  let u : RelEmbedding b b := {
    toFun := σ
    injective := σ.injective
    map_rel := fun R t => (congrArg (fun z => z.rel R t) hbσ).symm.to_iff }
  let q : palette b K Y := ⟨p.val.pullback σ, by
    refine ⟨e.comp u, ?_⟩
    rfl⟩
  have hn : paletteMap a K Y b q = paletteMap a K Y b p := by
    apply Subtype.ext
    exact (names_covariant a K Y u p.val).symm.trans hσ
  have hpq := congrArg Subtype.val (paletteMap_injective a K Y hD b hb hn)
  exact hr p.val p.property σ hpq

theorem names_finite_palette (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X)
    {F : Type} (b : RelStructure L F) (hfin : (palette b K Y).Finite) :
    (palette b K (expansion a K Y)).Finite := by
  letI : Finite (palette b K Y) := hfin.to_subtype
  letI : Finite (palette b K (expansion a K Y)) :=
    Finite.of_surjective (paletteMap a K Y b) (paletteMap_surjective a K Y b)
  exact Set.toFinite _

theorem names_palette_card (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X) [IsEmpty (S.Rel 0)]
    (hD : Determines a K Y) {F : Type} [Finite F]
    (b : RelStructure L F) (hb : Nonempty (RelEmbedding b K)) :
    (palette b K (expansion a K Y)).ncard = (palette b K Y).ncard := by
  exact (Nat.card_congr (paletteEquiv a K Y hD b hb)).symm

theorem names_canonization (a : ∀ j, RelStructure L (Fin (n j)))
    (K : RelStructure L X) (Y : RelStructure S X) [IsEmpty (S.Rel 0)]
    (hD : Determines a K Y) {F : Type} [Finite F]
    (b : RelStructure L F) (hb : Nonempty (RelEmbedding b K))
    (hcanon : ∀ (D : Type) [Fintype D] (c : RelEmbedding b K → D),
      ∃ g : RelEmbedding K K, ∃ d : palette b K Y → D,
        ∀ e, c (g.comp e) = d ⟨Y.pullback e, ⟨e, rfl⟩⟩) :
    ∀ (D : Type) [Fintype D] (c : RelEmbedding b K → D),
      ∃ g : RelEmbedding K K, ∃ d : palette b K (expansion a K Y) → D,
        ∀ e, c (g.comp e) = d ⟨(expansion a K Y).pullback e, ⟨e, rfl⟩⟩ := by
  classical
  intro D _ c
  obtain ⟨g, d, hd⟩ := hcanon D c
  let E := paletteEquiv a K Y hD b hb
  refine ⟨g, d ∘ E.symm, ?_⟩
  intro e
  have he : E ⟨Y.pullback e, ⟨e, rfl⟩⟩ =
      (⟨(expansion a K Y).pullback e, ⟨e, rfl⟩⟩ : palette b K (expansion a K Y)) := by
    apply Subtype.ext
    exact (pullback_of_baseEmbedding a K Y e).symm
  rw [hd e, ← he]
  exact congrArg d (E.symm_apply_apply _).symm

end RelationalRamsey632.Transfer.Named
