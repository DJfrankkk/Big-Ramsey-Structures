import CombinedRamsey.Negative.PersistenceLinkedAmalgam

/-!
Actual free position from finite homogeneity and the shared free-amalgamation
property of the age. No empty-nullary assumption is made. Compatible finite
embeddings of the free union converge pointwise on the countable domain.
Mixed tuples are considered inside the induced union, as required by the paper.
-/

namespace CombinedRamsey.Negative

open RelationalRamsey632 RelationalRamsey632.Existence

namespace FreePositionConstruction

variable {L : Language} {A B C D : Type}

def unionMap (a : RelStructure L A) (b : RelStructure L B)
    (c : RelStructure L C) (d : RelStructure L D)
    (e : RelationalRamsey632.RelEmbedding a c) (f : RelationalRamsey632.RelEmbedding b d) : RelationalRamsey632.RelEmbedding (FreeUnion a b) (FreeUnion c d) where
  toFun := Sum.map e f
  injective := Sum.map_injective.mpr ⟨e.injective, f.injective⟩
  map_rel R t := by
    classical
    constructor
    · rintro (⟨u, hu, hR⟩ | ⟨u, hu, hR⟩)
      · refine Or.inl ⟨e ∘ u, ?_, (e.map_rel R u).mp hR⟩
        rw [← hu]
        rfl
      · refine Or.inr ⟨f ∘ u, ?_, (f.map_rel R u).mp hR⟩
        rw [← hu]
        rfl
    · rintro (⟨u, hu, hR⟩ | ⟨u, hu, hR⟩)
      · have hall : ∀ j, ∃ x : A, t j = Sum.inl x := by
          intro j
          cases ht : t j with
          | inl x => exact ⟨x, rfl⟩
          | inr x =>
            have hj := congrFun hu j
            simp only [Function.comp_apply, ht, Sum.map_inr] at hj
            cases hj
        choose v hv using hall
        have htv : t = Sum.inl ∘ v := funext hv
        have hev : u = e ∘ v := by
          funext j
          apply Sum.inl_injective
          have hj := congrFun hu j
          simpa only [Function.comp_apply, htv, Sum.map_inl] using hj
        refine Or.inl ⟨v, htv.symm, ?_⟩
        exact (e.map_rel R v).mpr (hev ▸ hR)
      · have hall : ∀ j, ∃ x : B, t j = Sum.inr x := by
          intro j
          cases ht : t j with
          | inr x => exact ⟨x, rfl⟩
          | inl x =>
            have hj := congrFun hu j
            simp only [Function.comp_apply, ht, Sum.map_inl] at hj
            cases hj
        choose v hv using hall
        have htv : t = Sum.inr ∘ v := funext hv
        have hfv : u = f ∘ v := by
          funext j
          apply Sum.inr_injective
          have hj := congrFun hu j
          simpa only [Function.comp_apply, htv, Sum.map_inr] using hj
        refine Or.inr ⟨v, htv.symm, ?_⟩
        exact (f.map_rel R v).mpr (hfv ▸ hR)

def eraseEmpty {A : Type} : Empty ⊕ A → A := Sum.elim Empty.elim id

theorem eraseEmpty_injective {A : Type} : Function.Injective (eraseEmpty (A := A)) := by
  intro x y h
  cases x with
  | inl x => exact x.elim
  | inr x =>
    cases y with
    | inl y => exact y.elim
    | inr y => exact congrArg Sum.inr h

def emptySharedEmbedding (a : RelStructure L A) (b : RelStructure L B) :
    RelationalRamsey632.RelEmbedding (FreeUnion a b)
      (SharedBaseAmalgam.model (a.pullback eraseEmpty) (b.pullback eraseEmpty)) where
  toFun := Sum.inr
  injective := Sum.inr_injective
  map_rel R t := by
    classical
    constructor
    · rintro (⟨u, hu, hR⟩ | ⟨u, hu, hR⟩)
      · refine Or.inl ⟨Sum.inr ∘ u, ?_, hR⟩
        rw [← hu]
        rfl
      · refine Or.inr ⟨Sum.inr ∘ u, ?_, hR⟩
        rw [← hu]
        rfl
    · rintro (⟨u, hu, hR⟩ | ⟨u, hu, hR⟩)
      · refine Or.inl ⟨eraseEmpty ∘ u, ?_, hR⟩
        funext j
        have hj := congrFun hu j
        cases hx : u j with
        | inl x => exact x.elim
        | inr x =>
          apply Sum.inr_injective
          simpa only [Function.comp_apply, hx, SharedBaseAmalgam.left,
            Sum.map_inr, eraseEmpty, Sum.elim_inr, id_eq] using hj
      · refine Or.inr ⟨eraseEmpty ∘ u, ?_, hR⟩
        funext j
        have hj := congrFun hu j
        cases hx : u j with
        | inl x => exact x.elim
        | inr x =>
          apply Sum.inr_injective
          simpa only [Function.comp_apply, hx, SharedBaseAmalgam.right,
            Sum.map_inr, eraseEmpty, Sum.elim_inr, id_eq] using hj

variable (K : RelStructure L ℕ)

theorem finite_union_in_age (hs : AgeSharedFree K) (n m : ℕ) :
    Nonempty (RelationalRamsey632.RelEmbedding (FreeUnion (initialStructure K n) (initialStructure K m)) K) := by
  let a := (initialStructure K n).pullback (eraseEmpty (A := Fin n))
  let b := (initialStructure K m).pullback (eraseEmpty (A := Fin m))
  have hab : a.pullback Sum.inl = b.pullback Sum.inl := by
    change K.pullback (Fin.val ∘ eraseEmpty ∘ Sum.inl) =
      K.pullback (Fin.val ∘ eraseEmpty ∘ Sum.inl)
    apply congrArg K.pullback
    funext x
    exact x.elim
  have ha : Nonempty (RelationalRamsey632.RelEmbedding a K) :=
    ⟨(RelationalRamsey632.RelEmbedding.pullback K Fin.val Fin.val_injective).comp
      (RelationalRamsey632.RelEmbedding.pullback (initialStructure K n) eraseEmpty eraseEmpty_injective)⟩
  have hb : Nonempty (RelationalRamsey632.RelEmbedding b K) :=
    ⟨(RelationalRamsey632.RelEmbedding.pullback K Fin.val Fin.val_injective).comp
      (RelationalRamsey632.RelEmbedding.pullback (initialStructure K m) eraseEmpty eraseEmpty_injective)⟩
  obtain ⟨f⟩ := hs Empty (Fin n) (Fin m) a b hab ha hb
  exact ⟨f.comp (emptySharedEmbedding (initialStructure K n) (initialStructure K m))⟩

def initialMap {m l : ℕ} (h : m ≤ l) : RelationalRamsey632.RelEmbedding (initialStructure K m) (initialStructure K l) where
  toFun := Fin.castLE h
  injective := Fin.castLE_injective h
  map_rel _ _ := Iff.rfl

def startEmbedding {n : ℕ} (e : RelationalRamsey632.RelEmbedding (initialStructure K n) K) :
    RelationalRamsey632.RelEmbedding (FreeUnion (initialStructure K n) (initialStructure K 0)) K where
  toFun := Sum.elim e Fin.elim0
  injective := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (e.injective h)
      | inr y => exact y.elim0
    | inr x => exact x.elim0
  map_rel R t := by
    classical
    constructor
    · rintro (⟨u, hu, hR⟩ | ⟨u, hu, hR⟩)
      · rw [← hu]
        exact (e.map_rel R u).mp hR
      · have heq : Sum.elim e Fin.elim0 ∘ t = (Fin.val : Fin 0 → ℕ) ∘ u := by
          funext j
          exact (u j).elim0
        rw [heq]
        exact hR
    · intro hR
      let u : Fin _ → Fin n := fun j => Sum.elim id Fin.elim0 (t j)
      have htu : Sum.inl ∘ u = t := by
        funext j
        cases ht : t j with
        | inl x => simp only [Function.comp_apply, u, ht, Sum.elim_inl, id_eq]
        | inr x => exact x.elim0
      refine Or.inl ⟨u, htu, ?_⟩
      apply (e.map_rel R u).mpr
      rw [← htu] at hR
      exact hR

structure Stage {n : ℕ} (e : RelationalRamsey632.RelEmbedding (initialStructure K n) K) (m : ℕ) where
  embedding : RelationalRamsey632.RelEmbedding (FreeUnion (initialStructure K n) (initialStructure K m)) K
  boundary : ∀ a, embedding (Sum.inl a) = e a

theorem stage_extension (hh : FiniteEmbeddingHomogeneous K) (hs : AgeSharedFree K)
    {n : ℕ} (e : RelationalRamsey632.RelEmbedding (initialStructure K n) K) (m : ℕ) (s : Stage K e m) :
    ∃ v : Stage K e (m + 1),
      ∀ x : Fin n ⊕ Fin m, v.embedding (Sum.map id Fin.castSucc x) = s.embedding x := by
  let u := unionMap (initialStructure K n) (initialStructure K m)
    (initialStructure K n) (initialStructure K (m + 1)) (RelationalRamsey632.RelEmbedding.refl _) (initialMap K (Nat.le_succ m))
  obtain ⟨f, hf⟩ := finite_age_extension hh u s.embedding (finite_union_in_age K hs n (m + 1))
  refine ⟨⟨f, fun a => (hf (Sum.inl a)).trans (s.boundary a)⟩, hf⟩

theorem whole_union_embedding (hh : FiniteEmbeddingHomogeneous K) (hs : AgeSharedFree K)
    {n : ℕ} (e : RelationalRamsey632.RelEmbedding (initialStructure K n) K) :
    ∃ h : RelationalRamsey632.RelEmbedding (FreeUnion (initialStructure K n) K) K,
      ∀ a : Fin n, h (Sum.inl a) = e a := by
  classical
  let s0 : Stage K e 0 := ⟨startEmbedding K e, fun _ => rfl⟩
  choose next hnext using stage_extension K hh hs e
  let seq : ∀ m, Stage K e m := fun m => Nat.rec s0 (fun m s => next m s) m
  have hsucc : ∀ m (x : Fin n ⊕ Fin m),
      (seq (m + 1)).embedding (Sum.map id Fin.castSucc x) = (seq m).embedding x := by
    intro m x
    exact hnext m (seq m) x
  have hagree : ∀ {m l : ℕ} (hml : m ≤ l) (i : Fin m),
      (seq l).embedding (Sum.inr (Fin.castLE hml i)) = (seq m).embedding (Sum.inr i) := by
    intro m l hml
    induction l, hml using Nat.le_induction with
    | base => intro i; rfl
    | succ l hml ih =>
      intro i
      have hidx : Fin.castLE (Nat.le_succ_of_le hml) i = (Fin.castLE hml i).castSucc := rfl
      rw [hidx]
      exact (hsucc l (Sum.inr (Fin.castLE hml i))).trans (ih i)
  let f : ℕ → ℕ := fun x => (seq (x + 1)).embedding (Sum.inr ⟨x, by omega⟩)
  have hf : ∀ m (i : Fin m), f i.val = (seq m).embedding (Sum.inr i) := by
    intro m i
    exact (hagree (by omega : i.val + 1 ≤ m) ⟨i.val, by omega⟩).symm
  have hfinj : Function.Injective f := by
    intro x y hxy
    let m := max x y + 1
    let ix : Fin m := ⟨x, by dsimp [m]; omega⟩
    let iy : Fin m := ⟨y, by dsimp [m]; omega⟩
    have heq : (seq m).embedding (Sum.inr ix) = (seq m).embedding (Sum.inr iy) :=
      (hf m ix).symm.trans (hxy.trans (hf m iy))
    have h := (seq m).embedding.injective heq
    exact congrArg Fin.val (Sum.inr_injective h)
  have hdis : ∀ a x, e a ≠ f x := by
    intro a x heq
    let ix : Fin (x + 1) := ⟨x, by omega⟩
    have h : (seq (x + 1)).embedding (Sum.inl a) = (seq (x + 1)).embedding (Sum.inr ix) :=
      (seq (x + 1)).boundary a |>.trans (heq.trans (hf (x + 1) ix))
    have hbad := (seq (x + 1)).embedding.injective h
    cases hbad
  let whole : RelationalRamsey632.RelEmbedding (FreeUnion (initialStructure K n) K) K := {
    toFun := Sum.elim e f
    injective := by
      intro x y heq
      cases x with
      | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (e.injective heq)
        | inr y => exact False.elim (hdis x y heq)
      | inr x =>
        cases y with
        | inl y => exact False.elim (hdis y x heq.symm)
        | inr y => exact congrArg Sum.inr (hfinj heq)
    map_rel := by
      intro r R t
      let value : Fin n ⊕ ℕ → ℕ := Sum.elim (fun _ => 0) id
      let m := Finset.univ.sup (value ∘ t) + 1
      have hbound : ∀ j, value (t j) < m := fun j =>
        Nat.lt_succ_of_le (Finset.le_sup (f := value ∘ t) (Finset.mem_univ j))
      let u : Fin r → Fin n ⊕ Fin m := fun j =>
        Sum.map id (fun _ => (⟨value (t j), hbound j⟩ : Fin m)) (t j)
      let inc := unionMap (initialStructure K n) (initialStructure K m) (initialStructure K n) K
        (RelationalRamsey632.RelEmbedding.refl _)
        (RelationalRamsey632.RelEmbedding.pullback K Fin.val Fin.val_injective)
      have htu : inc ∘ u = t := by
        funext j
        cases hx : t j <;> simp [inc, unionMap, u, value, hx]
        rfl
      have hwhole : (seq m).embedding ∘ u = Sum.elim e f ∘ t := by
        funext j
        cases hx : t j with
        | inl a =>
          simpa only [u, hx, Function.comp_apply, Sum.map_inl, id_eq, Sum.elim_inl]
            using (seq m).boundary a
        | inr x =>
          simpa only [u, hx, Function.comp_apply, Sum.map_inr, value, Sum.elim_inr, id_eq]
            using (hf m ⟨value (t j), hbound j⟩).symm
      have hrel := (inc.map_rel R u).symm.trans ((seq m).embedding.map_rel R u)
      rw [htu, hwhole] at hrel
      exact hrel }
  exact ⟨whole, fun _ => rfl⟩

def rightInclusion (n : ℕ) : RelationalRamsey632.RelEmbedding K (FreeUnion (initialStructure K n) K) where
  toFun := Sum.inr
  injective := Sum.inr_injective
  map_rel R t := by
    constructor
    · intro ht
      exact Or.inr ⟨t, rfl, ht⟩
    · rintro (⟨u, hu, hR⟩ | ⟨u, hu, hR⟩)
      · have htu : (Fin.val : Fin n → ℕ) ∘ u = t := by
          funext j
          have hj := congrFun hu j
          cases hj
        exact htu ▸ hR
      · have hut : u = t := funext (fun j => Sum.inr_injective (congrFun hu j))
        exact hut ▸ hR

end FreePositionConstruction

theorem freePosition_of_homogeneous_shared_free {L : Language} (K : RelStructure L ℕ)
    (hh : FiniteEmbeddingHomogeneous K) (hs : AgeSharedFree K) : FreePosition K := by
  classical
  intro n e
  obtain ⟨h, hleft⟩ := FreePositionConstruction.whole_union_embedding K hh hs e
  let g := h.comp (FreePositionConstruction.rightInclusion K n)
  refine ⟨g, ?_, ?_⟩
  · intro a x heq
    have hj : h (Sum.inl a) = h (Sum.inr x) := (hleft a).trans heq
    have hbad := h.injective hj
    cases hbad
  · intro r R t hguard i j hbi hgj ht
    have hpre : ∀ k, ∃ x : Fin n ⊕ ℕ, h x = t k := by
      intro k
      rcases hguard k with hk | hk
      · obtain ⟨a, ha⟩ := hk
        exact ⟨Sum.inl a, (hleft a).trans ha⟩
      · obtain ⟨x, hx⟩ := hk
        exact ⟨Sum.inr x, hx⟩
    choose q hq using hpre
    have hqt : h ∘ q = t := funext hq
    obtain ⟨a, ha⟩ := hbi
    obtain ⟨x, hx⟩ := hgj
    have hqi : q i = Sum.inl a := h.injective ((hq i).trans (ha.symm.trans (hleft a).symm))
    have hqj : q j = Sum.inr x := h.injective ((hq j).trans hx.symm)
    have hrel := (h.map_rel R q).mpr (hqt.symm ▸ ht)
    rcases hrel with ⟨u, hu, _⟩ | ⟨u, hu, _⟩
    · have hbad := (congrFun hu j).trans hqj
      cases hbad
    · have hbad := (congrFun hu i).trans hqi
      cases hbad

end CombinedRamsey.Negative
