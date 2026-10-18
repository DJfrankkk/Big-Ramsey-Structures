import CombinedRamsey.Negative.PersistenceGreedy
import RelationalRamsey632.Existence.FreeAmalgamation

namespace CombinedRamsey.Negative

open RelationalRamsey632 RelationalRamsey632.Existence

variable {L : Language} {X Y : Type}

def FreeUnion (B : RelStructure L X) (C : RelStructure L Y) : RelStructure L (X ⊕ Y) where
  rel R t := (∃ u, Sum.inl ∘ u = t ∧ B.rel R u) ∨
    ∃ v, Sum.inr ∘ v = t ∧ C.rel R v

def AgeFreeAmalgamation (K : RelStructure L ℕ) : Prop :=
  ∀ (A B C : Type) [Finite A] [Finite B] [Finite C]
    (a : RelStructure L A) (b : RelStructure L B) (c : RelStructure L C)
    (f : RelEmbedding a b) (g : RelEmbedding a c),
    Nonempty (RelEmbedding b K) → Nonempty (RelEmbedding c K) →
    Nonempty (RelEmbedding (FreeAmalgamation.model f g) K)

def FreePosition (K : RelStructure L ℕ) : Prop :=
  ∀ n (e : RelEmbedding (initialStructure K n) K),
    ∃ g : RelEmbedding K K,
      (∀ (a : Fin n) x, e a ≠ g x) ∧
      (∀ r (R : L.Rel r) (t : Fin r → ℕ),
        (∀ k, t k ∈ Set.range e ∪ Set.range g) → ∀ (i j : Fin r),
        t i ∈ Set.range e → t j ∈ Set.range g → ¬ K.rel R t)

def TransitiveSingletons (K : RelStructure L ℕ) : Prop :=
  ∀ x y, K.pullback (fun _ : Fin 1 => x) = K.pullback (fun _ : Fin 1 => y)

theorem freeUnion_actual {a : RelStructure L X} {b : RelStructure L Y}
    {K : RelStructure L ℕ} (e : RelEmbedding a K) (f : RelEmbedding b K)
    (hcross : ∀ r (R : L.Rel r) (t : Fin r → ℕ),
      (∀ k, t k ∈ Set.range e ∪ Set.range f) → ∀ (i j : Fin r),
      t i ∈ Set.range e → t j ∈ Set.range f → ¬ K.rel R t) :
    K.pullback (Sum.elim e f) = FreeUnion a b := by
  classical
  apply RelStructure.ext_rel
  intro r R t
  constructor
  · intro ht
    by_cases hleft : ∃ i : Fin r, ∃ x : X, t i = Sum.inl x
    · obtain ⟨i, x, hi⟩ := hleft
      have hall : ∀ j, ∃ y : X, t j = Sum.inl y := by
        intro j
        cases hj : t j with
        | inl y => exact ⟨y, rfl⟩
        | inr y =>
          apply False.elim
          apply hcross r R (Sum.elim e f ∘ t) _ i j _ _ ht
          · intro k
            cases hk : t k with
            | inl z => exact Or.inl ⟨z, by simp only [Function.comp_apply, hk, Sum.elim_inl]⟩
            | inr z => exact Or.inr ⟨z, by simp only [Function.comp_apply, hk, Sum.elim_inr]⟩
          · exact ⟨x, by simp only [Function.comp_apply, hi, Sum.elim_inl]⟩
          · exact ⟨y, by simp only [Function.comp_apply, hj, Sum.elim_inr]⟩
      choose u hu using hall
      have htu : Sum.inl ∘ u = t := (funext hu).symm
      have hq : Sum.elim e f ∘ t = e ∘ u := by rw [← htu]; rfl
      exact Or.inl ⟨u, htu, (e.map_rel R u).mpr (hq ▸ ht)⟩
    · have hall : ∀ j, ∃ y : Y, t j = Sum.inr y := by
        intro j
        cases hj : t j with
        | inr y => exact ⟨y, rfl⟩
        | inl y => exact False.elim (hleft ⟨j, y, hj⟩)
      choose u hu using hall
      have htu : Sum.inr ∘ u = t := (funext hu).symm
      have hq : Sum.elim e f ∘ t = f ∘ u := by rw [← htu]; rfl
      exact Or.inr ⟨u, htu, (f.map_rel R u).mpr (hq ▸ ht)⟩
  · rintro (⟨u, hu, hR⟩ | ⟨u, hu, hR⟩)
    · rw [← hu]
      exact (e.map_rel R u).mp hR
    · rw [← hu]
      exact (f.map_rel R u).mp hR

def freeUnionEmbedding {a : RelStructure L X} {b : RelStructure L Y}
    {K : RelStructure L ℕ} (e : RelEmbedding a K) (f : RelEmbedding b K)
    (hdis : ∀ x y, e x ≠ f y)
    (hcross : ∀ r (R : L.Rel r) (t : Fin r → ℕ),
      (∀ k, t k ∈ Set.range e ∪ Set.range f) → ∀ (i j : Fin r),
      t i ∈ Set.range e → t j ∈ Set.range f → ¬ K.rel R t) :
    RelEmbedding (FreeUnion a b) K where
  toFun := Sum.elim e f
  injective := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (e.injective h)
      | inr y => exact False.elim (hdis x y h)
    | inr x =>
      cases y with
      | inl y => exact False.elim (hdis y x h.symm)
      | inr y => exact congrArg Sum.inr (f.injective h)
  map_rel R t :=
    Iff.of_eq (congrArg (fun z => z.rel R t) (freeUnion_actual e f hcross)).symm

namespace PointAmalgam

variable {n m : ℕ} (B : RelStructure L (Fin (n + 1)))
    (C : RelStructure L (Fin (m + 1)))
    (hpoint : B.pullback (fun _ : Fin 1 => Fin.last n) =
      C.pullback (fun _ : Fin 1 => Fin.last m))

def leftPoint : RelEmbedding (B.pullback (fun _ : Fin 1 => Fin.last n)) B :=
  RelEmbedding.pullback B (fun _ : Fin 1 => Fin.last n)
    (fun _ _ _ => Subsingleton.elim _ _)

def rightPoint : RelEmbedding (B.pullback (fun _ : Fin 1 => Fin.last n)) C where
  toFun := fun _ => Fin.last m
  injective := fun _ _ _ => Subsingleton.elim _ _
  map_rel R t := by
    rw [hpoint]
    rfl

abbrev Domain := FreeAmalgamation.Domain (leftPoint B) (rightPoint B C hpoint)

noncomputable def model : RelStructure L (Domain B C hpoint) :=
  FreeAmalgamation.model (leftPoint B) (rightPoint B C hpoint)

noncomputable def left : RelEmbedding B (model B C hpoint) :=
  FreeAmalgamation.leftEmbedding (leftPoint B) (rightPoint B C hpoint)

noncomputable def right : RelEmbedding C (model B C hpoint) :=
  FreeAmalgamation.rightEmbedding (leftPoint B) (rightPoint B C hpoint)

noncomputable def oldLeft : RelEmbedding (B.pullback Fin.castSucc) (model B C hpoint) :=
  (left B C hpoint).comp (RelEmbedding.pullback B Fin.castSucc (Fin.castSucc_injective n))

noncomputable def oldRight : RelEmbedding (C.pullback Fin.castSucc) (model B C hpoint) :=
  (right B C hpoint).comp (RelEmbedding.pullback C Fin.castSucc (Fin.castSucc_injective m))

theorem old_left_not_right (a : Fin n) :
    oldLeft B C hpoint a ∉ Set.range (right B C hpoint) := by
  rintro ⟨z, hz⟩
  obtain ⟨i, hi, _⟩ := FreeAmalgamation.common_vertex (leftPoint B) (rightPoint B C hpoint)
    a.castSucc z hz.symm
  have hv := congrArg Fin.val hi
  change n = a.val at hv
  have ha := a.isLt
  omega

theorem old_right_not_left (a : Fin m) :
    oldRight B C hpoint a ∉ Set.range (left B C hpoint) := by
  rintro ⟨z, hz⟩
  obtain ⟨i, _, hi⟩ := FreeAmalgamation.common_vertex (leftPoint B) (rightPoint B C hpoint)
    z a.castSucc hz
  have hv := congrArg Fin.val hi
  change m = a.val at hv
  have ha := a.isLt
  omega

noncomputable def oldMap : Fin n ⊕ Fin m → Domain B C hpoint :=
  Sum.elim (oldLeft B C hpoint) (oldRight B C hpoint)

theorem oldMap_injective : Function.Injective (oldMap B C hpoint) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl ((oldLeft B C hpoint).injective hab)
    | inr b => exact False.elim (old_left_not_right B C hpoint a ⟨b.castSucc, hab.symm⟩)
  | inr a =>
    cases b with
    | inl b => exact False.elim (old_right_not_left B C hpoint a ⟨b.castSucc, hab.symm⟩)
    | inr b => exact congrArg Sum.inr ((oldRight B C hpoint).injective hab)

theorem old_model_eq : (model B C hpoint).pullback (oldMap B C hpoint) =
    FreeUnion (B.pullback Fin.castSucc) (C.pullback Fin.castSucc) := by
  classical
  apply RelStructure.ext_rel
  intro r R t
  constructor
  · intro ht
    rcases FreeAmalgamation.free (leftPoint B) (rightPoint B C hpoint) R
      (oldMap B C hpoint ∘ t) ht with hl | hr
    · have he : ∀ i, ∃ a : Fin n, t i = Sum.inl a := by
        intro i
        cases hti : t i with
        | inl a => exact ⟨a, rfl⟩
        | inr a =>
          have hm := hl i
          rw [Function.comp_apply, hti] at hm
          exact False.elim (old_right_not_left B C hpoint a hm)
      choose u hu using he
      have htu : t = Sum.inl ∘ u := funext hu
      have hmap : oldMap B C hpoint ∘ t = oldLeft B C hpoint ∘ u := by rw [htu]; rfl
      refine Or.inl ⟨u, htu.symm, ?_⟩
      exact ((oldLeft B C hpoint).map_rel R u).mpr (hmap ▸ ht)
    · have he : ∀ i, ∃ a : Fin m, t i = Sum.inr a := by
        intro i
        cases hti : t i with
        | inr a => exact ⟨a, rfl⟩
        | inl a =>
          have hm := hr i
          rw [Function.comp_apply, hti] at hm
          exact False.elim (old_left_not_right B C hpoint a hm)
      choose u hu using he
      have htu : t = Sum.inr ∘ u := funext hu
      have hmap : oldMap B C hpoint ∘ t = oldRight B C hpoint ∘ u := by rw [htu]; rfl
      refine Or.inr ⟨u, htu.symm, ?_⟩
      exact ((oldRight B C hpoint).map_rel R u).mpr (hmap ▸ ht)
  · rintro (⟨u, hu, hR⟩ | ⟨u, hu, hR⟩)
    · rw [← hu]
      exact ((oldLeft B C hpoint).map_rel R u).mp hR
    · rw [← hu]
      exact ((oldRight B C hpoint).map_rel R u).mp hR

noncomputable def oldEmbedding :
    RelEmbedding (FreeUnion (B.pullback Fin.castSucc) (C.pullback Fin.castSucc))
      (model B C hpoint) where
  toFun := oldMap B C hpoint
  injective := oldMap_injective B C hpoint
  map_rel R t := Iff.of_eq (congrArg (fun z => z.rel R t) (old_model_eq B C hpoint)).symm

theorem last_eq : left B C hpoint (Fin.last n) = right B C hpoint (Fin.last m) := by
  exact (FreeAmalgamation.left_old (leftPoint B) (rightPoint B C hpoint) (0 : Fin 1)).trans
    (FreeAmalgamation.right_old (leftPoint B) (rightPoint B C hpoint) (0 : Fin 1)).symm

end PointAmalgam

end CombinedRamsey.Negative
