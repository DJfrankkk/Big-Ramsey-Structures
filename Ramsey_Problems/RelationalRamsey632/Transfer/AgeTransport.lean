import RelationalRamsey632.Transfer.UniformStabilization
import Mathlib.Logic.Equiv.List
import Mathlib.Data.Countable.Defs

namespace RelationalRamsey632.Transfer

open RelStructure

variable {L S : Language} {A F X : Type}

noncomputable def inverseEmbedding {a : RelStructure L A} {b : RelStructure L F}
    (u : RelEmbedding a b) (hu : Function.Surjective u) : RelEmbedding b a := by
  classical
  let v := Equiv.ofBijective u ⟨u.injective, hu⟩
  exact {
    toFun := v.symm
    injective := v.symm.injective
    map_rel := fun R t => by
      have ht := u.map_rel R (v.symm ∘ t)
      have he : u ∘ v.symm ∘ t = t := by
        funext j
        exact v.apply_symm_apply (t j)
      rw [he] at ht
      exact ht.symm }

@[simp] theorem inverseEmbedding_left {a : RelStructure L A} {b : RelStructure L F}
    (u : RelEmbedding a b) (hu : Function.Surjective u) (x : A) :
    inverseEmbedding u hu (u x) = x := by
  classical
  exact (Equiv.ofBijective u ⟨u.injective, hu⟩).symm_apply_apply x

@[simp] theorem inverseEmbedding_right {a : RelStructure L A} {b : RelStructure L F}
    (u : RelEmbedding a b) (hu : Function.Surjective u) (x : F) :
    u (inverseEmbedding u hu x) = x := by
  classical
  exact (Equiv.ofBijective u ⟨u.injective, hu⟩).apply_symm_apply x

theorem pullback_injective_of_surjective (u : A → F) (hu : Function.Surjective u) :
    Function.Injective (fun p : RelStructure S F => p.pullback u) := by
  classical
  intro p q h
  apply RelStructure.ext_rel
  intro r R t
  let s : Fin r → A := fun j => Classical.choose (hu (t j))
  have he : u ∘ s = t := by
    funext j
    exact Classical.choose_spec (hu (t j))
  have hh := congrArg (fun z : RelStructure S A => z.rel R s) h
  change p.rel R (u ∘ s) = q.rel R (u ∘ s) at hh
  rw [he] at hh
  exact hh.to_iff

theorem full_types_transfer {a : RelStructure L A} {b : RelStructure L F}
    {K : RelStructure L X} (u : RelEmbedding a b) (hu : Function.Surjective u)
    (Y Z : RelStructure S X)
    (h : ∀ e : RelEmbedding a K, Y.pullback e = Z.pullback e) :
    ∀ e : RelEmbedding b K, Y.pullback e = Z.pullback e := by
  intro e
  apply pullback_injective_of_surjective u hu
  exact h (e.comp u)

theorem unavoidable_transfer {a : RelStructure L A} {b : RelStructure L F}
    {K : RelStructure L X} (u : RelEmbedding a b) (hu : Function.Surjective u)
    (Y : RelStructure S X) (h : Unavoidable a K Y) : Unavoidable b K Y := by
  intro α
  apply Set.Subset.antisymm (palette_pullback_subset b K Y α)
  rintro p ⟨e, rfl⟩
  have hp : Y.pullback (e.comp u) ∈ palette a K (Y.pullback α) := by
    rw [h α]
    exact ⟨e.comp u, rfl⟩
  obtain ⟨v, hv⟩ := hp
  refine ⟨v.comp (inverseEmbedding u hu), ?_⟩
  apply pullback_injective_of_surjective u hu
  have he : (v.comp (inverseEmbedding u hu)).comp u = v := by
    ext x
    simp
  change Y.pullback (α.comp ((v.comp (inverseEmbedding u hu)).comp u))
    = Y.pullback (e.comp u)
  rw [he]
  exact hv

/-- Coverage by a sequence of actual finite age structures, without
requiring finitely many types at any fixed size. -/
def CoversAge {A : ℕ → Type} (a : ∀ j, RelStructure L (A j))
    (K : RelStructure L X) : Prop :=
  ∀ (F : Type) [Finite F] (b : RelStructure L F),
    Nonempty (RelEmbedding b K) →
      ∃ j, ∃ u : RelEmbedding (a j) b, Function.Surjective u

/-- Enumerating the finite subsets of the countable domain supplies a
cover of the age. Repetitions and the empty structure are harmless. -/
theorem countable_age_cover [Countable X] (K : RelStructure L X) :
    ∃ A : ℕ → Type, ∃ a : ∀ j, RelStructure L (A j),
      (∀ j, Finite (A j)) ∧
      (∀ j, Nonempty (RelEmbedding (a j) K)) ∧ CoversAge a K := by
  classical
  obtain ⟨s, hs⟩ := exists_surjective_nat (Finset X)
  let A : ℕ → Type := fun j => ↥(s j)
  let a : ∀ j, RelStructure L (A j) := fun j => K.pullback Subtype.val
  refine ⟨A, a, inferInstance, ?_, ?_⟩
  · intro j
    exact ⟨RelEmbedding.pullback K Subtype.val Subtype.val_injective⟩
  · intro F _ b hb
    letI : Fintype F := Fintype.ofFinite F
    let e := Classical.choice hb
    let t : Finset X := Finset.univ.image e
    obtain ⟨j, hj⟩ := hs t
    have hmem : ∀ z : A j, ∃ x : F, e x = z.val := by
      intro z
      have hz : z.val ∈ t := by simpa [A, hj] using z.property
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
      exact ⟨x, hx⟩
    let ufun : A j → F := fun z => Classical.choose (hmem z)
    have hufun : ∀ z, e (ufun z) = z.val := fun z => Classical.choose_spec (hmem z)
    let u : RelEmbedding (a j) b := {
      toFun := ufun
      injective := by
        intro z w he
        apply Subtype.ext
        exact (hufun z).symm.trans ((congrArg e he).trans (hufun w))
      map_rel := fun R q => by
        have heq : e ∘ ufun ∘ q = Subtype.val ∘ q := by
          funext k
          exact hufun (q k)
        have hh := e.map_rel R (ufun ∘ q)
        rw [heq] at hh
        exact hh.symm }
    refine ⟨j, u, ?_⟩
    intro x
    have hx : e x ∈ s j := by
      rw [hj]
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    refine ⟨⟨e x, hx⟩, ?_⟩
    apply e.injective
    exact hufun ⟨e x, hx⟩

end RelationalRamsey632.Transfer
