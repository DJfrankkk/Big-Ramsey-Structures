import CombinedRamsey.Negative.Persistence
import Mathlib.ModelTheory.Fraisse

/-! Actual one-point types and boundary transport. A realization is a full
relation-preserving and relation-reflecting embedding of the pointed table. -/

namespace CombinedRamsey.Negative

open RelationalRamsey632
open scoped FirstOrder

variable {L : Language} {X : Type}

def FiniteEmbeddingHomogeneous (K : RelStructure L X) : Prop :=
  ∀ (F : Type) [Finite F] (a : RelStructure L F)
    (e f : RelEmbedding a K), ∃ g : RelEmbedding K K, ∀ x, g (e x) = f x

theorem finiteEmbeddingHomogeneous_of_ultrahomogeneous (K : RelStructure L X)
    (hh : @FirstOrder.Language.IsUltrahomogeneous L.toFirstOrder X K.toFirstOrder) :
    FiniteEmbeddingHomogeneous K := by
  intro F _ a e f
  letI := a.toFirstOrder
  letI := K.toFirstOrder
  letI : Nonempty (X ↪[L.toFirstOrder] X) :=
    ⟨(RelationalRamsey632.RelEmbedding.refl K).toFirstOrder⟩
  obtain ⟨g, hg⟩ := hh.extend_embedding
    (FirstOrder.Language.Structure.FG.of_finite :
      FirstOrder.Language.Structure.FG L.toFirstOrder F)
    f.toFirstOrder e.toFirstOrder
  refine ⟨RelEmbedding.ofFirstOrder g, ?_⟩
  intro x
  have hx := congrArg (fun z : F ↪[L.toFirstOrder] X => z x) hg
  exact hx.symm

theorem finite_age_extension {Y Z : Type} [Finite Y]
    {K : RelStructure L X} (hh : FiniteEmbeddingHomogeneous K)
    {a : RelStructure L Y} {b : RelStructure L Z}
    (u : RelEmbedding a b) (e : RelEmbedding a K)
    (hb : Nonempty (RelEmbedding b K)) :
    ∃ v : RelEmbedding b K, ∀ y, v (u y) = e y := by
  obtain ⟨w⟩ := hb
  obtain ⟨g, hg⟩ := hh Y a (w.comp u) e
  exact ⟨g.comp w, hg⟩

def Realizations {n : ℕ} (t : RelStructure L (Fin n ⊕ Unit))
    (K : RelStructure L X) (b : RelEmbedding (t.pullback Sum.inl) K) : Set X :=
  {x | ∃ e : RelEmbedding t K, (∀ a, e (Sum.inl a) = b a) ∧ e (Sum.inr ()) = x}

theorem realizations_transport {K : RelStructure L X}
    (hh : FiniteEmbeddingHomogeneous K) {n : ℕ}
    (t : RelStructure L (Fin n ⊕ Unit))
    (b b' : RelEmbedding (t.pullback Sum.inl) K) :
    SameAgeOn K (Realizations t K b) K (Realizations t K b') := by
  have hinc (u v : RelEmbedding (t.pullback Sum.inl) K) :
      ∀ m (a : RelStructure L (Fin m)),
        InAgeOn K (Realizations t K u) a → InAgeOn K (Realizations t K v) a := by
    obtain ⟨g, hg⟩ := hh (Fin n) (t.pullback Sum.inl) u v
    intro m a ha
    obtain ⟨e, he⟩ := ha
    refine ⟨g.comp e, ?_⟩
    intro x
    obtain ⟨p, hp, hx⟩ := he x
    refine ⟨g.comp p, ?_, ?_⟩
    · intro y
      change g (p (Sum.inl y)) = v y
      rw [hp y, hg y]
    · change g (p (Sum.inr ())) = g (e x)
      rw [hx]
  exact fun m a => ⟨hinc b b' m a, hinc b' b m a⟩

theorem realizes_outside_boundary {K : RelStructure L X} {n : ℕ}
    {t : RelStructure L (Fin n ⊕ Unit)}
    {b : RelEmbedding (t.pullback Sum.inl) K} {x : X}
    (hx : x ∈ Realizations t K b) : x ∉ Set.range b := by
  obtain ⟨e, he, hx⟩ := hx
  rintro ⟨a, ha⟩
  have h : e (Sum.inr ()) = e (Sum.inl a) := hx.trans (ha.symm.trans (he a).symm)
  have hn := e.injective h
  cases hn

private theorem realization_transfer_same_boundary {K : RelStructure L X}
    {n m : ℕ} {t : RelStructure L (Fin n ⊕ Unit)}
    {s : RelStructure L (Fin m ⊕ Unit)}
    {b : RelEmbedding (t.pullback Sum.inl) K}
    {c : RelEmbedding (s.pullback Sum.inl) K}
    (hr : Set.range b = Set.range c) {x : X}
    (hx : x ∈ Realizations t K b) (hx' : x ∈ Realizations s K c) :
    Realizations t K b ⊆ Realizations s K c := by
  classical
  obtain ⟨p, hp, hpstar⟩ := hx
  obtain ⟨p', hp', hpstar'⟩ := hx'
  have hex : ∀ z : Fin m, ∃ y : Fin n, b y = c z := by
    intro z
    have hc : c z ∈ Set.range b := hr ▸ ⟨z, rfl⟩
    exact hc
  choose a ha using hex
  have hinj : Function.Injective a := by
    intro v w h
    apply c.injective
    rw [← ha v, ← ha w, h]
  let u : Fin m ⊕ Unit → Fin n ⊕ Unit := Sum.map a id
  have heq : p ∘ u = p' := by
    funext z
    cases z with
    | inl v => exact (hp (a v)).trans ((ha v).trans (hp' v).symm)
    | inr v => exact hpstar.trans hpstar'.symm
  let e : RelEmbedding s t := {
    toFun := u
    injective := Sum.map_injective.mpr ⟨hinj, Function.injective_id⟩
    map_rel := by
      intro r R v
      have hq : p ∘ u ∘ v = p' ∘ v := by rw [← Function.comp_assoc, heq]
      exact (p'.map_rel R v).trans (hq ▸ (p.map_rel R (u ∘ v)).symm) }
  intro y hy
  obtain ⟨q, hq, hqstar⟩ := hy
  refine ⟨q.comp e, ?_, ?_⟩
  · intro z
    exact (hq (a z)).trans (ha z)
  · exact hqstar

/-- Equal boundary sets and a common realizing vertex determine the same
entire realization set, even when the original labelled types differ. -/
theorem realizations_eq_of_same_boundary_and_common {K : RelStructure L X}
    {n m : ℕ} {t : RelStructure L (Fin n ⊕ Unit)}
    {s : RelStructure L (Fin m ⊕ Unit)}
    {b : RelEmbedding (t.pullback Sum.inl) K}
    {c : RelEmbedding (s.pullback Sum.inl) K}
    (hr : Set.range b = Set.range c) {x : X}
    (hx : x ∈ Realizations t K b) (hx' : x ∈ Realizations s K c) :
    Realizations t K b = Realizations s K c :=
  Set.Subset.antisymm (realization_transfer_same_boundary hr hx hx')
    (realization_transfer_same_boundary hr.symm hx' hx)

end CombinedRamsey.Negative
