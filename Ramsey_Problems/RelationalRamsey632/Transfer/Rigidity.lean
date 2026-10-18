import RelationalRamsey632.Transfer.Canonization
import Mathlib.Logic.Encodable.Basic
import Generic3Ramsey.OrbitCounting

namespace RelationalRamsey632.Transfer

open RelStructure

variable {L S : Language} {A M : Type}

/-- A permutation preserving an injective natural-number order is the
identity. The proof spells out the finite-order rigidity argument without
assuming an ordering on the relational language. -/
theorem perm_eq_one_of_order {F : Type} (rank : F → ℕ)
    (hrank : Function.Injective rank) (σ : Equiv.Perm F)
    (horder : ∀ x y, rank x < rank y ↔ rank (σ x) < rank (σ y)) : σ = 1 := by
  have hfix : ∀ n x, rank x = n → σ x = x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      rcases lt_trichotomy (rank (σ x)) (rank x) with hlt | heq | hgt
      · have hs := ih (rank (σ x)) (hx ▸ hlt) (σ x) rfl
        exact σ.injective hs
      · exact hrank heq
      · let y := σ.symm x
        have hy : rank y < rank x := (horder y x).mpr (by simpa [y] using hgt)
        have hs := ih (rank y) (hx ▸ hy) y rfl
        have hyx : y = x := hs.symm.trans (by simp [y])
        simpa [hyx] using hs
  ext x
  exact hfix (rank x) x rfl

def automorphismGroup (a : RelStructure L A) : Subgroup (Equiv.Perm A) where
  carrier := {σ | a.pullback σ = a}
  one_mem' := rfl
  mul_mem' := by
    intro σ τ hσ hτ
    change a.pullback (σ ∘ τ) = a
    rw [← pullback_comp, hσ, hτ]
  inv_mem' := by
    intro σ hσ
    apply RelStructure.ext_rel
    intro r R t
    have h := congrArg (fun p : RelStructure L A => p.rel R (σ.symm ∘ t)) hσ
    change a.rel R (σ ∘ σ.symm ∘ t) = a.rel R (σ.symm ∘ t) at h
    have ht : σ ∘ σ.symm ∘ t = t := by
      funext j
      simp
    rw [ht] at h
    exact h.symm.to_iff

def automorphismEmbedding {a : RelStructure L A} (σ : automorphismGroup a) :
    RelEmbedding a a where
  toFun := σ.val
  injective := σ.val.injective
  map_rel R t := by
    have h := congrArg (fun p : RelStructure L A => p.rel R t) σ.property
    exact h.symm.to_iff

/-- Rigidity here is about complete relation tables and actual automorphisms. -/
def Rigid (p : RelStructure S A) : Prop :=
  ∀ σ : Equiv.Perm A, p.pullback σ = p → σ = 1

/-- Source embedding degree one forces rigidity of every finite expanded
domain occurring in the source. -/
theorem source_rigid [Finite A] [Countable M]
    {N : RelStructure S M} {p : RelStructure S A}
    (hp : Nonempty (RelEmbedding p N)) (hR : SourceDegreeOne N p) : Rigid p := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  obtain ⟨rank, hrank⟩ := exists_injective_nat M
  let c : RelEmbedding p N → (A → A → Bool) :=
    fun u x y => decide (rank (u x) < rank (u y))
  obtain ⟨ζ, hζ⟩ := hR (A → A → Bool) c
  intro σ hσ
  let a : RelEmbedding p p := automorphismEmbedding (⟨σ, hσ⟩ : automorphismGroup p)
  let u := Classical.choice hp
  have heq := hζ u (u.comp a)
  let r : A → ℕ := rank ∘ ζ ∘ u
  have hinj : Function.Injective r := hrank.comp (ζ.injective.comp u.injective)
  apply perm_eq_one_of_order r hinj σ
  intro x y
  have hh := congrFun (congrFun heq x) y
  change decide (r x < r y) = decide (r (σ x) < r (σ y)) at hh
  constructor
  · intro h
    exact of_decide_eq_true (hh.symm.trans (decide_eq_true h))
  · intro h
    exact of_decide_eq_true (hh.trans (decide_eq_true h))

end RelationalRamsey632.Transfer
