import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.SetTheory.Cardinal.Finite

/-!
The finite group-action calculation behind the embedding/copy conversion
in `generic3_ramsey.pdf`, Section `Selection, recurrence, and exact degrees`.
Rigidity, equivariance of the actual normal-form types, and canonization
are explicit hypotheses. None is introduced as an axiom.
-/

namespace RamseyCommon.OrbitCounting

/-- Rigidity of the expanded automorphisms forces the action on types
to have no nontrivial point stabilizers. `ExpandedAut` can be the actual
expanded automorphism predicate when this lemma is instantiated. -/
theorem free_of_rigid_stabilizers
    {G P : Type*} [Group G] [MulAction G P]
    (ExpandedAut : P → G → Prop)
    (hstab : ∀ p g, g • p = p → ExpandedAut p g)
    (hrigid : ∀ p g, ExpandedAut p g → g = 1) :
    ∀ (g : G) (p : P), g • p = p → g = 1 :=
  fun g p h => hrigid p g (hstab p g h)

/-- The explicit freeness condition is equivalent to every stabilizer
subgroup being trivial. -/
theorem stabilizer_eq_bot_of_free
    {G P : Type*} [Group G] [MulAction G P]
    (hfree : ∀ (g : G) (p : P), g • p = p → g = 1) :
    ∀ p : P, MulAction.stabilizer G p = ⊥ := by
  intro p
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  exact hfree g p (MulAction.mem_stabilizer_iff.mp hg)

/-- A free finite group action partitions the type set into equally
sized orbits, each of size `|G|`. -/
theorem free_action_card
    {G P : Type*} [Group G] [MulAction G P] [Fintype G] [Fintype P]
    (hfree : ∀ (g : G) (p : P), g • p = p → g = 1) :
    Fintype.card P = Nat.card (MulAction.orbitRel.Quotient G P) * Fintype.card G := by
  classical
  letI : Fintype (MulAction.orbitRel.Quotient G P) := Fintype.ofFinite _
  have he := MulAction.selfEquivOrbitsQuotientProd
    (stabilizer_eq_bot_of_free hfree)
  have hc := Fintype.card_congr he
  simpa only [Fintype.card_prod, Nat.card_eq_fintype_card] using hc

/-- The quotient count is exact natural-number division by the group
cardinality. The divisor is positive because a group contains its unit. -/
theorem free_action_orbit_card_div
    {G P : Type*} [Group G] [MulAction G P] [Fintype G] [Fintype P]
    (hfree : ∀ (g : G) (p : P), g • p = p → g = 1) :
    Nat.card (MulAction.orbitRel.Quotient G P) = Fintype.card P / Fintype.card G := by
  rw [free_action_card hfree, Nat.mul_div_cancel]
  exact Fintype.card_pos

/-- In particular, the order of the acting group divides the number
of labelled types. -/
theorem group_card_dvd_of_free
    {G P : Type*} [Group G] [MulAction G P] [Fintype G] [Fintype P]
    (hfree : ∀ (g : G) (p : P), g • p = p → g = 1) :
    Fintype.card G ∣ Fintype.card P := by
  refine ⟨Nat.card (MulAction.orbitRel.Quotient G P), ?_⟩
  simpa only [Nat.mul_comm] using free_action_card hfree

/-- The constants obtained by canonizing a coloring of unlabelled
copies agree on every automorphism orbit of labelled types. -/
theorem canonical_constants_orbit_invariant
    {G E P K : Type*} [Group G] [MulAction G E] [MulAction G P]
    (typeOf : E → P) (c : E → K) (d : P → K)
    (htypes : Function.Surjective typeOf)
    (hequiv : ∀ (g : G) (e : E), typeOf (g • e) = g • typeOf e)
    (hcopy : ∀ (g : G) (e : E), c (g • e) = c e)
    (hcanon : ∀ e, c e = d (typeOf e)) :
    ∀ (g : G) (p : P), d (g • p) = d p := by
  intro g p
  obtain ⟨e, rfl⟩ := htypes p
  calc
    d (g • typeOf e) = d (typeOf (g • e)) := congrArg d (hequiv g e).symm
    _ = c (g • e) := (hcanon (g • e)).symm
    _ = c e := hcopy g e
    _ = d (typeOf e) := hcanon e

/-- An orbit-invariant color function descends to the actual quotient,
so its number of possible colors is bounded by the number of orbits. -/
theorem invariant_descends_to_orbit_quotient
    {G P K : Type*} [Group G] [MulAction G P]
    (d : P → K) (hinvariant : ∀ (g : G) (p : P), d (g • p) = d p) :
    ∃ dbar : MulAction.orbitRel.Quotient G P → K,
      ∀ p, dbar (Quotient.mk'' p) = d p := by
  refine ⟨Quotient.lift d ?_, fun _ => rfl⟩
  intro p q hpq
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hpq)
  rw [← hg]
  exact hinvariant g q

end RamseyCommon.OrbitCounting
