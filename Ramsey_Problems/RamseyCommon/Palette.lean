import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Choose

/-!
Finite arguments used in Section 6 of `generic3_ramsey.pdf`.

The theorems here are abstract. In particular, the source Ramsey theorem,
normal-form determination, and the realization criterion are not asserted.
Their relevant consequences appear as explicit hypotheses.
-/

namespace RamseyCommon.Palette

open scoped BigOperators

/-- If finite palettes are nested coordinatewise, a lower bound on their
total cardinality forces equality in every coordinate. This is the finite
rank argument in the proposition `Minimal palettes`. -/
theorem nested_palettes_eq
    {I : Type} [Fintype I] {P : I → Type}
    (small middle large : ∀ i, Finset (P i))
    (hsmall : ∀ i, small i ⊆ middle i)
    (hlarge : ∀ i, middle i ⊆ large i)
    (hmin : (∑ i, (large i).card) ≤ ∑ i, (small i).card) :
    ∀ i, middle i = large i := by
  classical
  have hsub : ∀ i, small i ⊆ large i := fun i => (hsmall i).trans (hlarge i)
  have hle : ∀ i ∈ Finset.univ, (small i).card ≤ (large i).card :=
    fun i _ => Finset.card_le_card (hsub i)
  have heq : (∑ i, (small i).card) = ∑ i, (large i).card :=
    Nat.le_antisymm (Finset.sum_le_sum hle) hmin
  have hcards := (Finset.sum_eq_sum_iff_of_le hle).mp heq
  intro i
  have hsmall_eq : small i = large i :=
    Finset.eq_of_subset_of_card_le (hsub i)
      (hcards i (Finset.mem_univ i)).ge
  exact Finset.Subset.antisymm (hlarge i) (hsmall_eq ▸ hsmall i)

/-- The same argument applied to the images of two transformation tables.
The hypothesis `hmin` is precisely the consequence of minimum rank used
in the paper; realization of the tables is deliberately not assumed here. -/
theorem minimal_image_rank_palette
    {I : Type} [Fintype I] {P : I → Type}
    [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]
    (base candidate : ∀ i, P i → P i)
    (palette : ∀ i, Finset (P i))
    (hsmall : ∀ i, Finset.univ.image (candidate i) ⊆ palette i)
    (hlarge : ∀ i, palette i ⊆ Finset.univ.image (base i))
    (hmin : (∑ i, (Finset.univ.image (base i)).card) ≤
      ∑ i, (Finset.univ.image (candidate i)).card) :
    ∀ i, palette i = Finset.univ.image (base i) :=
  nested_palettes_eq _ _ _ hsmall hlarge hmin

/-- A bound on the number of colors on the occurrences in one copy.
`act` can be composition of embeddings, but no such interpretation is
needed for the finite counting argument. -/
def ColorBound {E M K : Type} (act : M → E → E)
    (c : E → K) (m : M) (t : ℕ) : Prop :=
  ∃ s : Finset K, s.card ≤ t ∧ ∀ e, c (act m e) ∈ s

/-- Abstract embedding big Ramsey upper bound, with arbitrary finite
color sets. -/
def DegreeBound {E M : Type} (act : M → E → E) (t : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] (c : E → K), ∃ m, ColorBound act c m t

/-- A canonicalization into a finite palette gives its cardinality as
an upper bound. Every mathematical canonization assumption is explicit. -/
theorem canonicalization_degreeBound
    {E M P : Type} [Fintype P] (act : M → E → E) (typeOf : E → P)
    (hcanon : ∀ (K : Type) [Fintype K] (c : E → K),
      ∃ m, ∃ d : P → K, ∀ e, c (act m e) = d (typeOf e)) :
    DegreeBound act (Fintype.card P) := by
  classical
  intro K _ c
  obtain ⟨m, d, hd⟩ := hcanon K c
  refine ⟨m, Finset.univ.image d, ?_, ?_⟩
  · exact (Finset.card_image_le).trans_eq (Finset.card_univ)
  · intro e
    rw [hd e]
    exact Finset.mem_image.mpr ⟨typeOf e, Finset.mem_univ _, rfl⟩

/-- An unavoidable finite type coloring gives the matching lower bound.
Thus no smaller integer can be an abstract embedding big Ramsey degree. -/
theorem unavoidable_degree_lowerBound
    {E M P : Type} [Fintype P] (act : M → E → E) (typeOf : E → P)
    (hunavoidable : ∀ m, Function.Surjective (fun e => typeOf (act m e)))
    {t : ℕ} (hbound : DegreeBound act t) : Fintype.card P ≤ t := by
  classical
  obtain ⟨m, s, hs, hmem⟩ := hbound P typeOf
  have hall : Finset.univ ⊆ s := by
    intro p _
    obtain ⟨e, he⟩ := hunavoidable m p
    rw [← he]
    exact hmem e
  have hcard : Fintype.card P ≤ s.card := by
    simpa using Finset.card_le_card hall
  exact hcard.trans hs

/-- Exactness of the cardinality of an unavoidable canonical partition.
This verifies the finite upper/lower-bound transfer in the theorem
`Exact degrees and canonical partitions`,
conditional on the stated unavoidability and canonization inputs. -/
theorem exact_degree_of_canonicalization
    {E M P : Type} [Fintype P] (act : M → E → E) (typeOf : E → P)
    (hunavoidable : ∀ m, Function.Surjective (fun e => typeOf (act m e)))
    (hcanon : ∀ (K : Type) [Fintype K] (c : E → K),
      ∃ m, ∃ d : P → K, ∀ e, c (act m e) = d (typeOf e)) :
    DegreeBound act (Fintype.card P) ∧
      ∀ t, DegreeBound act t → Fintype.card P ≤ t :=
  ⟨canonicalization_degreeBound act typeOf hcanon,
    fun _ h => unavoidable_degree_lowerBound act typeOf hunavoidable h⟩

/-- If a finite set of type/color pairs contains every type but has at
most one pair per type in total, then its color is a function of type. -/
theorem joint_palette_functional
    {P K : Type} [Fintype P] [DecidableEq P] [DecidableEq K]
    (s : Finset (P × K)) (hcard : s.card ≤ Fintype.card P)
    (hall : ∀ p, ∃ k, (p, k) ∈ s) :
    ∃ d : P → K, ∀ p k, (p, k) ∈ s → k = d p := by
  classical
  have himage : s.image Prod.fst = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro p
    obtain ⟨k, hk⟩ := hall p
    exact Finset.mem_image.mpr ⟨(p, k), hk, rfl⟩
  have hsize : (s.image Prod.fst).card = s.card := by
    apply Nat.le_antisymm Finset.card_image_le
    simpa [himage] using hcard
  have hinj := (Finset.card_image_iff).mp hsize
  choose d hd using hall
  refine ⟨d, ?_⟩
  intro p k hk
  have hpairs : (p, k) = (p, d p) := hinj hk (hd p) rfl
  exact congrArg Prod.snd hpairs

/-- A degree bound that equals the number of unavoidable types also
gives a canonical partition. The proof uses the joint type/color
coloring, as in the theorem `Exact degrees and canonical partitions`. -/
theorem canonical_partition_of_exact_bound
    {E M P : Type} [Fintype P]
    (act : M → E → E) (typeOf : E → P)
    (hunavoidable : ∀ m, Function.Surjective (fun e => typeOf (act m e)))
    (hbound : DegreeBound act (Fintype.card P))
    (K : Type) [Fintype K] (c : E → K) :
    ∃ m, ∃ d : P → K, ∀ e, c (act m e) = d (typeOf (act m e)) := by
  classical
  obtain ⟨m, s, hs, hmem⟩ := hbound (P × K) (fun e => (typeOf e, c e))
  have hall : ∀ p, ∃ k, (p, k) ∈ s := by
    intro p
    obtain ⟨e, he⟩ := hunavoidable m p
    refine ⟨c (act m e), ?_⟩
    simpa [he] using hmem e
  obtain ⟨d, hd⟩ := joint_palette_functional s hs hall
  exact ⟨m, d, fun e => hd _ _ (hmem e)⟩

/-- A surjective map on a finite palette returns every type after `q!`
iterations whenever the palette has at most `q` types. This verifies the
permutation exponent step in recurrence and the source return map. -/
theorem surjective_iterate_factorial
    {P : Type} [Fintype P] (f : P → P) (hf : Function.Surjective f)
    (q : ℕ) (hq : Fintype.card P ≤ q) :
    f^[q.factorial] = id := by
  classical
  let p : Equiv.Perm P := Equiv.ofBijective f
    ⟨Finite.injective_iff_surjective.mpr hf, hf⟩
  have hp : p ^ (Fintype.card P).factorial = 1 := by
    simpa only [Fintype.card_perm] using (pow_card_eq_one (x := p))
  obtain ⟨k, hk⟩ := Nat.factorial_dvd_factorial hq
  have hpower : p ^ q.factorial = 1 := by
    rw [hk, pow_mul, hp, one_pow]
  have hcoe := congrArg (fun e : Equiv.Perm P => (e : P → P)) hpower
  simp only [Equiv.Perm.coe_pow, Equiv.Perm.coe_one] at hcoe
  exact hcoe

/-- One factorial exponent works simultaneously for a family of finite
palettes. -/
theorem simultaneous_return_exponent
    {I : Type} {P : I → Type} [∀ i, Fintype (P i)]
    (f : ∀ i, P i → P i) (hf : ∀ i, Function.Surjective (f i))
    (q : ℕ) (hq : ∀ i, Fintype.card (P i) ≤ q) :
    ∀ i, (f i)^[q.factorial] = id :=
  fun i => surjective_iterate_factorial (f i) (hf i) q (hq i)

/-- A map that acts on finite types by a surjective type transformation
has a factorial iterate preserving every type. -/
theorem types_preserved_by_factorial_iterate
    {E P : Type} [Fintype P]
    (typeOf : E → P) (f : E → E) (p : P → P)
    (hact : ∀ e, typeOf (f e) = p (typeOf e))
    (hp : Function.Surjective p) (q : ℕ) (hq : Fintype.card P ≤ q) :
    ∀ e, typeOf (f^[q.factorial] e) = typeOf e := by
  have hsem : Function.Semiconj typeOf f p := hact
  intro e
  have hi := hsem.iterate_right q.factorial e
  rw [surjective_iterate_factorial p hp q hq] at hi
  exact hi

/-- The return-map argument applies to every occurrence in an arbitrary
source `S`, not just occurrences in the image of a coding map. This
captures the quantifier needed in the article's selected-types converse. -/
theorem source_return_map_preserves
    {S E P : Type} (sourceType : S → P) (typeOf : E → P)
    (r : S → E) (f : E → E) (p : P → P) (n : ℕ)
    (hr : ∀ s, typeOf (r s) = p (sourceType s))
    (hf : ∀ e, typeOf (f e) = p (typeOf e))
    (hperiod : p^[n + 1] = id) :
    ∀ s, typeOf (f^[n] (r s)) = sourceType s := by
  have hsem : Function.Semiconj typeOf f p := hf
  intro s
  calc
    typeOf (f^[n] (r s)) = p^[n] (typeOf (r s)) := hsem.iterate_right n (r s)
    _ = p^[n] (p (sourceType s)) := congrArg (p^[n]) (hr s)
    _ = p^[n + 1] (sourceType s) := (Function.iterate_succ_apply p n _).symm
    _ = sourceType s := by rw [hperiod]; rfl

end RamseyCommon.Palette
