import RelationalRamsey632.Transfer.Canonization
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factorial.Basic

namespace RelationalRamsey632.Transfer

open RelStructure
open scoped BigOperators

variable {L S : Language} {X M : Type}

def embeddingIterate {K : RelStructure L X} (f : RelEmbedding K K) :
    ℕ → RelEmbedding K K
  | 0 => RelEmbedding.refl K
  | n + 1 => f.comp (embeddingIterate f n)

@[simp] theorem embeddingIterate_zero {K : RelStructure L X} (f : RelEmbedding K K) :
    embeddingIterate f 0 = RelEmbedding.refl K := rfl

@[simp] theorem embeddingIterate_succ {K : RelStructure L X}
    (f : RelEmbedding K K) (n : ℕ) :
    embeddingIterate f (n + 1) = f.comp (embeddingIterate f n) := rfl

theorem embeddingIterate_comp {K : RelStructure L X} (f : RelEmbedding K K)
    {A : Type} {a : RelStructure L A} (e : RelEmbedding a K) (n : ℕ) :
    (embeddingIterate f n).comp e = (fun u => f.comp u)^[n] e := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [embeddingIterate_succ, RelEmbedding.comp_assoc, ih,
      Function.iterate_succ_apply']

def Unavoidable {A : Type} (a : RelStructure L A) (K : RelStructure L X)
    (Y : RelStructure S X) : Prop :=
  ∀ f : RelEmbedding K K, palette a K (Y.pullback f) = palette a K Y

def PreservesFamily {J : Type} {A : J → Type}
    (a : ∀ j, RelStructure L (A j)) (K : RelStructure L X)
    (Y : RelStructure S X) (f : RelEmbedding K K) : Prop :=
  ∀ j (e : RelEmbedding (a j) K), Y.pullback (f.comp e) = Y.pullback e

/-- Source homogeneity induces permutations of finite unavoidable palettes.
The equation is uniform over all selected source occurrences, including
occurrences not in the image of the original pullback map. -/
theorem selected_source_action (ι : LanguageInclusion L S)
    {J : Type} [Fintype J] {A : J → Type} [∀ j, Finite (A j)]
    (a : ∀ j, RelStructure L (A j))
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (hN : N.reduct ι = B) {ψ : M → X} (hψ : Approximate K B ψ)
    (i : RelEmbedding K B) (ha : ∀ j, Nonempty (RelEmbedding (a j) K))
    (hfin : ∀ j, (palette (a j) K (N.pullback i)).Finite)
    (hunav : ∀ j, Unavoidable (a j) K (N.pullback i))
    (hR : ∀ j p, p ∈ palette (a j) K (N.pullback i) → SourceDegreeOne N p)
    (α : RelEmbedding K K) :
    ∃ ζ : RelEmbedding N N,
      ∃ π : ∀ j, palette (a j) K (N.pullback i) → palette (a j) K (N.pullback i),
        (∀ j, Function.Surjective (π j)) ∧
        ∀ j (u : RelEmbedding (a j) B) (hp : N.pullback u ∈ palette (a j) K (N.pullback i)),
          (N.pullback i).pullback (α ∘ ψ ∘ ζ ∘ u) = (π j ⟨N.pullback u, hp⟩).val := by
  classical
  let Y := N.pullback i
  have hY : Y.reduct ι = K := by
    rw [reduct_pullback, hN]
    exact i.pullback_eq
  let P : J → Type := fun j => palette (a j) K Y
  letI : ∀ j, Fintype (P j) := fun j => (hfin j).fintype
  let color : ∀ jp : (j : J) × P j, RelEmbedding jp.2.val N → P jp.1 :=
    fun jp u =>
      let v := α.comp (approximateEmbedding hψ (ha jp.1)
        (toBaseEmbedding ι (palette_reduct ι hY jp.2.property) hN u))
      ⟨Y.pullback v, ⟨v, rfl⟩⟩
  obtain ⟨ζ, hζ⟩ := simultaneous_source N (fun jp : (j : J) × P j => jp.2.val)
    (fun jp => hR jp.1 jp.2.val jp.2.property) color
  have hex : ∀ jp : (j : J) × P j, Nonempty (RelEmbedding jp.2.val N) := by
    intro jp
    obtain ⟨e, he⟩ := jp.2.property
    have u := RelEmbedding.pullback N (i.comp e) (i.comp e).injective
    have he' : N.pullback (i.comp e) = jp.2.val := he
    rw [he'] at u
    exact ⟨u⟩
  let w := fun jp => Classical.choice (hex jp)
  let π : ∀ j, P j → P j := fun j p => color ⟨j, p⟩ (ζ.comp (w ⟨j, p⟩))
  have hact : ∀ j (u : RelEmbedding (a j) B)
      (hp : N.pullback u ∈ palette (a j) K Y),
      Y.pullback (α ∘ ψ ∘ ζ ∘ u) = (π j ⟨N.pullback u, hp⟩).val := by
    intro j u hp
    let p : P j := ⟨N.pullback u, hp⟩
    let v : RelEmbedding p.val N := RelEmbedding.pullback N u u.injective
    have hc := hζ ⟨j, p⟩ v (w ⟨j, p⟩)
    exact congrArg Subtype.val hc
  refine ⟨ζ, π, ?_, hact⟩
  intro j p
  let ζb := toBaseEmbedding ι hN hN ζ
  let f := α.comp (approximateComp hψ (ζb.comp i))
  have hp : p.val ∈ palette (a j) K (Y.pullback f) := by
    rw [hunav j f]
    exact p.property
  obtain ⟨e, he⟩ := hp
  refine ⟨⟨Y.pullback e, ⟨e, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  have hh := hact j (i.comp e) (show N.pullback (i.comp e) ∈ palette (a j) K Y from ⟨e, rfl⟩)
  exact hh.symm.trans he

/-- Finite selected palettes can be preserved inside every reduct self-copy,
without any finite determination of all expansion relations. -/
theorem coarse_recurrence (ι : LanguageInclusion L S)
    {J : Type} [Fintype J] {A : J → Type} [∀ j, Finite (A j)]
    (a : ∀ j, RelStructure L (A j))
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (hN : N.reduct ι = B) {ψ : M → X} (hψ : Approximate K B ψ)
    (i : RelEmbedding K B) (ha : ∀ j, Nonempty (RelEmbedding (a j) K))
    (hfin : ∀ j, (palette (a j) K (N.pullback i)).Finite)
    (hunav : ∀ j, Unavoidable (a j) K (N.pullback i))
    (hR : ∀ j p, p ∈ palette (a j) K (N.pullback i) → SourceDegreeOne N p)
    (α : RelEmbedding K K) :
    ∃ β : RelEmbedding K K,
      PreservesFamily a K (N.pullback i) (α.comp β) := by
  classical
  let Y := N.pullback i
  let P : J → Type := fun j => palette (a j) K Y
  letI : ∀ j, Fintype (P j) := fun j => (hfin j).fintype
  obtain ⟨ζ, π, hsurj, hact⟩ := selected_source_action ι a hN hψ i ha hfin hunav hR α
  let ζb := toBaseEmbedding ι hN hN ζ
  let h := approximateComp hψ (ζb.comp i)
  let f := α.comp h
  let q := ∑ j, Fintype.card (P j)
  have hq : ∀ j, Fintype.card (P j) ≤ q := by
    intro j
    exact Finset.single_le_sum (fun k _ => Nat.zero_le (Fintype.card (P k)))
      (Finset.mem_univ j)
  have hp : PreservesFamily a K Y (embeddingIterate f q.factorial) := by
    intro j e
    let typeOf : RelEmbedding (a j) K → P j := fun v => ⟨Y.pullback v, ⟨v, rfl⟩⟩
    have hf : ∀ v, typeOf (f.comp v) = π j (typeOf v) := by
      intro v
      apply Subtype.ext
      exact hact j (i.comp v) ⟨v, rfl⟩
    have hh := Generic3Ramsey.Palette.types_preserved_by_factorial_iterate
      typeOf (fun v => f.comp v) (π j) hf (hsurj j) q (hq j) e
    rw [← embeddingIterate_comp f e q.factorial] at hh
    exact congrArg Subtype.val hh
  have hpos : 0 < q.factorial := Nat.factorial_pos q
  refine ⟨h.comp (embeddingIterate f (q.factorial - 1)), ?_⟩
  have hf : α.comp (h.comp (embeddingIterate f (q.factorial - 1)))
      = embeddingIterate f q.factorial := by
    rw [← RelEmbedding.comp_assoc]
    change f.comp (embeddingIterate f (q.factorial - 1)) = _
    rw [← embeddingIterate_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpos.ne')]
  rw [hf]
  exact hp

/-- The explicit factorial power from the recurrence statement. The
exponent is the factorial of the total number of selected labelled types,
and the power remains inside the prescribed reduct copy. -/
theorem coarse_recurrence_quantitative (ι : LanguageInclusion L S)
    {J : Type} [Fintype J] {A : J → Type} [∀ j, Finite (A j)]
    (a : ∀ j, RelStructure L (A j))
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (hN : N.reduct ι = B) {ψ : M → X} (hψ : Approximate K B ψ)
    (i : RelEmbedding K B) (ha : ∀ j, Nonempty (RelEmbedding (a j) K))
    (hfin : ∀ j, (palette (a j) K (N.pullback i)).Finite)
    (hunav : ∀ j, Unavoidable (a j) K (N.pullback i))
    (hR : ∀ j p, p ∈ palette (a j) K (N.pullback i) → SourceDegreeOne N p)
    (α : RelEmbedding K K) :
    ∃ h : RelEmbedding K K,
      PreservesFamily a K (N.pullback i)
        (embeddingIterate (α.comp h) (∑ j, (palette (a j) K (N.pullback i)).ncard).factorial) ∧
      ∃ β : RelEmbedding K K,
        embeddingIterate (α.comp h) (∑ j, (palette (a j) K (N.pullback i)).ncard).factorial
          = α.comp β := by
  classical
  let Y := N.pullback i
  let P : J → Type := fun j => palette (a j) K Y
  letI : ∀ j, Fintype (P j) := fun j => (hfin j).fintype
  obtain ⟨ζ, π, hsurj, hact⟩ := selected_source_action ι a hN hψ i ha hfin hunav hR α
  let ζb := toBaseEmbedding ι hN hN ζ
  let h := approximateComp hψ (ζb.comp i)
  let f := α.comp h
  let q := ∑ j, (palette (a j) K Y).ncard
  have hq : ∀ j, Fintype.card (P j) ≤ q := by
    intro j
    have hh := Finset.single_le_sum
      (fun k _ => Nat.zero_le (palette (a k) K Y).ncard) (Finset.mem_univ j)
    simpa only [P, q, Set.fintypeCard_eq_ncard] using hh
  have hp : PreservesFamily a K Y (embeddingIterate f q.factorial) := by
    intro j e
    let typeOf : RelEmbedding (a j) K → P j := fun v => ⟨Y.pullback v, ⟨v, rfl⟩⟩
    have hf : ∀ v, typeOf (f.comp v) = π j (typeOf v) := by
      intro v
      apply Subtype.ext
      exact hact j (i.comp v) ⟨v, rfl⟩
    have hh := Generic3Ramsey.Palette.types_preserved_by_factorial_iterate
      typeOf (fun v => f.comp v) (π j) hf (hsurj j) q (hq j) e
    rw [← embeddingIterate_comp f e q.factorial] at hh
    exact congrArg Subtype.val hh
  refine ⟨h, hp, h.comp (embeddingIterate f (q.factorial - 1)), ?_⟩
  rw [← RelEmbedding.comp_assoc]
  change embeddingIterate f q.factorial = f.comp (embeddingIterate f (q.factorial - 1))
  rw [← embeddingIterate_succ,
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_pos q).ne')]

end RelationalRamsey632.Transfer
