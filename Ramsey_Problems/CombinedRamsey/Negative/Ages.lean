import RelationalRamsey632.Model
import Mathlib.Combinatorics.Compactness
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-! Actual induced ages and the finite-colouring compactness argument in
`neg:age-indivisibility` (3). No Ramsey or indivisibility theorem is an axiom. -/

namespace CombinedRamsey.Negative

open RelationalRamsey632

variable {L : Language} {X Y A : Type}

def InAgeOn (K : RelStructure L X) (P : Set X) (a : RelStructure L A) : Prop :=
  ∃ e : RelEmbedding a K, ∀ x, e x ∈ P

def SameAgeOn (K : RelStructure L X) (P : Set X)
    (N : RelStructure L Y) (Q : Set Y) : Prop :=
  ∀ n (a : RelStructure L (Fin n)), InAgeOn K P a ↔ InAgeOn N Q a

def AgeIndivisibleOn (K : RelStructure L X) (P : Set X) : Prop :=
  ∀ r (χ : X → Fin (r + 1)), ∃ i,
    SameAgeOn K P K (P ∩ {x | χ x = i})

theorem inAgeOn_mono {K : RelStructure L X} {P Q : Set X}
    (hPQ : P ⊆ Q) {a : RelStructure L A} (h : InAgeOn K P a) :
    InAgeOn K Q a := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, fun x => hPQ (he x)⟩

theorem sameAgeOn_refl (K : RelStructure L X) (P : Set X) :
    SameAgeOn K P K P := fun _ _ => Iff.rfl

theorem sameAgeOn_symm {K : RelStructure L X} {P : Set X}
    {N : RelStructure L Y} {Q : Set Y} (h : SameAgeOn K P N Q) :
    SameAgeOn N Q K P := fun n a => (h n a).symm

theorem sameAgeOn_trans {Z : Type} {K : RelStructure L X} {P : Set X}
    {N : RelStructure L Y} {Q : Set Y} {M : RelStructure L Z} {R : Set Z}
    (h : SameAgeOn K P N Q) (h' : SameAgeOn N Q M R) :
    SameAgeOn K P M R := fun n a => (h n a).trans (h' n a)

theorem sameAgeOn_image {K : RelStructure L X} (f : RelEmbedding K K)
    (P : Set X) : SameAgeOn K P K (f '' P) := by
  intro n a
  constructor
  · rintro ⟨e, he⟩
    exact ⟨f.comp e, fun x => ⟨e x, he x, rfl⟩⟩
  · rintro ⟨e, he⟩
    choose u hu hu' using he
    let g : RelEmbedding a K := {
      toFun := u
      injective := by
        intro x y hxy
        apply e.injective
        rw [← hu' x, ← hu' y, hxy]
      map_rel := by
        intro r R t
        have ht : f ∘ u ∘ t = e ∘ t := by
          funext i
          exact hu' (t i)
        exact (e.map_rel R t).trans (ht ▸ (f.map_rel R (u ∘ t)).symm) }
    exact ⟨g, hu⟩

def MonoIn (K : RelStructure L X) (P : Set X) (a : RelStructure L A)
    {C : Type} (χ : X → C) : Prop :=
  ∃ (e : RelEmbedding a K) (i : C), ∀ x, e x ∈ P ∧ χ (e x) = i

def FiniteMonoWitness (K : RelStructure L X) (P : Set X)
    (a : RelStructure L A) (r : ℕ) : Prop :=
  ∃ s : Finset X, (↑s : Set X) ⊆ P ∧
    ∀ χ : X → Fin (r + 1), MonoIn K (↑s) a χ

/-- Finite monochromatic witnesses follow from actual age indivisibility by
Rado selection of consistent finite avoiding colourings. -/
theorem finiteMonoWitness_of_ageIndivisible {K : RelStructure L X} {P : Set X}
    (hP : AgeIndivisibleOn K P) {n : ℕ} (a : RelStructure L (Fin n))
    (ha : InAgeOn K P a) (r : ℕ) : FiniteMonoWitness K P a r := by
  classical
  by_contra hnone
  have hex : ∀ s : Finset X, ∃ χ : X → Fin (r + 1),
      ¬ MonoIn K (↑(s.filter (· ∈ P))) a χ := by
    intro s
    by_contra h
    push Not at h
    exact hnone ⟨s.filter (· ∈ P), fun _ hx => (Finset.mem_filter.mp hx).2, h⟩
  choose g hg using hex
  obtain ⟨χ, hχ⟩ := Finset.rado_selection g
  obtain ⟨i, hi⟩ := hP r χ
  obtain ⟨e, he⟩ := (hi n a).mp ha
  let s : Finset X := Finset.univ.image e
  obtain ⟨t, hst, hmatch⟩ := hχ s
  apply hg t
  refine ⟨e, i, ?_⟩
  intro x
  have hs : e x ∈ s := Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  refine ⟨Finset.mem_filter.mpr ⟨hst hs, (he x).1⟩, ?_⟩
  exact (hmatch (e x) hs).symm.trans (he x).2

/-- Same-age transfer of a finite monochromatic witness. The finite structure
used on the right is the full induced table on the actual witness vertices. -/
theorem finiteMonoWitness_transfer {K : RelStructure L X} {P : Set X}
    {N : RelStructure L Y} {Q : Set Y} (hage : SameAgeOn K P N Q)
    {n r : ℕ} {a : RelStructure L (Fin n)}
    (hw : FiniteMonoWitness K P a r) (χ : Y → Fin (r + 1)) : MonoIn N Q a χ := by
  classical
  obtain ⟨s, hs, hmono⟩ := hw
  let enum : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let q : Fin (Fintype.card s) → X := fun i => (enum i).val
  let b := K.pullback q
  have hb : InAgeOn K P b :=
    ⟨RelEmbedding.pullback K q (Subtype.val_injective.comp enum.injective),
      fun i => hs (enum i).property⟩
  obtain ⟨v, hv⟩ := (hage _ b).mp hb
  let lifted : X → Fin (r + 1) := fun x =>
    if hx : x ∈ s then χ (v (enum.symm ⟨x, hx⟩)) else 0
  obtain ⟨e, i, he⟩ := hmono lifted
  let u : Fin n → Fin (Fintype.card s) := fun x => enum.symm ⟨e x, (he x).1⟩
  have hq : q ∘ u = e := by funext x; exact congrArg Subtype.val (enum.apply_symm_apply _)
  let eb : RelEmbedding a b := {
    toFun := u
    injective := by
      intro x y hxy
      apply e.injective
      exact (congrFun hq x).symm.trans ((congrArg q hxy).trans (congrFun hq y))
    map_rel := by
      intro r R t
      change a.rel R t ↔ K.rel R (q ∘ u ∘ t)
      rw [← Function.comp_assoc, hq]
      exact e.map_rel R t }
  refine ⟨v.comp eb, i, ?_⟩
  intro x
  refine ⟨hv (u x), ?_⟩
  have hx := (he x).2
  have hxs : e x ∈ s := (he x).1
  dsimp only [lifted] at hx
  rw [dif_pos hxs] at hx
  exact hx

/-- Equality of induced ages preserves age indivisibility. This proves the
compactness step of the paper without a countability assumption. -/
theorem ageIndivisible_of_sameAge {K : RelStructure L X} {P : Set X}
    {N : RelStructure L Y} {Q : Set Y} (hP : AgeIndivisibleOn K P)
    (hage : SameAgeOn K P N Q) : AgeIndivisibleOn N Q := by
  classical
  intro r χ
  by_contra hnone
  have hex : ∀ i : Fin (r + 1), ∃ (n : ℕ) (a : RelStructure L (Fin n)),
      InAgeOn N Q a ∧ ¬ InAgeOn N (Q ∩ {x | χ x = i}) a := by
    intro i
    have hn : ¬ SameAgeOn N Q N (Q ∩ {x | χ x = i}) :=
      fun h => hnone ⟨i, h⟩
    unfold SameAgeOn at hn
    push Not at hn
    obtain ⟨n, a, hn⟩ := hn
    have hsub : InAgeOn N (Q ∩ {x | χ x = i}) a → InAgeOn N Q a :=
      inAgeOn_mono Set.inter_subset_left
    rcases hn with hn | hn
    · exact ⟨n, a, hn.1, hn.2⟩
    · exact False.elim (hn.1 (hsub hn.2))
  choose size pattern hp hn using hex
  choose e he using fun i => (hage (size i) (pattern i)).mpr (hp i)
  let s : Finset X := Finset.univ.biUnion (fun i => Finset.univ.image (e i))
  have hs : (↑s : Set X) ⊆ P := by
    intro x hx
    obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hxi
    exact he i y
  let enum : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let q : Fin (Fintype.card s) → X := fun i => (enum i).val
  let b := K.pullback q
  have hb : InAgeOn K P b :=
    ⟨RelEmbedding.pullback K q (Subtype.val_injective.comp enum.injective),
      fun i => hs (enum i).property⟩
  have hw := finiteMonoWitness_of_ageIndivisible hP b hb r
  obtain ⟨v, i, hv⟩ := finiteMonoWitness_transfer hage hw χ
  have hmem : ∀ y, e i y ∈ s := by
    intro y
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
      Finset.mem_image.mpr ⟨y, Finset.mem_univ y, rfl⟩⟩
  let u : Fin (size i) → Fin (Fintype.card s) :=
    fun y => enum.symm ⟨e i y, hmem y⟩
  have hq : q ∘ u = e i := by funext y; exact congrArg Subtype.val (enum.apply_symm_apply _)
  let eb : RelEmbedding (pattern i) b := {
    toFun := u
    injective := by
      intro x y hxy
      apply (e i).injective
      exact (congrFun hq x).symm.trans ((congrArg q hxy).trans (congrFun hq y))
    map_rel := by
      intro j R t
      change (pattern i).rel R t ↔ K.rel R (q ∘ u ∘ t)
      rw [← Function.comp_assoc, hq]
      exact (e i).map_rel R t }
  exact hn i ⟨v.comp eb, fun y => hv (u y)⟩

theorem sameAgeOn_induced (K : RelStructure L X) (P : Set X) :
    SameAgeOn (K.pullback (Subtype.val : P → X)) Set.univ K P := by
  intro n a
  constructor
  · rintro ⟨e, _⟩
    let into := RelEmbedding.pullback K (Subtype.val : P → X) Subtype.val_injective
    exact ⟨into.comp e, fun x => (e x).property⟩
  · rintro ⟨e, he⟩
    exact ⟨{
      toFun := fun x => ⟨e x, he x⟩
      injective := fun x y h => e.injective (congrArg Subtype.val h)
      map_rel := fun R t => e.map_rel R t }, fun _ => Set.mem_univ _⟩

/-- Forgetting added links preserves age indivisibility. Full expanded
finite tables are transferred before taking the reduct. -/
theorem ageIndivisible_reduct {S : Language} (ι : LanguageInclusion L S)
    (N : RelStructure S X) (hind : AgeIndivisibleOn N Set.univ) :
    AgeIndivisibleOn (N.reduct ι) Set.univ := by
  intro r χ
  obtain ⟨i, hi⟩ := hind r χ
  refine ⟨i, ?_⟩
  intro n a
  constructor
  · rintro ⟨e, _⟩
    let p := N.pullback e
    have hp : InAgeOn N Set.univ p :=
      ⟨RelEmbedding.pullback N e e.injective, fun _ => Set.mem_univ _⟩
    obtain ⟨u, hu⟩ := (hi n p).mp hp
    refine ⟨{
      toFun := u
      injective := u.injective
      map_rel := by
        intro k R t
        exact (e.map_rel R t).trans (u.map_rel (ι.relMap k R) t) }, hu⟩
  · exact inAgeOn_mono Set.inter_subset_left

end CombinedRamsey.Negative
