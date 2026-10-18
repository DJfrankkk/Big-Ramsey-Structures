import RelationalRamsey632.Transfer.CoarseRecurrence

namespace RelationalRamsey632.Transfer

open RelStructure
open scoped BigOperators

variable {L S : Language} {X M : Type}

/-- A single approximate return map corrects every selected source type.
Its quantification includes every qualifying source embedding, not only
the embeddings induced by the initial coding map. -/
theorem support_return_map (ι : LanguageInclusion L S)
    {J : Type} [Fintype J] {A : J → Type} [∀ j, Finite (A j)]
    (a : ∀ j, RelStructure L (A j))
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (hN : N.reduct ι = B) {ψ : M → X} (hψ : Approximate K B ψ)
    (i : RelEmbedding K B) (ha : ∀ j, Nonempty (RelEmbedding (a j) K))
    (hfin : ∀ j, (palette (a j) K (N.pullback i)).Finite)
    (hunav : ∀ j, Unavoidable (a j) K (N.pullback i))
    (hR : ∀ j p, p ∈ palette (a j) K (N.pullback i) → SourceDegreeOne N p) :
    ∃ Q : M → X, Approximate K B Q ∧
      ∀ j (u : RelEmbedding (a j) B),
        N.pullback u ∈ palette (a j) K (N.pullback i) →
          (N.pullback i).pullback (Q ∘ u) = N.pullback u := by
  classical
  let Y := N.pullback i
  let P : J → Type := fun j => palette (a j) K Y
  letI : ∀ j, Fintype (P j) := fun j => (hfin j).fintype
  obtain ⟨ζ, π, hsurj, hact⟩ :=
    selected_source_action ι a hN hψ i ha hfin hunav hR (RelEmbedding.refl K)
  let ζb := toBaseEmbedding ι hN hN ζ
  let r : M → X := ψ ∘ ζ
  have hr : Approximate K B r := approximate_precompose hψ ζb
  let f := approximateComp hr i
  let q := ∑ j, Fintype.card (P j)
  have hq : ∀ j, Fintype.card (P j) ≤ q := by
    intro j
    exact Finset.single_le_sum (fun k _ => Nat.zero_le (Fintype.card (P k)))
      (Finset.mem_univ j)
  let F := embeddingIterate f (q.factorial - 1)
  refine ⟨F ∘ r, approximate_postcompose hr F, ?_⟩
  intro j u hp
  let typeOf : RelEmbedding (a j) K → P j := fun v => ⟨Y.pullback v, ⟨v, rfl⟩⟩
  let ru := approximateEmbedding hr (ha j) u
  let p : P j := ⟨N.pullback u, hp⟩
  have hsource : typeOf ru = π j p := by
    apply Subtype.ext
    exact hact j u hp
  have hf : ∀ v, typeOf (f.comp v) = π j (typeOf v) := by
    intro v
    apply Subtype.ext
    exact hact j (i.comp v) ⟨v, rfl⟩
  have hsem : Function.Semiconj typeOf (fun v => f.comp v) (π j) := hf
  have hper := Generic3Ramsey.Palette.surjective_iterate_factorial
    (π j) (hsurj j) q (hq j)
  have heq : q.factorial - 1 + 1 = q.factorial :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_pos q).ne')
  have hret : typeOf (F.comp ru) = p := by
    rw [show F.comp ru = (fun v => f.comp v)^[q.factorial - 1] ru
      from embeddingIterate_comp f ru _]
    rw [hsem.iterate_right, hsource, ← Function.iterate_succ_apply,
      Nat.succ_eq_add_one, heq, hper]
    rfl
  exact congrArg Subtype.val hret

/-- Supportedness records the complete selected pullbacks on every small
embedding into the input finite structure. -/
def Supported {J : Type} {A : J → Type}
    (a : ∀ j, RelStructure L (A j))
    {F : Type} (b : RelStructure L F) (K : RelStructure L X)
    (Y : RelStructure S X) (N : RelStructure S M)
    {B : RelStructure L M} (u : RelEmbedding b B) : Prop :=
  ∀ j (h : RelEmbedding (a j) b), N.pullback (u.comp h) ∈ palette (a j) K Y

/-- A supported source embedding is transported into K with exactly the
same selected restrictions. This is the semantic realization statement
needed for the finite coarse diagrams of Section 6. -/
theorem supported_transport (ι : LanguageInclusion L S)
    {J : Type} [Fintype J] {A : J → Type} [∀ j, Finite (A j)]
    (a : ∀ j, RelStructure L (A j))
    {K : RelStructure L X} {B : RelStructure L M} {N : RelStructure S M}
    (hN : N.reduct ι = B) {ψ : M → X} (hψ : Approximate K B ψ)
    (i : RelEmbedding K B) (ha : ∀ j, Nonempty (RelEmbedding (a j) K))
    (hfin : ∀ j, (palette (a j) K (N.pullback i)).Finite)
    (hunav : ∀ j, Unavoidable (a j) K (N.pullback i))
    (hR : ∀ j p, p ∈ palette (a j) K (N.pullback i) → SourceDegreeOne N p) :
    ∃ Q : M → X, ∃ hQ : Approximate K B Q,
      ∀ (F : Type) [Finite F] (b : RelStructure L F)
        (hb : Nonempty (RelEmbedding b K)) (u : RelEmbedding b B),
        Supported a b K (N.pullback i) N u →
          ∀ j (h : RelEmbedding (a j) b),
            (N.pullback i).pullback
              ((approximateEmbedding hQ hb u).comp h)
                = N.pullback (u.comp h) := by
  obtain ⟨Q, hQ, hret⟩ := support_return_map ι a hN hψ i ha hfin hunav hR
  refine ⟨Q, hQ, ?_⟩
  intro F _ b hb u hu j h
  exact hret j (u.comp h) (hu j h)

end RelationalRamsey632.Transfer
