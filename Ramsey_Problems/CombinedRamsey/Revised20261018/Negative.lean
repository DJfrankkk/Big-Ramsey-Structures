import CombinedRamsey.Negative.FraisseConclusion

/-!
Literal negative-section interface for the 18 October manuscript.  The fixed
language, complete forbidden tables and generic are the actual objects of
the existing proof.  Replacing the manuscript's proof of age indivisibility
by a citation does not introduce a new premise: its prior Lean proof is reused.
-/

namespace CombinedRamsey.Revised20261018.Negative

open RelationalRamsey632 RelationalRamsey632.Transfer
open CombinedRamsey.Negative

/-- The manuscript's literal family-avoidance predicate uses induced
embeddings of every member of the one fixed finite family. -/
def AvoidsForbiddenFamily {X : Type} (A : RelStructure Lstar X) : Prop :=
  ∀ F : Fstar, ¬ Nonempty (RelEmbedding (forbiddenStructure F) A)

/-- The table-based class in the existing proof equals literal avoidance
of all fixed forbidden structures; no weaker homomorphism convention is used. -/
theorem forbStar_iff_literal_avoidance {X : Type} (A : RelStructure Lstar X) :
    ForbStar A ↔ A.InjectiveRelations ∧ AvoidsForbiddenFamily A := by
  constructor
  · rintro ⟨hinj, hforb⟩
    refine ⟨hinj, ?_⟩
    intro F
    have he : (Table.ofRel A).toRel = A := Table.toRel_ofRel A hinj
    cases F with
    | inl F =>
      change ¬ Nonempty (RelEmbedding F.val.toRel A)
      rw [← he]
      exact hforb.1 F.val F.property
    | inr F =>
      change ¬ Nonempty (RelEmbedding F.val.toRel A)
      rw [← he]
      exact hforb.2 F.val F.property
  · rintro ⟨hinj, hforb⟩
    refine ⟨hinj, ?_, ?_⟩
    · intro B hB
      have hf := hforb (.inl ⟨B,hB⟩)
      change ¬ Nonempty (RelEmbedding B.toRel A) at hf
      simpa only [Table.toRel_ofRel A hinj] using hf
    · intro B hB
      have hf := hforb (.inr ⟨B,hB⟩)
      change ¬ Nonempty (RelEmbedding B.toRel A) at hf
      simpa only [Table.toRel_ofRel A hinj] using hf

/-- The fixed generic has exactly the manuscript's induced forbidden age. -/
theorem age_exact_literal {X : Type} [Finite X] (A : RelStructure Lstar X) :
    Nonempty (RelEmbedding A Kstar) ↔
      A.InjectiveRelations ∧ AvoidsForbiddenFamily A :=
  (Kstar_age_exact A).trans (forbStar_iff_literal_avoidance A)

/-- Pure-delta tables mean the full singleton type from the statement,
including the absence of binary and ternary diagonal relations. -/
theorem pureDelta_iff_singleton_type {X : Type} (A : RelStructure Lstar X)
    (hinj : A.InjectiveRelations) :
    (Table.ofRel A).PureDelta ↔ ∀ x, HasPointType A deltaStar x := by
  constructor
  · intro h x
    apply RelStructure.ext_rel
    intro r R t
    cases R with
    | unary u =>
      have he : (fun _ : Fin 1 => x) ∘ t = ![x] := by
        funext i
        fin_cases i
        rfl
      change A.rel (.unary u) ((fun _ : Fin 1 => x) ∘ t) ↔ u = .V
      rw [he]
      exact h x u
    | binary b =>
      simp only [deltaStar, delta, deltaTable, RelStructure.pullback, Table.toRel, and_false]
      constructor
      · intro hrel
        have hi := hinj 2 (.binary b) ((fun _ : Fin 1 => x) ∘ t) (by omega) hrel
        exact (by decide : (0 : Fin 2) ≠ 1) (hi rfl)
      · exact False.elim
    | ternary b =>
      simp only [deltaStar, delta, deltaTable, RelStructure.pullback, Table.toRel, and_false]
      constructor
      · intro hrel
        have hi := hinj 3 (.ternary b) ((fun _ : Fin 1 => x) ∘ t) (by omega) hrel
        exact (by decide : (0 : Fin 3) ≠ 1) (hi rfl)
      · exact False.elim
  · intro h x u
    have he := congrArg (fun B : RelStructure Lstar (Fin 1) => B.rel (.unary u) ![0]) (h x)
    have he' : A.rel (.unary u) (fun _ : Fin 1 => x) ↔ u = .V := by
      simpa [RelStructure.pullback, deltaStar, delta, deltaTable,
        Table.toRel, Function.comp_def] using Iff.of_eq he
    have hfun : (fun _ : Fin 1 => x) = ![x] := by
      funext i
      fin_cases i
      rfl
    change A.rel (.unary u) ![x] ↔ u = .V
    rwa [hfun] at he'

/-- Proposition `neg:age-characterization` in literal relational semantics, with arbitrary finite
injective B and no E-completeness condition on B. -/
theorem actual_realization_age_formula {X : Type} [Finite X]
    {k : ℕ} (hk : 0 < k) (H : Digraph (Fin k))
    (A : RelStructure Lstar X) (hinj : A.InjectiveRelations) :
    InAgeOn Kstar (EncodedRealizations H Kstar (ConcreteGeneric.baseEmbedding H)) A ↔
      (∀ x, HasPointType A deltaStar x) ∧
      ∀ h, Nonempty (Hom ((Table.ofRel A).localGraph h) H) := by
  have hf := realization_age_formula H Kstar (ConcreteGeneric.baseEmbedding H) hk
    ConcreteGeneric.natModel_legal.2 ConcreteGeneric.natModel_rel_finite_extension
    (Table.ofRel A) (Table.ofRel_canonical A hinj)
  rw [Table.toRel_ofRel A hinj, pureDelta_iff_singleton_type A hinj] at hf
  exact hf

/-- One fixed language/family/generic witnesses `thm:negative` / `neg:main`.
The objects are chosen before every colour and finite-degree quantifier. -/
theorem negative_main :
    Finite (Sigma Lstar.Rel) ∧
    (∀ r, 3 < r → IsEmpty (Lstar.Rel r)) ∧
    Finite Fstar ∧
    (∀ F : Fstar, forbiddenCard F = 3 ∨ forbiddenCard F = 4) ∧
    (∀ F : Fstar, Irreducible (forbiddenStructure F)) ∧
    (∀ t, ¬ EmbeddingDegreeBound deltaStar Kstar t) ∧
    (∀ t, ¬ CopyDegreeBound deltaStar Kstar t) :=
  ⟨Lstar_finite, Lstar_maximum_arity, Fstar_finite, Fstar_size,
    Fstar_irreducible, deltaStar_no_finite_embedding_degree,
    deltaStar_no_finite_copy_degree⟩

/-- The strengthening to every finite age member containing a delta vertex
is simultaneous for embedding and actual finite-subset copy degrees. -/
theorem containing_delta_infinite_degrees {X : Type} [Finite X]
    (A : RelStructure Lstar X) (hA : Nonempty (RelEmbedding A Kstar))
    (v : X) (hv : HasPointType A deltaStar v) :
    (∀ t, ¬ EmbeddingDegreeBound A Kstar t) ∧
      (∀ t, ¬ CopyDegreeBound A Kstar t) :=
  containing_delta_no_finite_degrees A hA v hv

/-- Corollary `neg:no-brs`, ordinary precompact big Ramsey structures. -/
theorem no_big_ramsey_structure {S : Language} (ι : LanguageInclusion Lstar S)
    (Z : RelStructure S ℕ) : ¬ OrdinaryBigRamseyExpansion ι Z :=
  no_precompact_big_ramsey_structure ι Z

/-- The stronger singleton degree-one obstruction in Corollary `neg:no-brs`. -/
theorem no_singleton_degree_one_expansion {S : Language} (ι : LanguageInclusion Lstar S)
    (Z : RelStructure S ℕ) (hZ : Z.reduct ι = Kstar)
    (hfinite : (RelStructure.palette deltaStar Kstar Z).Finite)
    (hR : ∀ p ∈ RelStructure.palette deltaStar Kstar Z, SourceDegreeOne Z p) : False :=
  no_precompact_singleton_degree_one ι Z hZ hfinite hR

end CombinedRamsey.Revised20261018.Negative
