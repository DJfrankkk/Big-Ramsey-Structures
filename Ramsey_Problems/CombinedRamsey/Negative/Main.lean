import CombinedRamsey.Negative.Cycles
import CombinedRamsey.Negative.ConcreteGeneric
import CombinedRamsey.Negative.PersistenceComplete

/-! The fixed finite constrained counterexample. All colourings and degree
obstructions are internally proved for the actual constructed structure. -/

namespace CombinedRamsey.Negative

open RelationalRamsey632 RelationalRamsey632.Transfer

abbrev Lstar := language
abbrev Fstar := ForbiddenFamily
noncomputable abbrev Kstar := ConcreteGeneric.natModel

def deltaStar : RelStructure Lstar (Fin 1) := delta.pullback (fun _ => ())

theorem Lstar_finite : Finite (Sigma Lstar.Rel) := by
  classical
  let f : (Sigma Symbol) → Unary ⊕ Binary ⊕ Ternary := fun s => match s with
    | ⟨_,.unary u⟩ => .inl u
    | ⟨_,.binary b⟩ => .inr (.inl b)
    | ⟨_,.ternary t⟩ => .inr (.inr t)
  apply Finite.of_injective f
  intro s t h
  cases s with
  | mk _ s =>
    cases s <;> cases t with
    | mk _ t => cases t <;> simp_all [f]

theorem Lstar_maximum_arity : ∀ r, 3 < r → IsEmpty (Lstar.Rel r) := language_maximum_arity

theorem Fstar_finite : Finite Fstar := forbiddenFamily_finite

def forbiddenCard : Fstar → ℕ
  | .inl _ => 3
  | .inr _ => 4

def forbiddenStructure (F : Fstar) : RelStructure Lstar (Fin (forbiddenCard F)) :=
  match F with
  | .inl F => F.val.toRel
  | .inr F => F.val.toRel

theorem Fstar_size (F : Fstar) : forbiddenCard F = 3 ∨ forbiddenCard F = 4 := by
  cases F <;> simp [forbiddenCard]

theorem Fstar_irreducible (F : Fstar) : Irreducible (forbiddenStructure F) := by
  cases F with
  | inl F => exact forbidden3_irreducible F.property
  | inr F => exact forbidden4_irreducible F.property

def ForbStar {V : Type} (A : RelStructure Lstar V) : Prop :=
  A.InjectiveRelations ∧ Forb (Table.ofRel A)

theorem Kstar_age_exact {V : Type} [Finite V] (A : RelStructure Lstar V) :
    Nonempty (RelEmbedding A Kstar) ↔ ForbStar A := by
  rw [ConcreteGeneric.natModel_age_exact]
  exact and_congr Iff.rfl (legal_iff_forb (Table.ofRel A))

theorem Kstar_ultrahomogeneous :
    @FirstOrder.Language.IsUltrahomogeneous Lstar.toFirstOrder ℕ Kstar.toFirstOrder :=
  ConcreteGeneric.natModel_ultrahomogeneous

theorem Kstar_free_amalgamation {X Y Z : Type} {A : RelStructure Lstar X}
    {B : RelStructure Lstar Y} {C : RelStructure Lstar Z}
    (hB : ForbStar B) (hC : ForbStar C)
    (f : RelEmbedding A B) (g : RelEmbedding A C) :
    ForbStar (RelationalRamsey632.Existence.FreeAmalgamation.model f g) := by
  have hb : LegalModel B := ⟨hB.1,(legal_iff_forb (Table.ofRel B)).mpr hB.2⟩
  have hc : LegalModel C := ⟨hC.1,(legal_iff_forb (Table.ofRel C)).mpr hC.2⟩
  have h := legalModel_free_amalgam hb hc f g
  exact ⟨h.1,(legal_iff_forb _).mp h.2⟩

theorem labelled_type_deltaStar {k : ℕ} (H : Digraph (Fin k)) :
    (labelledType H).pullback (fun _ : Fin 1 => Sum.inr ()) = deltaStar := by
  have h := congrArg (fun D : RelStructure language Unit => D.pullback (fun _ : Fin 1 => ()))
    (labelled_type_singleton H)
  exact h

theorem Kstar_persistent_colours : PersistentVertexColourings Kstar deltaStar := by
  apply persistent_colours_of_incomparable_realized_types Kstar deltaStar
    ConcreteGeneric.natModel_finite_homogeneous ConcreteGeneric.natModel_age_shared_free
  intro q
  let size : Fin (q+1) → ℕ := fun i => boundarySize (primeCycle i.val)
  let type : ∀ i, RelStructure Lstar (Fin (size i) ⊕ Unit) :=
    fun i => labelledType (primeCycle i.val)
  let original : ∀ i, Boundary size type Kstar i :=
    fun i => labelledBase (primeCycle i.val) Kstar (ConcreteGeneric.baseEmbedding (primeCycle i.val))
  refine ⟨size,type,original,?_,?_,?_⟩
  · intro i
    exact ConcreteGeneric.labelled_realizations_nonempty (primeCycle i.val)
  · intro i
    exact labelled_type_deltaStar (primeCycle i.val)
  · intro i j hij
    have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hno := prime_cycles_incomparable hval
    refine ⟨Nat.card (Unit ⊕ Fin (primeSequence i.val)),hubPattern (primeCycle i.val),?_⟩
    exact ConcreteGeneric.labelled_separating_pattern (primeSequence_prime i.val).pos
      (primeSequence_prime j.val).pos (primeCycle i.val) (primeCycle j.val) hno

theorem deltaStar_in_age : Nonempty (RelEmbedding deltaStar Kstar) := by
  obtain ⟨_,hχ⟩ := Kstar_persistent_colours 0
  obtain ⟨x,hx,_⟩ := hχ (RelationalRamsey632.RelEmbedding.refl Kstar) 0
  exact ⟨singletonEmbedding x hx⟩

theorem deltaStar_point : HasPointType deltaStar deltaStar (0 : Fin 1) := by
  have he : (fun _ : Fin 1 => (0 : Fin 1)) = id := by
    funext i; exact Subsingleton.elim _ _
  rw [HasPointType,he]
  rfl

theorem deltaStar_no_finite_embedding_degree :
    ∀ t, ¬ EmbeddingDegreeBound deltaStar Kstar t :=
  no_finite_embedding_degree Kstar_persistent_colours ConcreteGeneric.natModel_finite_homogeneous
    deltaStar_in_age 0 deltaStar_point

theorem deltaStar_no_finite_copy_degree : ∀ t, ¬ CopyDegreeBound deltaStar Kstar t :=
  no_finite_copy_degree Kstar_persistent_colours ConcreteGeneric.natModel_finite_homogeneous
    deltaStar_in_age 0 deltaStar_point

theorem containing_delta_no_finite_degrees {V : Type} [Finite V]
    (A : RelStructure Lstar V) (ha : Nonempty (RelEmbedding A Kstar))
    (v : V) (hv : HasPointType A deltaStar v) :
    (∀ t, ¬ EmbeddingDegreeBound A Kstar t) ∧ (∀ t, ¬ CopyDegreeBound A Kstar t) :=
  ⟨no_finite_embedding_degree Kstar_persistent_colours ConcreteGeneric.natModel_finite_homogeneous ha v hv,
    no_finite_copy_degree Kstar_persistent_colours ConcreteGeneric.natModel_finite_homogeneous ha v hv⟩

theorem no_precompact_singleton_degree_one {S : Language} (ι : LanguageInclusion Lstar S)
    (Z : RelStructure S ℕ) (hZ : Z.reduct ι = Kstar)
    (hfinite : (RelStructure.palette deltaStar Kstar Z).Finite)
    (hR : ∀ p ∈ RelStructure.palette deltaStar Kstar Z, SourceDegreeOne Z p) : False :=
  no_precompact_singleton_degree_one_expansion Kstar_persistent_colours
    ConcreteGeneric.natModel_finite_homogeneous deltaStar_in_age ι Z hZ hfinite hR

def PrecompactDegreeOneExpansion {S : Language} (ι : LanguageInclusion Lstar S)
    (Z : RelStructure S ℕ) : Prop :=
  Z.reduct ι = Kstar ∧
  (∀ n (A : RelStructure Lstar (Fin n)), Nonempty (RelEmbedding A Kstar) →
    (RelStructure.palette A Kstar Z).Finite) ∧
  (∀ n (A : RelStructure Lstar (Fin n)), Nonempty (RelEmbedding A Kstar) →
    ∀ p ∈ RelStructure.palette A Kstar Z, SourceDegreeOne Z p)

theorem no_precompact_degree_one_expansion {S : Language} (ι : LanguageInclusion Lstar S)
    (Z : RelStructure S ℕ) : ¬ PrecompactDegreeOneExpansion ι Z := by
  rintro ⟨hred,hfin,hR⟩
  exact no_precompact_singleton_degree_one ι Z hred (hfin 1 deltaStar deltaStar_in_age)
    (hR 1 deltaStar deltaStar_in_age)

end CombinedRamsey.Negative
