import RelationalRamsey632.Source.NormalForms
import RelationalRamsey632.Transfer.Source
import RelationalRamsey632.Transfer.Rigidity
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finite.Prod

/-! The literal full normal-form relational source, on labelled nodes.
Every positive-arity predicate specifies one ordered compressed tuple.
This is an interpreted structure, rather than a list of source properties. -/

namespace RelationalRamsey632.Source

variable (A : ℕ → Type) (U : Type)

abbrev Vertex := U × Node A 0

def normalFormLanguage : Language where
  Rel r := {_p : Fin r → Vertex A U // 0 < r}

noncomputable def normalFormStructure : RelStructure (normalFormLanguage A U) (Vertex A U) where
  rel R t := Function.Injective t ∧ normalForm t = R.val

theorem normalFormStructure_positive : (normalFormLanguage A U).Positive :=
  ⟨fun R => Nat.lt_irrefl 0 R.property⟩

theorem normalFormStructure_injective : (normalFormStructure A U).InjectiveRelations := by
  intro r R t _ h
  exact h.1

noncomputable def nodeEquivSigma (i : ℕ) : Node A i ≃ Σ n, Level A i n where
  toFun t := ⟨t.height, t.table⟩
  invFun t := ⟨t.fst, t.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem nodeCountable [∀ j, Fintype (A j)] (i : ℕ) : Countable (Node A i) :=
  Countable.of_equiv (Σ n, Level A i n) (nodeEquivSigma A i).symm

theorem vertexCountable [∀ j, Fintype (A j)] [Countable U] : Countable (Vertex A U) := by
  haveI := nodeCountable A 0
  infer_instance

theorem normalFormLanguage_countable [∀ j, Fintype (A j)] [Countable U] :
    Countable (Sigma (normalFormLanguage A U).Rel) := by
  haveI := vertexCountable A U
  haveI : ∀ r, Countable ((normalFormLanguage A U).Rel r) := fun r => by
    change Countable {_p : Fin r → Vertex A U // 0 < r}
    infer_instance
  infer_instance

theorem normalForm_permutation {n : ℕ} (t : Fin n → Vertex A U) (σ : Equiv.Perm (Fin n)) :
    normalForm (t ∘ σ) = normalForm t ∘ σ := by
  have hp : tupleProjections (t ∘ σ) = tupleProjections t := by
    apply Set.ext
    intro x
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨σ i, hi⟩
    · rintro ⟨i, hi⟩
      refine ⟨σ.symm i, ?_⟩
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi
  have hl : tupleLevels (t ∘ σ) = tupleLevels t := by
    apply Finset.coe_injective
    rw [tupleLevels_coe, tupleLevels_coe, hp]
  funext j
  simp only [normalForm, hl, Function.comp_apply]

theorem embeddings_iff_normalForms (f : Vertex A U → Vertex A U) :
    Transfer.IsEmbeddingMap (normalFormStructure A U) (normalFormStructure A U) f ↔
      Function.Injective f ∧
        ∀ n, 0 < n → ∀ t : Fin n → Vertex A U, Function.Injective t →
          normalForm (f ∘ t) = normalForm t := by
  constructor
  · rintro ⟨hi, hm⟩
    refine ⟨hi, ?_⟩
    intro n hn t ht
    have h : (normalFormStructure A U).rel ⟨normalForm t, hn⟩ t := ⟨ht, rfl⟩
    exact ((hm n ⟨normalForm t, hn⟩ t).mp h).2
  · rintro ⟨hi, hn⟩
    refine ⟨hi, ?_⟩
    intro n R t
    change (Function.Injective t ∧ normalForm t = R.val) ↔
      (Function.Injective (f ∘ t) ∧ normalForm (f ∘ t) = R.val)
    rw [hi.of_comp_iff t]
    by_cases ht : Function.Injective t
    · rw [hn n R.property t ht]
    · simp only [ht, false_and]

theorem normalForm_of_finiteEmbedding {F : Type}
    (p : RelStructure (normalFormLanguage A U) F)
    (e f : RelEmbedding p (normalFormStructure A U))
    {n : ℕ} (hn : 0 < n) (t : Fin n → F) (ht : Function.Injective t) :
    normalForm (e ∘ t) = normalForm (f ∘ t) := by
  let R : (normalFormLanguage A U).Rel n := ⟨normalForm (e ∘ t), hn⟩
  have he : (normalFormStructure A U).rel R (e ∘ t) := ⟨e.injective.comp ht, rfl⟩
  exact ((f.map_rel R t).mp ((e.map_rel R t).mpr he)).2.symm

theorem normalForm_finite_rigid {F : Type} [Finite F]
    (p : RelStructure (normalFormLanguage A U) F)
    (he : Nonempty (RelEmbedding p (normalFormStructure A U))) : Transfer.Rigid p := by
  classical
  letI := Fintype.ofFinite F
  intro σ hσ
  by_cases hn : 0 < Fintype.card F
  · let e := Classical.choice he
    let u : RelEmbedding p p := {
      toFun := σ
      injective := σ.injective
      map_rel := fun R t => (congrArg (fun z => z.rel R t) hσ).symm.to_iff }
    let E := Fintype.equivFin F
    let τ := E.symm.trans (σ.trans E)
    let t := e ∘ E.symm
    have hnf := normalForm_of_finiteEmbedding A U p e (e.comp u) hn E.symm E.symm.injective
    have heq : e.comp u ∘ E.symm = t ∘ τ := by
      funext j
      change e (σ (E.symm j)) = e (E.symm (E (σ (E.symm j))))
      rw [E.symm_apply_apply]
    rw [heq, normalForm_permutation] at hnf
    have hinj := normalForm_injective t (e.injective.comp E.symm.injective)
    have hτ : ∀ j, τ j = j := fun j => hinj ((congrFun hnf j).symm)
    apply Equiv.ext
    intro x
    apply E.injective
    change E (σ x) = E x
    simpa only [τ, Equiv.trans_apply, Equiv.symm_apply_apply] using hτ (E x)
  · haveI : IsEmpty F := Fintype.card_eq_zero_iff.mp (by omega)
    exact Subsingleton.elim _ _

end RelationalRamsey632.Source
