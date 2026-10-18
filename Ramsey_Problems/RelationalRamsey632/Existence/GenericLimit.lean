import RelationalRamsey632.Existence.OnePointStage
import RelationalRamsey632.Existence.OnePointAmalgam
import RelationalRamsey632.Existence.ExtensionConsequences
import RelationalRamsey632.Existence.Obstructions
import Mathlib.ModelTheory.DirectLimit
import Mathlib.Data.Finite.Prod
import Mathlib.SetTheory.Cardinal.Finite

/-!
The finite-stage generic construction and its actual first-order direct limit.
It simultaneously covers fixed-nullary ordinary finite languages and the
injective finite-per-arity convention.
-/

namespace RelationalRamsey632
namespace Existence
namespace GenericConstruction

variable (L : Language) (inj : Bool)

structure Stage where
  Domain : Type
  model : RelStructure L Domain
  admissible : Admissible inj model
  finite : Finite Domain

def initial (θ : L.Rel 0 → Prop) : Stage L inj where
  Domain := Empty
  model := nullaryOnly L θ Empty
  admissible := fun _ => nullaryOnly_injective L θ Empty
  finite := inferInstance

def next (hL : LocallyFiniteLanguage L inj) (A : Stage L inj) : Stage L inj := by
  letI := A.finite
  exact {
    Domain := OnePointStage.Domain (inj := inj) A.model
    model := OnePointStage.model (inj := inj) A.model
    admissible := OnePointStage.structure_admissible A.model
    finite := OnePointStage.finite_domain A.model hL }

def stage (hL : LocallyFiniteLanguage L inj) (θ : L.Rel 0 → Prop) : ℕ → Stage L inj
  | 0 => initial L inj θ
  | n + 1 => next L inj hL (stage hL θ n)

variable (hL : LocallyFiniteLanguage L inj) (θ : L.Rel 0 → Prop)

abbrev StageDomain (n : ℕ) := (stage L inj hL θ n).Domain

def stageModel (n : ℕ) : RelStructure L (StageDomain L inj hL θ n) :=
  (stage L inj hL θ n).model

instance stageFinite (n : ℕ) : Finite (StageDomain L inj hL θ n) :=
  (stage L inj hL θ n).finite

instance stageFirstOrder (n : ℕ) : L.toFirstOrder.Structure (StageDomain L inj hL θ n) :=
  (stageModel L inj hL θ n).toFirstOrder

def step (n : ℕ) :
    @FirstOrder.Language.Embedding L.toFirstOrder
      (StageDomain L inj hL θ n) (StageDomain L inj hL θ (n + 1))
      (stageFirstOrder L inj hL θ n) (stageFirstOrder L inj hL θ (n + 1)) :=
  (OnePointStage.oldEmbedding (stageModel L inj hL θ n)
    (stage L inj hL θ n).admissible).toFirstOrder

def maps (i j : ℕ) (hij : i ≤ j) :
    FirstOrder.Language.Embedding L.toFirstOrder
      (StageDomain L inj hL θ i) (StageDomain L inj hL θ j) :=
  FirstOrder.Language.DirectedSystem.natLERec (step L inj hL θ) i j hij

instance mapsDirected : DirectedSystem (StageDomain L inj hL θ)
    (fun i j hij => maps L inj hL θ i j hij) :=
  FirstOrder.Language.DirectedSystem.natLERec.directedSystem (step L inj hL θ)

abbrev Limit := FirstOrder.Language.DirectLimit (StageDomain L inj hL θ)
  (maps L inj hL θ)

noncomputable def limitModel : RelStructure L (Limit L inj hL θ) :=
  RelStructure.ofFirstOrder (inferInstance : L.toFirstOrder.Structure (Limit L inj hL θ))

noncomputable def ofStage (n : ℕ) :
    RelEmbedding (stageModel L inj hL θ n) (limitModel L inj hL θ) := by
  let e := FirstOrder.Language.DirectLimit.of L.toFirstOrder ℕ
    (StageDomain L inj hL θ) (maps L inj hL θ) n
  exact {
    toFun := e
    injective := e.injective
    map_rel := fun R t => (e.map_rel' R t).symm }

theorem countable_limit : Countable (Limit L inj hL θ) := by
  haveI : Countable ((n : ℕ) × StageDomain L inj hL θ n) := inferInstance
  change Countable (Quotient _)
  infer_instance

theorem exists_tuple_in_stage {T : Type} [Finite T]
    (x : T → Limit L inj hL θ) :
    ∃ (n : ℕ) (y : T → StageDomain L inj hL θ n),
      ∀ a, ofStage L inj hL θ n (y a) = x a := by
  obtain ⟨n, y, h⟩ := FirstOrder.Language.DirectLimit.exists_quotient_mk'_sigma_mk'_eq
    (StageDomain L inj hL θ) (maps L inj hL θ) x
  exact ⟨n, y, fun a => (congrFun h a).symm⟩

theorem limit_admissible : Admissible inj (limitModel L inj hL θ) := by
  intro hi r R t hr ht i j hij
  obtain ⟨n, u, hu⟩ := exists_tuple_in_stage L inj hL θ t
  have htu : ofStage L inj hL θ n ∘ u = t := funext hu
  have hR : (stageModel L inj hL θ n).rel R u := by
    apply ((ofStage L inj hL θ n).map_rel R u).mpr
    exact htu.symm ▸ ht
  apply (stage L inj hL θ n).admissible hi r R u hr hR
  apply (ofStage L inj hL θ n).injective
  exact (hu i).trans (hij.trans (hu j).symm)

theorem ofStage_succ (n : ℕ) (x : StageDomain L inj hL θ n) :
    ofStage L inj hL θ (n + 1) (Sum.inl x) = ofStage L inj hL θ n x := by
  have hm : maps L inj hL θ n (n + 1) (Nat.le_succ n) x = Sum.inl x := by
    simp [maps, FirstOrder.Language.DirectedSystem.natLERec,
      Nat.leRecOn_succ, Nat.leRecOn_self, step, RelEmbedding.toFirstOrder,
      OnePointStage.oldEmbedding, RelEmbedding.comp, OnePointStage.extensionEmbedding,
      OnePointStage.place, OnePointExtension.inclusion]
    rfl
  have h := FirstOrder.Language.DirectLimit.of_f
    (f := maps L inj hL θ) (i := n) (j := n + 1) (hij := Nat.le_succ n) (x := x)
  exact hm ▸ h

theorem extension_property : OnePointExtensionProperty inj (limitModel L inj hL θ) := by
  classical
  intro n B hB f
  obtain ⟨k, u, hu⟩ := exists_tuple_in_stage L inj hL θ f.toFun
  let A := stageModel L inj hL θ k
  let ef : RelEmbedding (B.pullback Fin.castSucc) A := {
    toFun := u
    injective := fun i j hij => f.injective
      ((hu i).symm.trans ((congrArg (ofStage L inj hL θ k) hij).trans (hu j)))
    map_rel := fun R t => by
      have hc : f ∘ t = ofStage L inj hL θ k ∘ (u ∘ t) := by
        funext a
        exact (hu (t a)).symm
      have hf := f.map_rel R t
      rw [hc] at hf
      exact hf.trans ((ofStage L inj hL θ k).map_rel R (u ∘ t)).symm }
  let E := OnePointAmalgam.extension A B ef (stage L inj hL θ k).admissible hB
  let eB := OnePointAmalgam.embedding A B ef
  let eE := OnePointStage.extensionEmbedding A E
  let g := (ofStage L inj hL θ (k + 1)).comp (eE.comp eB)
  refine ⟨g, ?_⟩
  intro i
  change ofStage L inj hL θ (k + 1)
    (OnePointStage.place A E (OnePointAmalgam.place A B ef i.castSucc)) = f i
  rw [OnePointAmalgam.place_old]
  exact (ofStage_succ L inj hL θ k (u i)).trans (hu i)

theorem limit_nullary (R : L.Rel 0) (t : Fin 0 → Limit L inj hL θ) :
    (limitModel L inj hL θ).rel R t ↔ θ R := by
  have ht : ofStage L inj hL θ 0 ∘ (Fin.elim0 : Fin 0 → StageDomain L inj hL θ 0) = t := by
    funext i
    exact i.elim0
  have he := (ofStage L inj hL θ 0).map_rel R Fin.elim0
  rw [ht] at he
  have hold : (stageModel L inj hL θ 0).rel R Fin.elim0 ↔ θ R := by
    simp [stageModel, stage, initial, nullaryOnly]
  exact he.symm.trans hold

theorem card_stage_lower (n : ℕ) : n ≤ Nat.card (StageDomain L inj hL θ n) := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    haveI := OnePointExtension.finite (A := stageModel L inj hL θ n) hL
    haveI : Nonempty (OnePointExtension inj (stageModel L inj hL θ n)) :=
      ⟨OnePointExtension.default (stage L inj hL θ n).admissible⟩
    have hp : 0 < Nat.card (OnePointExtension inj (stageModel L inj hL θ n)) := Nat.card_pos
    have hc : Nat.card (StageDomain L inj hL θ (n + 1)) =
        Nat.card (StageDomain L inj hL θ n) +
          Nat.card (OnePointExtension inj (stageModel L inj hL θ n)) := by
      change Nat.card (StageDomain L inj hL θ n ⊕
        OnePointExtension inj (stageModel L inj hL θ n)) = _
      exact Nat.card_sum
    rw [hc]
    omega

theorem infinite_limit : Infinite (Limit L inj hL θ) := by
  apply not_finite_iff_infinite.mp
  intro hf
  letI := hf
  have he := Nat.card_le_card_of_injective
    (ofStage L inj hL θ (Nat.card (Limit L inj hL θ) + 1))
    (ofStage L inj hL θ (Nat.card (Limit L inj hL θ) + 1)).injective
  have hl := card_stage_lower L inj hL θ (Nat.card (Limit L inj hL θ) + 1)
  omega

end GenericConstruction
end Existence
end RelationalRamsey632
