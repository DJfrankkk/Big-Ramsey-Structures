import RelationalRamsey632.Existence.GenericLimit

/-! An actual direct-limit construction for a hereditary finite class.
The selected extensions, structures and embeddings are concrete. The
class closure rules are explicit and must be instantiated by a legal
class; no existence theorem or Fraisse-limit oracle is assumed. -/

namespace CombinedRamsey.Negative.ConstrainedGeneric

open RelationalRamsey632 RelationalRamsey632.Existence

abbrev Predicate (L : Language) := {X : Type} → RelStructure L X → Prop

variable {L : Language} (P : Predicate L) {X : Type}

abbrev Extensions (A : RelStructure L X) := {E : OnePointExtension true A // P E.model}

abbrev NextDomain (A : RelStructure L X) := X ⊕ Extensions P A

def inclusionMap (A : RelStructure L X) : NextDomain P A → OnePointStage.Domain (inj := true) A :=
  Sum.map id Subtype.val

theorem inclusionMap_injective (A : RelStructure L X) :
    Function.Injective (inclusionMap P A) :=
  Sum.map_injective.mpr ⟨Function.injective_id, Subtype.val_injective⟩

def nextModel (A : RelStructure L X) : RelStructure L (NextDomain P A) :=
  (OnePointStage.model (inj := true) A).pullback (inclusionMap P A)

def oldEmbedding (A : RelStructure L X) (hA : A.InjectiveRelations) :
    RelEmbedding A (nextModel P A) where
  toFun := Sum.inl
  injective := Sum.inl_injective
  map_rel R t := (OnePointStage.oldEmbedding A (fun _ => hA)).map_rel R t

def place (A : RelStructure L X) (E : Extensions P A) : X ⊕ Unit → NextDomain P A :=
  Sum.elim Sum.inl (fun _ => Sum.inr E)

theorem place_injective (A : RelStructure L X) (E : Extensions P A) :
    Function.Injective (place P A E) := by
  intro a b h
  cases a <;> cases b <;> simp_all [place]

def extensionEmbedding (A : RelStructure L X) (E : Extensions P A) :
    RelEmbedding E.val.model (nextModel P A) where
  toFun := place P A E
  injective := place_injective P A E
  map_rel R t := by
    have he : inclusionMap P A ∘ place P A E = OnePointStage.place A E.val := by
      funext x
      cases x <;> rfl
    change E.val.model.rel R t ↔
      (OnePointStage.model (inj := true) A).rel R ((inclusionMap P A ∘ place P A E) ∘ t)
    rw [he]
    exact (OnePointStage.extensionEmbedding A E.val).map_rel R t

theorem nextModel_injective (A : RelStructure L X) : (nextModel P A).InjectiveRelations :=
  RelStructure.injectiveRelations_pullback
    ((OnePointStage.structure_admissible A) rfl) (inclusionMap P A)

theorem extensions_finite (hL : L.FinitePerArity) (A : RelStructure L X) [Finite X] :
    Finite (Extensions P A) := by
  haveI := OnePointExtension.finite (A := A) (inj := true) hL
  infer_instance

theorem nextDomain_finite (hL : L.FinitePerArity) (A : RelStructure L X) [Finite X] :
    Finite (NextDomain P A) := by
  haveI := extensions_finite P hL A
  infer_instance

structure Rules (P : Predicate L) where
  injective : ∀ {X : Type} (A : RelStructure L X), P A → A.InjectiveRelations
  empty : P (nullaryOnly L (fun _ => False) Empty)
  hereditary : ∀ {X Y : Type} (A : RelStructure L X), P A →
    ∀ f : Y → X, Function.Injective f → P (A.pullback f)
  finiteCharacter : ∀ {X : Type} (A : RelStructure L X),
    (∀ n (f : Fin n → X), Function.Injective f → P (A.pullback f)) → P A
  isolated : ∀ {X : Type} (A : RelStructure L X), P A →
    P (OnePointExtension.isolated A)
  amalgam : ∀ {X : Type} {n : ℕ} (A : RelStructure L X) (B : RelStructure L (Fin (n + 1))),
    P A → P B → ∀ f : RelEmbedding (B.pullback Fin.castSucc) A,
      P (OnePointAmalgam.model A B f)
  star : ∀ {X : Type} (A : RelStructure L X), P A → P (nextModel P A)

variable (L : Language) (P : Predicate L) (hL : L.FinitePerArity) (C : Rules P)

structure Stage where
  Domain : Type
  model : RelStructure L Domain
  legal : P model
  finite : Finite Domain

def initial : Stage L P where
  Domain := Empty
  model := nullaryOnly L (fun _ => False) Empty
  legal := C.empty
  finite := inferInstance

def next (A : Stage L P) : Stage L P := by
  letI := A.finite
  exact {
    Domain := NextDomain P A.model
    model := nextModel P A.model
    legal := C.star A.model A.legal
    finite := nextDomain_finite P hL A.model }

def stage : ℕ → Stage L P
  | 0 => initial L P C
  | n + 1 => next L P hL C (stage n)

abbrev StageDomain (n : ℕ) := (stage L P hL C n).Domain

def stageModel (n : ℕ) : RelStructure L (StageDomain L P hL C n) :=
  (stage L P hL C n).model

instance stageFinite (n : ℕ) : Finite (StageDomain L P hL C n) :=
  (stage L P hL C n).finite

instance stageFirstOrder (n : ℕ) : L.toFirstOrder.Structure (StageDomain L P hL C n) :=
  (stageModel L P hL C n).toFirstOrder

def step (n : ℕ) :
    @FirstOrder.Language.Embedding L.toFirstOrder
      (StageDomain L P hL C n) (StageDomain L P hL C (n + 1))
      (stageFirstOrder L P hL C n) (stageFirstOrder L P hL C (n + 1)) :=
  (oldEmbedding P (stageModel L P hL C n)
    (C.injective _ (stage L P hL C n).legal)).toFirstOrder

def maps (i j : ℕ) (hij : i ≤ j) :
    FirstOrder.Language.Embedding L.toFirstOrder
      (StageDomain L P hL C i) (StageDomain L P hL C j) :=
  FirstOrder.Language.DirectedSystem.natLERec (step L P hL C) i j hij

instance mapsDirected : DirectedSystem (StageDomain L P hL C)
    (fun i j hij => maps L P hL C i j hij) :=
  FirstOrder.Language.DirectedSystem.natLERec.directedSystem (step L P hL C)

abbrev Limit := FirstOrder.Language.DirectLimit (StageDomain L P hL C) (maps L P hL C)

noncomputable def limitModel : RelStructure L (Limit L P hL C) :=
  RelStructure.ofFirstOrder (inferInstance : L.toFirstOrder.Structure (Limit L P hL C))

noncomputable def ofStage (n : ℕ) :
    RelEmbedding (stageModel L P hL C n) (limitModel L P hL C) := by
  let e := FirstOrder.Language.DirectLimit.of L.toFirstOrder ℕ
    (StageDomain L P hL C) (maps L P hL C) n
  exact {
    toFun := e
    injective := e.injective
    map_rel := fun R t => (e.map_rel' R t).symm }

theorem countable_limit : Countable (Limit L P hL C) := by
  haveI : Countable ((n : ℕ) × StageDomain L P hL C n) := inferInstance
  change Countable (Quotient _)
  infer_instance

theorem exists_tuple_in_stage {T : Type} [Finite T] (x : T → Limit L P hL C) :
    ∃ (n : ℕ) (y : T → StageDomain L P hL C n), ∀ a, ofStage L P hL C n (y a) = x a := by
  obtain ⟨n, y, h⟩ := FirstOrder.Language.DirectLimit.exists_quotient_mk'_sigma_mk'_eq
    (StageDomain L P hL C) (maps L P hL C) x
  exact ⟨n, y, fun a => (congrFun h a).symm⟩

theorem limit_legal : P (limitModel L P hL C) := by
  apply C.finiteCharacter
  intro n f hf
  obtain ⟨k, u, hu⟩ := exists_tuple_in_stage L P hL C f
  have hi : Function.Injective u := by
    intro i j hij
    exact hf ((hu i).symm.trans ((congrArg (ofStage L P hL C k) hij).trans (hu j)))
  have he : (limitModel L P hL C).pullback f = (stageModel L P hL C k).pullback u := by
    have hfu : (ofStage L P hL C k) ∘ u = f := funext hu
    rw [← hfu]
    exact congrArg (fun B => B.pullback u) (ofStage L P hL C k).pullback_eq
  rw [he]
  exact C.hereditary _ (stage L P hL C k).legal u hi

theorem limit_injective : (limitModel L P hL C).InjectiveRelations :=
  C.injective _ (limit_legal L P hL C)

theorem ofStage_succ (n : ℕ) (x : StageDomain L P hL C n) :
    ofStage L P hL C (n + 1) (Sum.inl x) = ofStage L P hL C n x := by
  have hm : maps L P hL C n (n + 1) (Nat.le_succ n) x = Sum.inl x := by
    simp [maps, FirstOrder.Language.DirectedSystem.natLERec,
      Nat.leRecOn_succ, Nat.leRecOn_self, step, RelEmbedding.toFirstOrder,
      oldEmbedding]
    rfl
  have h := FirstOrder.Language.DirectLimit.of_f
    (f := maps L P hL C) (i := n) (j := n + 1) (hij := Nat.le_succ n) (x := x)
  exact hm ▸ h

def ExtensionProperty (K : RelStructure L X) : Prop :=
  ∀ n (B : RelStructure L (Fin (n + 1))), P B →
    ∀ f : RelEmbedding (B.pullback Fin.castSucc) K,
      ∃ g : RelEmbedding B K, ∀ i : Fin n, g i.castSucc = f i

theorem extension_property : ExtensionProperty L P (limitModel L P hL C) := by
  classical
  intro n B hB f
  obtain ⟨k, u, hu⟩ := exists_tuple_in_stage L P hL C f.toFun
  let A := stageModel L P hL C k
  let ef : RelEmbedding (B.pullback Fin.castSucc) A := {
    toFun := u
    injective := fun i j hij => f.injective
      ((hu i).symm.trans ((congrArg (ofStage L P hL C k) hij).trans (hu j)))
    map_rel := fun R t => by
      have ht : f ∘ t = ofStage L P hL C k ∘ (u ∘ t) := funext (fun i => (hu (t i)).symm)
      have hh := f.map_rel R t
      rw [ht] at hh
      exact hh.trans ((ofStage L P hL C k).map_rel R (u ∘ t)).symm }
  let E : Extensions P A :=
    ⟨OnePointAmalgam.extension A B ef (fun _ => C.injective _ (stage L P hL C k).legal)
      (fun _ => C.injective _ hB), C.amalgam A B (stage L P hL C k).legal hB ef⟩
  let eB := OnePointAmalgam.embedding A B ef
  let eE := extensionEmbedding P A E
  let g := (ofStage L P hL C (k + 1)).comp (eE.comp eB)
  refine ⟨g, ?_⟩
  intro i
  change ofStage L P hL C (k + 1) (place P A E (OnePointAmalgam.place A B ef i.castSucc)) = f i
  rw [OnePointAmalgam.place_old]
  exact (ofStage_succ L P hL C k (u i)).trans (hu i)

theorem card_stage_lower (n : ℕ) : n ≤ Nat.card (StageDomain L P hL C n) := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    letI := (stage L P hL C n).finite
    haveI := extensions_finite P hL (stage L P hL C n).model
    haveI : Finite (Extensions P (stageModel L P hL C n)) := by
      change Finite (Extensions P (stage L P hL C n).model)
      infer_instance
    haveI : Nonempty (Extensions P (stageModel L P hL C n)) :=
      ⟨⟨OnePointExtension.default (fun _ => C.injective _ (stage L P hL C n).legal),
        C.isolated _ (stage L P hL C n).legal⟩⟩
    have hp : 0 < Nat.card (Extensions P (stageModel L P hL C n)) := Nat.card_pos
    have hc : Nat.card (StageDomain L P hL C (n + 1)) =
        Nat.card (StageDomain L P hL C n) + Nat.card (Extensions P (stageModel L P hL C n)) :=
      Nat.card_sum
    rw [hc]
    omega

theorem infinite_limit : Infinite (Limit L P hL C) := by
  apply not_finite_iff_infinite.mp
  intro hf
  letI := hf
  have he := Nat.card_le_card_of_injective
    (ofStage L P hL C (Nat.card (Limit L P hL C) + 1))
    (ofStage L P hL C (Nat.card (Limit L P hL C) + 1)).injective
  have hl := card_stage_lower L P hL C (Nat.card (Limit L P hL C) + 1)
  omega

end CombinedRamsey.Negative.ConstrainedGeneric
