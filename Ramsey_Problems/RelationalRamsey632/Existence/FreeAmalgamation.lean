import RelationalRamsey632.Existence.OnePointStage
import RelationalRamsey632.Existence.SingletonTypes
import Mathlib.Logic.Equiv.Set

/-! Free amalgamation with induced embeddings, including nullary relations. -/

namespace RelationalRamsey632.Existence
namespace SharedBaseAmalgam

variable {L : Language} {X Y Z : Type}

abbrev Domain := X ⊕ (Y ⊕ Z)

def left : X ⊕ Y → Domain (X := X) (Y := Y) (Z := Z) :=
  Sum.map id Sum.inl

def right : X ⊕ Z → Domain (X := X) (Y := Y) (Z := Z) :=
  Sum.map id Sum.inr

theorem left_injective : Function.Injective (left (X := X) (Y := Y) (Z := Z)) :=
  Sum.map_injective.mpr ⟨Function.injective_id, Sum.inl_injective⟩

theorem right_injective : Function.Injective (right (X := X) (Y := Y) (Z := Z)) :=
  Sum.map_injective.mpr ⟨Function.injective_id, Sum.inr_injective⟩

theorem common_tuple {r : ℕ} (u : Fin r → X ⊕ Y) (v : Fin r → X ⊕ Z)
    (h : left ∘ u = right ∘ v) :
    ∃ w : Fin r → X, u = Sum.inl ∘ w ∧ v = Sum.inl ∘ w := by
  classical
  have hw : ∀ i, ∃ x : X, u i = Sum.inl x ∧ v i = Sum.inl x := by
    intro i
    have hi := congrFun h i
    cases hu : u i with
    | inl x =>
      cases hv : v i with
      | inl y =>
        have hxy : x = y := by simpa [left, right, hu, hv] using hi
        subst y
        exact ⟨x, rfl, rfl⟩
      | inr y => simp [left, right, hu, hv] at hi
    | inr y =>
      cases hv : v i <;> simp [left, right, hu, hv] at hi
  choose w hu hv using hw
  exact ⟨w, funext hu, funext hv⟩

variable (B : RelStructure L (X ⊕ Y)) (C : RelStructure L (X ⊕ Z))

def model : RelStructure L (Domain (X := X) (Y := Y) (Z := Z)) where
  rel R t := (∃ u, left ∘ u = t ∧ B.rel R u) ∨
    ∃ v, right ∘ v = t ∧ C.rel R v

theorem model_admissible {inj : Bool} (hB : Admissible inj B) (hC : Admissible inj C) :
    Admissible inj (model B C) := by
  intro hi r R t hr ht i j hij
  rcases ht with ⟨u, hu, hR⟩ | ⟨v, hv, hR⟩
  · apply hB hi r R u hr hR
    apply left_injective
    exact (congrFun hu i).trans (hij.trans (congrFun hu j).symm)
  · apply hC hi r R v hr hR
    apply right_injective
    exact (congrFun hv i).trans (hij.trans (congrFun hv j).symm)

variable (hBC : B.pullback Sum.inl = C.pullback Sum.inl)

def leftEmbedding : RelEmbedding B (model B C) where
  toFun := left
  injective := left_injective
  map_rel R t := by
    constructor
    · intro hR
      exact Or.inl ⟨t, rfl, hR⟩
    · rintro (⟨u, hu, hR⟩ | ⟨v, hv, hR⟩)
      · have hut : u = t := funext (fun i => left_injective (congrFun hu i))
        exact hut ▸ hR
      · obtain ⟨w, htw, hvw⟩ := common_tuple t v hv.symm
        have he := congrArg (fun S : RelStructure L X => S.rel R w) hBC
        rw [hvw] at hR
        have hB : B.rel R (Sum.inl ∘ w) := (Iff.of_eq he).mpr hR
        exact htw.symm ▸ hB

def rightEmbedding : RelEmbedding C (model B C) where
  toFun := right
  injective := right_injective
  map_rel R t := by
    constructor
    · intro hR
      exact Or.inr ⟨t, rfl, hR⟩
    · rintro (⟨u, hu, hR⟩ | ⟨v, hv, hR⟩)
      · obtain ⟨w, huw, htw⟩ := common_tuple u t hu
        have he := congrArg (fun S : RelStructure L X => S.rel R w) hBC
        rw [huw] at hR
        have hC : C.rel R (Sum.inl ∘ w) := (Iff.of_eq he).mp hR
        exact htw.symm ▸ hC
      · have hvt : v = t := funext (fun i => right_injective (congrFun hv i))
        exact hvt ▸ hR

theorem free {r : ℕ} (R : L.Rel r) (t : Fin r → Domain (X := X) (Y := Y) (Z := Z))
    (hR : (model B C).rel R t) :
    (∀ i, t i ∈ Set.range (leftEmbedding B C hBC)) ∨
      (∀ i, t i ∈ Set.range (rightEmbedding B C hBC)) := by
  rcases hR with ⟨u, hu, _⟩ | ⟨v, hv, _⟩
  · exact Or.inl (fun i => ⟨u i, congrFun hu i⟩)
  · exact Or.inr (fun i => ⟨v i, congrFun hv i⟩)

end SharedBaseAmalgam

namespace FreeAmalgamation

variable {L : Language} {X Y Z : Type}
variable {A : RelStructure L X} {B : RelStructure L Y} {C : RelStructure L Z}

abbrev Complement (f : RelEmbedding A B) := {y : Y // y ∉ Set.range f}

noncomputable def split (f : RelEmbedding A B) : X ⊕ Complement f ≃ Y := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective f f.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range f))

@[simp] theorem split_old (f : RelEmbedding A B) (x : X) : split f (Sum.inl x) = f x := rfl

noncomputable def splitModel (f : RelEmbedding A B) : RelStructure L (X ⊕ Complement f) :=
  B.pullback (split f)

noncomputable def splitEmbedding (f : RelEmbedding A B) : RelEmbedding B (splitModel f) where
  toFun := (split f).symm
  injective := (split f).symm.injective
  map_rel R t := by
    change B.rel R t ↔ B.rel R (split f ∘ ((split f).symm ∘ t))
    simp [Function.comp_def]

theorem split_old_eq (f : RelEmbedding A B) : (splitModel f).pullback Sum.inl = A := by
  have hf : split f ∘ Sum.inl = f := funext (split_old f)
  rw [splitModel, RelStructure.pullback_comp, hf]
  exact f.pullback_eq

variable (f : RelEmbedding A B) (g : RelEmbedding A C)

abbrev Domain := X ⊕ (Complement f ⊕ Complement g)

noncomputable def model : RelStructure L (Domain f g) :=
  SharedBaseAmalgam.model (splitModel f) (splitModel g)

theorem base_eq : (splitModel f).pullback Sum.inl = (splitModel g).pullback Sum.inl :=
  (split_old_eq f).trans (split_old_eq g).symm

noncomputable def leftEmbedding : RelEmbedding B (model f g) :=
  (SharedBaseAmalgam.leftEmbedding (splitModel f) (splitModel g) (base_eq f g)).comp
    (splitEmbedding f)

noncomputable def rightEmbedding : RelEmbedding C (model f g) :=
  (SharedBaseAmalgam.rightEmbedding (splitModel f) (splitModel g) (base_eq f g)).comp
    (splitEmbedding g)

theorem left_old (x : X) : leftEmbedding f g (f x) = Sum.inl x := by
  have hf : (split f).symm (f x) = Sum.inl x := by
    apply (split f).injective
    simp
  change SharedBaseAmalgam.left ((split f).symm (f x)) = Sum.inl x
  rw [hf]
  rfl

theorem right_old (x : X) : rightEmbedding f g (g x) = Sum.inl x := by
  have hg : (split g).symm (g x) = Sum.inl x := by
    apply (split g).injective
    simp
  change SharedBaseAmalgam.right ((split g).symm (g x)) = Sum.inl x
  rw [hg]
  rfl

theorem square : (leftEmbedding f g).comp f = (rightEmbedding f g).comp g := by
  ext x
  exact (left_old f g x).trans (right_old f g x).symm

theorem common_vertex (y : Y) (z : Z) (h : leftEmbedding f g y = rightEmbedding f g z) :
    ∃ x : X, f x = y ∧ g x = z := by
  change SharedBaseAmalgam.left ((split f).symm y) =
    SharedBaseAmalgam.right ((split g).symm z) at h
  cases hu : (split f).symm y with
  | inl x =>
    cases hv : (split g).symm z with
    | inl w =>
      have hxw : x = w := by simpa [SharedBaseAmalgam.left, SharedBaseAmalgam.right, hu, hv] using h
      subst w
      refine ⟨x, ?_, ?_⟩
      · have hy := (split f).apply_symm_apply y
        rw [hu, split_old] at hy
        exact hy
      · have hz := (split g).apply_symm_apply z
        rw [hv, split_old] at hz
        exact hz
    | inr w => simp [SharedBaseAmalgam.left, SharedBaseAmalgam.right, hu, hv] at h
  | inr w =>
    cases hv : (split g).symm z <;>
      simp [SharedBaseAmalgam.left, SharedBaseAmalgam.right, hu, hv] at h

theorem model_admissible {inj : Bool} (hB : Admissible inj B) (hC : Admissible inj C) :
    Admissible inj (model f g) :=
  SharedBaseAmalgam.model_admissible (splitModel f) (splitModel g)
    (fun hi => B.injectiveRelations_pullback (hB hi) (split f))
    (fun hi => C.injectiveRelations_pullback (hC hi) (split g))

theorem finite_domain [Finite X] [Finite Y] [Finite Z] : Finite (Domain f g) := by
  infer_instance

theorem free {r : ℕ} (R : L.Rel r) (t : Fin r → Domain f g) (hR : (model f g).rel R t) :
    (∀ i, t i ∈ Set.range (leftEmbedding f g)) ∨
      (∀ i, t i ∈ Set.range (rightEmbedding f g)) := by
  rcases SharedBaseAmalgam.free (splitModel f) (splitModel g) (base_eq f g) R t hR
    with hl | hr
  · left
    intro i
    obtain ⟨u, hu⟩ := hl i
    refine ⟨split f u, ?_⟩
    change SharedBaseAmalgam.left ((split f).symm (split f u)) = t i
    simpa [SharedBaseAmalgam.leftEmbedding] using hu
  · right
    intro i
    obtain ⟨u, hu⟩ := hr i
    refine ⟨split g u, ?_⟩
    change SharedBaseAmalgam.right ((split g).symm (split g u)) = t i
    simpa [SharedBaseAmalgam.rightEmbedding] using hu

end FreeAmalgamation

variable {L : Language} {X Y : Type}

def emptyFixedEmbedding (θ : L.Rel 0 → Prop) (B : RelStructure L X)
    (hθ : FixedNullary L θ B) : RelEmbedding (nullaryOnly L θ Empty) B where
  toFun := Empty.elim
  injective := fun x => Empty.elim x
  map_rel := by
    intro r R t
    cases r with
    | zero =>
      simp only [nullaryOnly, dite_true]
      exact (hθ R (Empty.elim ∘ t)).symm
    | succ r => exact Empty.elim (t 0)

theorem joint_embedding_fixednullary {inj : Bool} [Finite X] [Finite Y]
    (θ : L.Rel 0 → Prop) (B : RelStructure L X) (C : RelStructure L Y)
    (hB : Admissible inj B) (hC : Admissible inj C)
    (hθB : FixedNullary L θ B) (hθC : FixedNullary L θ C) :
    ∃ (V : Type) (D : RelStructure L V), Finite V ∧ Admissible inj D ∧ FixedNullary L θ D ∧
      Nonempty (RelEmbedding B D) ∧ Nonempty (RelEmbedding C D) := by
  let f := emptyFixedEmbedding θ B hθB
  let g := emptyFixedEmbedding θ C hθC
  let D := FreeAmalgamation.model f g
  let i := FreeAmalgamation.leftEmbedding f g
  let j := FreeAmalgamation.rightEmbedding f g
  refine ⟨FreeAmalgamation.Domain f g, D, FreeAmalgamation.finite_domain f g,
    FreeAmalgamation.model_admissible f g hB hC, ?_, ⟨i⟩, ⟨j⟩⟩
  intro R t
  have ht : i ∘ (Fin.elim0 : Fin 0 → X) = t := by
    funext q
    exact q.elim0
  have hi := i.map_rel R Fin.elim0
  rw [ht] at hi
  exact hi.symm.trans (hθB R Fin.elim0)

end RelationalRamsey632.Existence
