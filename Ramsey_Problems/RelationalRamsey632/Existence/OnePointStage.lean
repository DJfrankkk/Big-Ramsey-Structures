import RelationalRamsey632.Existence.FiniteTypes
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finite.Sum

/-!
Actual finite-stage construction: simultaneously realize all admissible
one-point extensions, with no new relation crossing two distinct new vertices.
The Boolean convention parameter covers ordinary and injective relations.
-/

namespace RelationalRamsey632
namespace Existence

variable {L : Language} {X : Type}

def Admissible (inj : Bool) (A : RelStructure L X) : Prop :=
  inj = true → A.InjectiveRelations

abbrev ClassStructure (L : Language) (inj : Bool) (X : Type) :=
  {A : RelStructure L X // Admissible inj A}

def LocallyFiniteLanguage (L : Language) (inj : Bool) : Prop :=
  if inj then L.FinitePerArity else Finite (Sigma L.Rel)

theorem finite_class_structures (L : Language) (inj : Bool)
    (hL : LocallyFiniteLanguage L inj) (X : Type) [Finite X] :
    Finite (ClassStructure L inj X) := by
  cases inj with
  | false =>
    classical
    haveI : Finite (Sigma L.Rel) := hL
    letI := Fintype.ofFinite X
    let e : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
    let f : ClassStructure L false X → RelStructure L (Fin (Fintype.card X)) :=
      fun A => A.val.pullback e.symm
    letI := finite_ordinary_structures L (Fintype.card X)
    apply Finite.of_injective f
    intro A B h
    apply Subtype.ext
    apply RelStructure.ext_rel
    intro r R t
    have ht := congrArg (fun S : RelStructure L (Fin (Fintype.card X)) => S.rel R (e ∘ t)) h
    simpa [f, RelStructure.pullback, Function.comp_def] using ht
  | true =>
    haveI := finite_injective_structures_on_finite L hL X
    exact Finite.of_injective
      (fun A : ClassStructure L true X =>
        (⟨A.val, A.property rfl⟩ : InjectiveStructure L X))
      (fun A B h => by
        apply Subtype.ext
        exact congrArg (fun Z : InjectiveStructure L X => Z.val) h)

structure OnePointExtension (inj : Bool) (A : RelStructure L X) where
  model : RelStructure L (X ⊕ Unit)
  old_eq : model.pullback Sum.inl = A
  admissible : Admissible inj model

namespace OnePointExtension

variable {inj : Bool} {A : RelStructure L X}

@[ext] theorem ext {B C : OnePointExtension inj A}
    (h : B.model = C.model) : B = C := by
  cases B
  cases C
  congr

theorem finite (hL : LocallyFiniteLanguage L inj) [Finite X] :
    Finite (OnePointExtension inj A) := by
  haveI := finite_class_structures L inj hL (X ⊕ Unit)
  exact Finite.of_injective
    (fun B : OnePointExtension inj A =>
      (⟨B.model, B.admissible⟩ : ClassStructure L inj (X ⊕ Unit)))
    (fun B C h => ext (congrArg Subtype.val h))

def isolated (A : RelStructure L X) : RelStructure L (X ⊕ Unit) where
  rel R t := ∃ u : Fin _ → X, Sum.inl ∘ u = t ∧ A.rel R u

theorem isolated_old_eq (A : RelStructure L X) :
    (isolated A).pullback Sum.inl = A := by
  apply RelStructure.ext_rel
  intro r R t
  constructor
  · rintro ⟨u, hu, hR⟩
    have htu : u = t := funext (fun i => Sum.inl_injective (congrFun hu i))
    exact htu ▸ hR
  · intro hR
    exact ⟨t, rfl, hR⟩

theorem isolated_admissible (hA : Admissible inj A) : Admissible inj (isolated A) := by
  intro hi r R t hr ht i j hij
  obtain ⟨u, hu, hR⟩ := ht
  apply hA hi r R u hr hR
  apply Sum.inl_injective
  exact (congrFun hu i).trans (hij.trans (congrFun hu j).symm)

def default (hA : Admissible inj A) : OnePointExtension inj A where
  model := isolated A
  old_eq := isolated_old_eq A
  admissible := isolated_admissible hA

def inclusion (B : OnePointExtension inj A) : RelEmbedding A B.model where
  toFun := Sum.inl
  injective := Sum.inl_injective
  map_rel R t := by
    have h := congrArg (fun Z : RelStructure L X => Z.rel R t) B.old_eq
    exact (Iff.of_eq h).symm

end OnePointExtension

namespace OnePointStage

variable {inj : Bool} (A : RelStructure L X)

abbrev Domain := X ⊕ OnePointExtension inj A

def place (B : OnePointExtension inj A) : X ⊕ Unit → Domain (inj := inj) A :=
  Sum.elim Sum.inl (fun _ => Sum.inr B)

theorem place_injective (B : OnePointExtension inj A) : Function.Injective (place A B) := by
  intro x y h
  cases x <;> cases y <;> simp_all [place]

def model : RelStructure L (Domain (inj := inj) A) where
  rel R t := ∃ B : OnePointExtension inj A, ∃ u : Fin _ → X ⊕ Unit,
    place A B ∘ u = t ∧ B.model.rel R u

theorem structure_admissible : Admissible inj (model (inj := inj) A) := by
  intro hi r R t hr ht i j hij
  obtain ⟨B, u, hu, hR⟩ := ht
  apply B.admissible hi r R u hr hR
  apply place_injective A B
  exact (congrFun hu i).trans (hij.trans (congrFun hu j).symm)

theorem place_reflects (B : OnePointExtension inj A) {r : ℕ} (R : L.Rel r)
    (t : Fin r → X ⊕ Unit) :
    (model (inj := inj) A).rel R (place A B ∘ t) → B.model.rel R t := by
  classical
  rintro ⟨C, u, htu, hR⟩
  by_cases hBC : B = C
  · subst C
    have hut : u = t := funext (fun i => place_injective A B (congrFun htu i))
    exact hut ▸ hR
  · have hold : ∀ i, ∃ x : X, t i = Sum.inl x := by
      intro i
      have hv := congrFun htu i
      cases ht : t i with
      | inl x => exact ⟨x, rfl⟩
      | inr v =>
        cases hu : u i with
        | inl x => simp [place, ht, hu] at hv
        | inr w =>
          have hCB : C = B := by simpa [place, ht, hu] using hv
          exact False.elim (hBC hCB.symm)
    choose v hv using hold
    have hvt : Sum.inl ∘ v = t := funext (fun i => (hv i).symm)
    have hvu : Sum.inl ∘ v = u := by
      funext i
      apply place_injective A C
      have h := congrFun htu i
      simpa [place, hv i] using h.symm
    have hA : A.rel R v := by
      rw [← hvu] at hR
      exact (C.inclusion.map_rel R v).mpr hR
    rw [← hvt]
    exact (B.inclusion.map_rel R v).mp hA

def extensionEmbedding (B : OnePointExtension inj A) :
    RelEmbedding B.model (model (inj := inj) A) where
  toFun := place A B
  injective := place_injective A B
  map_rel R t := ⟨fun hR => ⟨B, t, rfl, hR⟩, place_reflects A B R t⟩

def oldEmbedding (hA : Admissible inj A) : RelEmbedding A (model (inj := inj) A) :=
  (extensionEmbedding A (OnePointExtension.default hA)).comp
    (OnePointExtension.default hA).inclusion

@[simp] theorem oldEmbedding_apply (hA : Admissible inj A) (x : X) :
    oldEmbedding A hA x = Sum.inl x := rfl

@[simp] theorem extensionEmbedding_old (B : OnePointExtension inj A) (x : X) :
    extensionEmbedding A B (Sum.inl x) = Sum.inl x := rfl

@[simp] theorem extensionEmbedding_new (B : OnePointExtension inj A) :
    extensionEmbedding A B (Sum.inr ()) = Sum.inr B := rfl

theorem finite_domain (hL : LocallyFiniteLanguage L inj) [Finite X] :
    Finite (Domain (inj := inj) A) := by
  haveI := OnePointExtension.finite (A := A) hL
  infer_instance

end OnePointStage
end Existence
end RelationalRamsey632


