import Mathlib.ModelTheory.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Pi

/-!
Exact relational semantics for Problem 6.3.2.  Tuples are functions `Fin r → X`;
repeated entries are permitted unless `InjectiveRelations` is imposed.  Arity
zero is retained here, so the existence obstructions do not disappear by
definition.  The Ramsey applications impose positive arity separately.

The last section gives a definitional bridge to Mathlib first-order structures.
-/

namespace RelationalRamsey632

structure Language where
  Rel : ℕ → Type

structure RelStructure (L : Language) (X : Type) where
  rel : {r : ℕ} → L.Rel r → (Fin r → X) → Prop

namespace RelStructure

variable {L : Language} {X Y W : Type}

theorem ext_rel {A B : RelStructure L X}
    (h : ∀ (r : ℕ) (R : L.Rel r) (t : Fin r → X), A.rel R t ↔ B.rel R t) :
    A = B := by
  cases A with
  | mk a =>
    cases B with
    | mk b =>
      congr
      funext r R t
      exact propext (h r R t)

def pullback (B : RelStructure L Y) (f : X → Y) : RelStructure L X where
  rel R t := B.rel R (f ∘ t)

@[simp] theorem pullback_rel (B : RelStructure L Y) (f : X → Y)
    {r : ℕ} (R : L.Rel r) (t : Fin r → X) :
    (B.pullback f).rel R t = B.rel R (f ∘ t) := rfl

@[simp] theorem pullback_id (B : RelStructure L X) : B.pullback id = B := rfl

@[simp] theorem pullback_comp (B : RelStructure L W) (g : Y → W) (f : X → Y) :
    (B.pullback g).pullback f = B.pullback (g ∘ f) := rfl

def InjectiveRelations (A : RelStructure L X) : Prop :=
  ∀ (r : ℕ) (R : L.Rel r) (t : Fin r → X),
    0 < r → A.rel R t → Function.Injective t

theorem injectiveRelations_pullback {B : RelStructure L Y}
    (hB : B.InjectiveRelations) (f : X → Y) :
    (B.pullback f).InjectiveRelations := by
  intro r R t hr ht i j hij
  exact hB r R (f ∘ t) hr ht (congrArg f hij)

end RelStructure

structure RelEmbedding {L : Language} {X Y : Type}
    (A : RelStructure L X) (B : RelStructure L Y) where
  toFun : X → Y
  injective : Function.Injective toFun
  map_rel : ∀ {r : ℕ} (R : L.Rel r) (t : Fin r → X),
    A.rel R t ↔ B.rel R (toFun ∘ t)

namespace RelEmbedding

variable {L : Language} {X Y W : Type}
variable {A : RelStructure L X} {B : RelStructure L Y} {C : RelStructure L W}

instance : CoeFun (RelEmbedding A B) (fun _ => X → Y) := ⟨toFun⟩

@[ext] theorem ext {f g : RelEmbedding A B} (h : ∀ x, f x = g x) : f = g := by
  cases f
  cases g
  congr
  exact funext h

def refl (A : RelStructure L X) : RelEmbedding A A where
  toFun := id
  injective := Function.injective_id
  map_rel _ _ := Iff.rfl

def comp (g : RelEmbedding B C) (f : RelEmbedding A B) : RelEmbedding A C where
  toFun := g ∘ f
  injective := g.injective.comp f.injective
  map_rel R t := (f.map_rel R t).trans (g.map_rel R (f ∘ t))

@[simp] theorem refl_apply (A : RelStructure L X) (x : X) : refl A x = x := rfl
@[simp] theorem comp_apply (g : RelEmbedding B C) (f : RelEmbedding A B) (x : X) :
    g.comp f x = g (f x) := rfl

@[simp] theorem comp_refl (f : RelEmbedding A B) : f.comp (refl A) = f := by
  ext x
  rfl

@[simp] theorem refl_comp (f : RelEmbedding A B) : (refl B).comp f = f := by
  ext x
  rfl

theorem comp_assoc {V : Type} {D : RelStructure L V}
    (h : RelEmbedding C D) (g : RelEmbedding B C) (f : RelEmbedding A B) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext x
  rfl

theorem pullback_eq (f : RelEmbedding A B) : B.pullback f = A := by
  apply RelStructure.ext_rel
  intro r R t
  exact (f.map_rel R t).symm

def pullback (B : RelStructure L Y) (f : X → Y) (hf : Function.Injective f) :
    RelEmbedding (B.pullback f) B where
  toFun := f
  injective := hf
  map_rel _ _ := Iff.rfl

end RelEmbedding

structure LanguageInclusion (L S : Language) where
  relMap : (r : ℕ) → L.Rel r → S.Rel r
  relInjective : ∀ r, Function.Injective (relMap r)

namespace RelStructure

variable {L S : Language} {X Y : Type}

def reduct (i : LanguageInclusion L S) (Z : RelStructure S X) : RelStructure L X where
  rel {r} R t := Z.rel (i.relMap r R) t

@[simp] theorem reduct_pullback (i : LanguageInclusion L S)
    (Z : RelStructure S Y) (f : X → Y) :
    (Z.pullback f).reduct i = (Z.reduct i).pullback f := rfl

def IsExpansion (i : LanguageInclusion L S) (K : RelStructure L X)
    (Z : RelStructure S X) : Prop := Z.reduct i = K

def palette (A : RelStructure L X) (K : RelStructure L Y) (Z : RelStructure S Y) :
    Set (RelStructure S X) := Set.range (fun e : RelEmbedding A K => Z.pullback e)

theorem mem_palette_iff (A : RelStructure L X) (K : RelStructure L Y)
    (Z : RelStructure S Y) (p : RelStructure S X) :
    p ∈ palette A K Z ↔ ∃ e : RelEmbedding A K, Z.pullback e = p := Iff.rfl

theorem palette_pullback_subset (A : RelStructure L X) (K : RelStructure L Y)
    (Z : RelStructure S Y) (f : RelEmbedding K K) :
    palette A K (Z.pullback f) ⊆ palette A K Z := by
  rintro p ⟨e, rfl⟩
  exact ⟨f.comp e, rfl⟩

end RelStructure

namespace RelEmbedding

variable {L S : Language} {X Y : Type}
variable {A : RelStructure S X} {B : RelStructure S Y}

def reduct (f : RelEmbedding A B) (i : LanguageInclusion L S) :
    RelEmbedding (A.reduct i) (B.reduct i) where
  toFun := f
  injective := f.injective
  map_rel R t := f.map_rel (i.relMap _ R) t

end RelEmbedding

namespace Language

def toFirstOrder (L : Language) : FirstOrder.Language where
  Functions _ := Empty
  Relations := L.Rel

instance (L : Language) : L.toFirstOrder.IsRelational := by
  intro n
  change IsEmpty Empty
  infer_instance

def Positive (L : Language) : Prop := IsEmpty (L.Rel 0)
def FinitePerArity (L : Language) : Prop := ∀ r, Finite (L.Rel r)

end Language

namespace RelStructure

variable {L : Language} {X : Type}

@[reducible] def toFirstOrder (A : RelStructure L X) : L.toFirstOrder.Structure X where
  funMap f := Empty.elim f
  RelMap := A.rel

def ofFirstOrder (A : L.toFirstOrder.Structure X) : RelStructure L X where
  rel := A.RelMap

@[simp] theorem of_toFirstOrder (A : RelStructure L X) :
    ofFirstOrder A.toFirstOrder = A := rfl

@[simp] theorem to_ofFirstOrder (A : L.toFirstOrder.Structure X) :
    (ofFirstOrder A).toFirstOrder = A := by
  cases A with
  | mk f r =>
    apply FirstOrder.Language.Structure.ext
    · funext n x
      exact Empty.elim x
    · rfl

end RelStructure

namespace RelEmbedding

variable {L : Language} {X Y : Type}
variable {A : RelStructure L X} {B : RelStructure L Y}

def toFirstOrder (f : RelEmbedding A B) :
    @FirstOrder.Language.Embedding L.toFirstOrder X Y A.toFirstOrder B.toFirstOrder := by
  letI := A.toFirstOrder
  letI := B.toFirstOrder
  exact {
    toFun := f
    inj' := f.injective
    map_fun' := fun F => Empty.elim F
    map_rel' := fun R t => (f.map_rel R t).symm }

def ofFirstOrder
    (f : @FirstOrder.Language.Embedding L.toFirstOrder X Y A.toFirstOrder B.toFirstOrder) :
    RelEmbedding A B := by
  letI := A.toFirstOrder
  letI := B.toFirstOrder
  exact {
    toFun := f
    injective := f.injective
    map_rel := fun R t => (f.map_rel' R t).symm }

@[simp] theorem of_toFirstOrder (f : RelEmbedding A B) :
    ofFirstOrder f.toFirstOrder = f := by
  ext x
  rfl

end RelEmbedding

end RelationalRamsey632
