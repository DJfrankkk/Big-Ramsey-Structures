import RelationalRamsey632.Model
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.EquivFin

/-!
The actual source Ramsey and weak-map arguments of Sections 5--7.
All occurrences are embeddings of interpreted relational structures, and
every palette is a set of complete relation tables pulled back along them.
-/

namespace RelationalRamsey632.Transfer

open RelStructure

variable {L S : Language} {X M : Type}

/-- Preservation and reflection together with injectivity for a specified map. -/
def IsEmbeddingMap {A B : Type} (K : RelStructure L A) (N : RelStructure L B)
    (f : A → B) : Prop :=
  Function.Injective f ∧
    ∀ (r : ℕ) (R : L.Rel r) (t : Fin r → A), K.rel R t ↔ N.rel R (f ∘ t)

def embeddingOfMap {A B : Type} {K : RelStructure L A} {N : RelStructure L B}
    (f : A → B) (h : IsEmbeddingMap K N f) : RelEmbedding K N where
  toFun := f
  injective := h.1
  map_rel R t := h.2 _ R t

/-- The paper's approximate map, quantified over all finite structures in the age. -/
def Approximate (K : RelStructure L X) (N : RelStructure L M) (ψ : M → X) : Prop :=
  ∀ (A : Type) [Finite A] (a : RelStructure L A),
    Nonempty (RelEmbedding a K) → ∀ u : RelEmbedding a N,
      IsEmbeddingMap a K (ψ ∘ u)

def approximateEmbedding {A : Type} [Finite A] {a : RelStructure L A}
    {K : RelStructure L X} {N : RelStructure L M} {ψ : M → X}
    (hψ : Approximate K N ψ) (ha : Nonempty (RelEmbedding a K))
    (u : RelEmbedding a N) : RelEmbedding a K :=
  embeddingOfMap _ (hψ A a ha u)

@[simp] theorem approximateEmbedding_apply {A : Type} [Finite A]
    {a : RelStructure L A} {K : RelStructure L X} {N : RelStructure L M}
    {ψ : M → X} (hψ : Approximate K N ψ)
    (ha : Nonempty (RelEmbedding a K)) (u : RelEmbedding a N) (x : A) :
    approximateEmbedding hψ ha u x = ψ (u x) := rfl

/-- Every relation is checked on its finite tuple support, and injectivity
is checked on a finite two-point support. No restriction on the language size. -/
theorem approximate_comp_embedding {K : RelStructure L X} {N : RelStructure L M}
    {ψ : M → X} (hψ : Approximate K N ψ) (i : RelEmbedding K N) :
    IsEmbeddingMap K K (ψ ∘ i) := by
  classical
  constructor
  · intro x y hxy
    let F : Set X := {x, y}
    have hF : F.Finite := (Set.finite_singleton y).insert x
    letI : Finite F := hF.to_subtype
    let a : RelStructure L F := K.pullback Subtype.val
    let e : RelEmbedding a K := RelEmbedding.pullback K Subtype.val Subtype.val_injective
    let u : RelEmbedding a N := i.comp e
    have hinj := (hψ F a ⟨e⟩ u).1
    have hx : x ∈ F := by simp [F]
    have hy : y ∈ F := by simp [F]
    have hs : (⟨x, hx⟩ : F) = ⟨y, hy⟩ := hinj hxy
    exact congrArg Subtype.val hs
  · intro r R t
    let F : Set X := Set.range t
    have hF : F.Finite := by
      simpa [F] using (Set.finite_univ : (Set.univ : Set (Fin r)).Finite).image t
    letI : Finite F := hF.to_subtype
    let a : RelStructure L F := K.pullback Subtype.val
    let e : RelEmbedding a K := RelEmbedding.pullback K Subtype.val Subtype.val_injective
    let u : RelEmbedding a N := i.comp e
    let s : Fin r → F := fun j => ⟨t j, ⟨j, rfl⟩⟩
    exact (hψ F a ⟨e⟩ u).2 r R s

def approximateComp {K : RelStructure L X} {N : RelStructure L M}
    {ψ : M → X} (hψ : Approximate K N ψ) (i : RelEmbedding K N) :
    RelEmbedding K K := embeddingOfMap _ (approximate_comp_embedding hψ i)

@[simp] theorem approximateComp_apply {K : RelStructure L X} {N : RelStructure L M}
    {ψ : M → X} (hψ : Approximate K N ψ) (i : RelEmbedding K N) (x : X) :
    approximateComp hψ i x = ψ (i x) := rfl

theorem approximate_postcompose {K : RelStructure L X} {N : RelStructure L M}
    {ψ : M → X} (hψ : Approximate K N ψ) (f : RelEmbedding K K) :
    Approximate K N (f ∘ ψ) := by
  intro A _ a ha u
  have hu := hψ A a ha u
  exact ⟨f.injective.comp hu.1,
    fun r R t => (hu.2 r R t).trans (f.map_rel R ((ψ ∘ u) ∘ t))⟩

theorem approximate_precompose {K : RelStructure L X} {N : RelStructure L M}
    {ψ : M → X} (hψ : Approximate K N ψ) (f : RelEmbedding N N) :
    Approximate K N (ψ ∘ f) := by
  intro A _ a ha u
  exact hψ A a ha (f.comp u)

/-- Embedding degree one, with arbitrary finite color sets. -/
def SourceDegreeOne {A : Type} (N : RelStructure S M) (p : RelStructure S A) : Prop :=
  ∀ (D : Type) [Fintype D] (c : RelEmbedding p N → D),
    ∃ ζ : RelEmbedding N N, ∀ u v : RelEmbedding p N,
      c (ζ.comp u) = c (ζ.comp v)

/-- One source self-embedding simultaneously homogenizes any finite list
of actual expanded domains. Earlier homogenizations survive composition. -/
theorem simultaneous_source {I : Type} [Fintype I]
    {A : I → Type} (N : RelStructure S M) (p : ∀ j, RelStructure S (A j))
    (hR : ∀ j, SourceDegreeOne N (p j))
    {D : I → Type} [∀ j, Fintype (D j)]
    (c : ∀ j, RelEmbedding (p j) N → D j) :
    ∃ ζ : RelEmbedding N N, ∀ j u v,
      c j (ζ.comp u) = c j (ζ.comp v) := by
  classical
  have h : ∀ s : Finset I, ∃ ζ : RelEmbedding N N,
      ∀ j ∈ s, ∀ u v, c j (ζ.comp u) = c j (ζ.comp v) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨RelEmbedding.refl N, by simp⟩
    | @insert j s _ ih =>
      obtain ⟨ζ, hζ⟩ := ih
      obtain ⟨w, hw⟩ := hR j (D j) (fun u => c j (ζ.comp u))
      refine ⟨ζ.comp w, ?_⟩
      intro k hk u v
      rcases Finset.mem_insert.mp hk with rfl | hks
      · exact hw u v
      · exact hζ k hks (w.comp u) (w.comp v)
  obtain ⟨ζ, hζ⟩ := h Finset.univ
  exact ⟨ζ, fun j => hζ j (Finset.mem_univ j)⟩

end RelationalRamsey632.Transfer
