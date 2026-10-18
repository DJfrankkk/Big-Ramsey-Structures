import RelationalRamsey632.Existence.OnePointStage
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.Encodable.Basic
import Lean.Elab.Tactic.Omega

namespace RelationalRamsey632.Existence

variable {L : Language} {X : Type}

def OnePointExtensionProperty (inj : Bool) (K : RelStructure L X) : Prop :=
  ∀ n (B : RelStructure L (Fin (n + 1))), Admissible inj B →
    ∀ f : RelEmbedding (B.pullback Fin.castSucc) K,
      ∃ g : RelEmbedding B K, ∀ i : Fin n, g i.castSucc = f i

def initialSegment (B : RelStructure L Nat) (n : Nat) : RelStructure L (Fin n) :=
  B.pullback Fin.val

theorem initialSegment_admissible {inj : Bool} (B : RelStructure L Nat)
    (hB : Admissible inj B) (n : Nat) : Admissible inj (initialSegment B n) := by
  intro hi
  exact RelStructure.injectiveRelations_pullback (hB hi) Fin.val

@[simp] theorem initialSegment_castSucc (B : RelStructure L Nat) (n : Nat) :
    (initialSegment B (n + 1)).pullback Fin.castSucc = initialSegment B n := rfl

noncomputable def embeddingStages {inj : Bool} (K : RelStructure L X)
    (hK : OnePointExtensionProperty inj K) (B : RelStructure L Nat)
    (hB : Admissible inj B) (e0 : RelEmbedding (initialSegment B 0) K) :
    (n : Nat) → RelEmbedding (initialSegment B n) K
  | 0 => e0
  | n + 1 => Classical.choose (hK n (initialSegment B (n + 1))
      (initialSegment_admissible B hB (n + 1))
      (embeddingStages K hK B hB e0 n))

theorem embeddingStages_successor {inj : Bool} (K : RelStructure L X)
    (hK : OnePointExtensionProperty inj K) (B : RelStructure L Nat)
    (hB : Admissible inj B) (e0 : RelEmbedding (initialSegment B 0) K)
    (n : Nat) (i : Fin n) :
    embeddingStages K hK B hB e0 (n + 1) i.castSucc = embeddingStages K hK B hB e0 n i :=
  Classical.choose_spec (hK n (initialSegment B (n + 1))
    (initialSegment_admissible B hB (n + 1)) (embeddingStages K hK B hB e0 n)) i

theorem embeddingStages_coherent {inj : Bool} (K : RelStructure L X)
    (hK : OnePointExtensionProperty inj K) (B : RelStructure L Nat)
    (hB : Admissible inj B) (e0 : RelEmbedding (initialSegment B 0) K)
    {i n m : Nat} (hin : i < n) (hnm : n ≤ m) :
    embeddingStages K hK B hB e0 m ⟨i, lt_of_lt_of_le hin hnm⟩ =
      embeddingStages K hK B hB e0 n ⟨i, hin⟩ := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [show (⟨i, lt_of_lt_of_le hin (hnm.trans (Nat.le_succ m))⟩ : Fin (m + 1)) =
      (⟨i, lt_of_lt_of_le hin hnm⟩ : Fin m).castSucc from rfl,
      embeddingStages_successor K hK B hB e0 m _, ih]

noncomputable def countableEmbeddingMap {inj : Bool} (K : RelStructure L X)
    (hK : OnePointExtensionProperty inj K) (B : RelStructure L Nat)
    (hB : Admissible inj B) (e0 : RelEmbedding (initialSegment B 0) K) (i : Nat) : X :=
  embeddingStages K hK B hB e0 (i + 1) ⟨i, Nat.lt_succ_self i⟩

theorem countableEmbeddingMap_at_stage {inj : Bool} (K : RelStructure L X)
    (hK : OnePointExtensionProperty inj K) (B : RelStructure L Nat)
    (hB : Admissible inj B) (e0 : RelEmbedding (initialSegment B 0) K)
    {i n : Nat} (hi : i < n) : countableEmbeddingMap K hK B hB e0 i =
      embeddingStages K hK B hB e0 n ⟨i, hi⟩ :=
  (embeddingStages_coherent K hK B hB e0 (Nat.lt_succ_self i) (by omega : i + 1 ≤ n)).symm

noncomputable def countableEmbeddingNat {inj : Bool} (K : RelStructure L X)
    (hK : OnePointExtensionProperty inj K) (B : RelStructure L Nat)
    (hB : Admissible inj B) (e0 : RelEmbedding (initialSegment B 0) K) : RelEmbedding B K where
  toFun := countableEmbeddingMap K hK B hB e0
  injective := by
    intro i j hij
    let n := max i j + 1
    have hi : i < n := by dsimp [n]; omega
    have hj : j < n := by dsimp [n]; omega
    rw [countableEmbeddingMap_at_stage K hK B hB e0 hi,
      countableEmbeddingMap_at_stage K hK B hB e0 hj] at hij
    exact congrArg Fin.val ((embeddingStages K hK B hB e0 n).injective hij)
  map_rel := by
    intro r R t
    let n := (Finset.univ : Finset (Fin r)).sup t + 1
    have ht : ∀ i : Fin r, t i < n := by
      intro i
      exact lt_of_le_of_lt (Finset.le_sup (Finset.mem_univ i)) (Nat.lt_succ_self _)
    let s : Fin r → Fin n := fun i => ⟨t i, ht i⟩
    have hf : (countableEmbeddingMap K hK B hB e0) ∘ t =
        (embeddingStages K hK B hB e0 n) ∘ s := by
      funext i
      exact countableEmbeddingMap_at_stage K hK B hB e0 (ht i)
    rw [hf]
    exact (embeddingStages K hK B hB e0 n).map_rel R s

/-- An empty-domain embedding exists in every positive-arity language.
The more general construction above keeps it explicit for fixed nullaries. -/
def emptyEmbedding [IsEmpty (L.Rel 0)] (B : RelStructure L Nat) (K : RelStructure L X) :
    RelEmbedding (initialSegment B 0) K where
  toFun := Fin.elim0
  injective := by intro i; exact i.elim0
  map_rel := by
    intro r R t
    cases r with
    | zero => exact isEmptyElim R
    | succ r => exact (t 0).elim0

theorem universal_on_nat {inj : Bool} [IsEmpty (L.Rel 0)] (K : RelStructure L X)
    (hK : OnePointExtensionProperty inj K) (B : RelStructure L Nat) (hB : Admissible inj B) :
    Nonempty (RelEmbedding B K) :=
  ⟨countableEmbeddingNat K hK B hB (emptyEmbedding B K)⟩

def pushedStructure {V : Type} (B : RelStructure L V) (code : V ↪ Nat) : RelStructure L Nat where
  rel R t := ∃ u : Fin _ → V, code ∘ u = t ∧ B.rel R u

theorem pushedStructure_pullback {V : Type} (B : RelStructure L V) (code : V ↪ Nat) :
    (pushedStructure B code).pullback code = B := by
  apply RelStructure.ext_rel
  intro r R t
  constructor
  · rintro ⟨u, hu, hR⟩
    have heq : u = t := by
      funext i
      exact code.injective (congrFun hu i)
    simpa only [heq] using hR
  · intro hR
    exact ⟨t, rfl, hR⟩

def pushEmbedding {V : Type} (B : RelStructure L V) (code : V ↪ Nat) :
    RelEmbedding B (pushedStructure B code) where
  toFun := code
  injective := code.injective
  map_rel := by
    intro r R t
    constructor
    · intro hR
      exact ⟨t, rfl, hR⟩
    · rintro ⟨u, hu, hR⟩
      have heq : u = t := by funext i; exact code.injective (congrFun hu i)
      simpa only [heq] using hR

theorem pushedStructure_admissible {inj : Bool} {V : Type}
    (B : RelStructure L V) (hB : Admissible inj B) (code : V ↪ Nat) :
    Admissible inj (pushedStructure B code) := by
  intro htrue r R t hr ht
  obtain ⟨u, hu, hR⟩ := ht
  rw [← hu]
  exact code.injective.comp (hB htrue r R u hr hR)

/-- Countable universality in both affirmative modes, with the positive-arity
version supplying the empty initial embedding automatically. Every tuple is
checked at a common finite stage, even in an infinite language. -/
noncomputable def countableEmbedding {inj : Bool} [IsEmpty (L.Rel 0)]
    {V : Type} [Countable V] (K : RelStructure L X) (hK : OnePointExtensionProperty inj K)
    (B : RelStructure L V) (hB : Admissible inj B) : RelEmbedding B K := by
  letI := Encodable.ofCountable V
  let code : V ↪ Nat := ⟨Encodable.encode, Encodable.encode_injective⟩
  let C := pushedStructure B code
  exact (countableEmbeddingNat K hK C (pushedStructure_admissible B hB code)
    (emptyEmbedding C K)).comp (pushEmbedding B code)

theorem universal_for_countable {inj : Bool} [IsEmpty (L.Rel 0)]
    {V : Type} [Countable V] (K : RelStructure L X) (hK : OnePointExtensionProperty inj K)
    (B : RelStructure L V) (hB : Admissible inj B) : Nonempty (RelEmbedding B K) :=
  ⟨countableEmbedding K hK B hB⟩

def NullaryAgrees {V W : Type} (B : RelStructure L V) (K : RelStructure L W) : Prop :=
  ∀ (R : L.Rel 0) (t : Fin 0 → V) (u : Fin 0 → W), B.rel R t ↔ K.rel R u

def emptyEmbeddingOfNullary (B : RelStructure L Nat) (K : RelStructure L X)
    (hnull : NullaryAgrees B K) : RelEmbedding (initialSegment B 0) K where
  toFun := Fin.elim0
  injective := by intro i; exact i.elim0
  map_rel := by
    intro r R t
    cases r with
    | zero => exact hnull R (Fin.val ∘ t) (Fin.elim0 ∘ t)
    | succ r => exact (t 0).elim0

theorem nullaryAgrees_push {V : Type} (B : RelStructure L V) (K : RelStructure L X)
    (code : V ↪ Nat) (hnull : NullaryAgrees B K) : NullaryAgrees (pushedStructure B code) K := by
  intro R t u
  constructor
  · rintro ⟨s, _, hR⟩
    exact (hnull R s u).mp hR
  · intro hR
    refine ⟨Fin.elim0, ?_, (hnull R Fin.elim0 u).mpr hR⟩
    funext i
    exact i.elim0

/-- Universality in the fixed-nullary cases uses exactly agreement of the
nullary truth values, rather than dropping those symbols from embeddings. -/
noncomputable def countableEmbeddingOfNullary {inj : Bool} {V : Type} [Countable V]
    (K : RelStructure L X) (hK : OnePointExtensionProperty inj K)
    (B : RelStructure L V) (hB : Admissible inj B) (hnull : NullaryAgrees B K) : RelEmbedding B K := by
  letI := Encodable.ofCountable V
  let code : V ↪ Nat := ⟨Encodable.encode, Encodable.encode_injective⟩
  let C := pushedStructure B code
  exact (countableEmbeddingNat K hK C (pushedStructure_admissible B hB code)
    (emptyEmbeddingOfNullary C K (nullaryAgrees_push B K code hnull))).comp (pushEmbedding B code)

end RelationalRamsey632.Existence
