import RelationalRamsey632.Transfer.IsoRepresentatives

namespace RelationalRamsey632.Transfer

variable {L : Language} (K : RelStructure L ℕ)

abbrev PositiveIsoIndex := {j : Named.IsoAgeIndex K // 0 < Named.isoAgeArity K j}

def positiveArity (j : PositiveIsoIndex K) : ℕ := Named.isoAgeArity K j.val

noncomputable def positiveFamily (j : PositiveIsoIndex K) :
    RelStructure L (Fin (positiveArity K j)) := Named.isoAgeFamily K j.val

abbrev BoundedPositiveIsoIndex (n : ℕ) := {j : PositiveIsoIndex K // positiveArity K j ≤ n}

theorem positiveIndex_nonempty : Nonempty (PositiveIsoIndex K) := by
  let b := K.pullback (Fin.val : Fin 1 → ℕ)
  let e := RelEmbedding.pullback K (Fin.val : Fin 1 → ℕ) Fin.val_injective
  let j : Named.IsoAgeIndex K :=
    ⟨1, Quotient.mk (Named.ageSetoid K 1) ⟨b, ⟨e⟩⟩⟩
  exact ⟨⟨j, Nat.zero_lt_one⟩⟩

theorem positiveIndex_countable (hK : K.InjectiveRelations) (hL : L.FinitePerArity) :
    Countable (PositiveIsoIndex K) := by
  haveI := Named.countable_iso_age K hK hL
  infer_instance

theorem boundedPositiveIndex_finite (hK : K.InjectiveRelations) (hL : L.FinitePerArity)
    (n : ℕ) : Finite (BoundedPositiveIsoIndex K n) := by
  letI : ∀ r : Fin (n + 1), Finite (Named.IsoAge K r.val) :=
    fun r => Named.finite_iso_age K hK hL r.val
  let f : BoundedPositiveIsoIndex K n → Σ r : Fin (n + 1), Named.IsoAge K r.val :=
    fun j => ⟨⟨positiveArity K j.val, Nat.lt_succ_of_le j.property⟩, j.val.val.snd⟩
  let g : (Σ r : Fin (n + 1), Named.IsoAge K r.val) → Named.IsoAgeIndex K :=
    fun j => ⟨j.fst.val, j.snd⟩
  exact Finite.of_injective f (by
    intro j k h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg g h)

theorem boundedPositiveIndex_zero : IsEmpty (BoundedPositiveIsoIndex K 0) :=
  ⟨fun j => (Nat.not_le_of_lt j.val.property) j.property⟩

theorem positiveFamily_covers_nonempty {F : Type} [Finite F] [Nonempty F]
    (b : RelStructure L F) (hb : Nonempty (RelEmbedding b K)) :
    ∃ j : PositiveIsoIndex K, ∃ u : RelEmbedding (positiveFamily K j) b,
      Function.Surjective u := by
  classical
  obtain ⟨j, u, hu⟩ := Named.iso_age_family_covers K F b hb
  obtain ⟨x, _⟩ := hu (Classical.choice (inferInstance : Nonempty F))
  have hj : 0 < Named.isoAgeArity K j := (Nat.zero_le x.val).trans_lt x.isLt
  exact ⟨⟨j, hj⟩, u, hu⟩

noncomputable def sizeThreshold (hK : K.InjectiveRelations) (hL : L.FinitePerArity)
    (index : PositiveIsoIndex K → ℕ) (n : ℕ) : ℕ := by
  classical
  letI := boundedPositiveIndex_finite K hK hL n
  letI := Fintype.ofFinite (BoundedPositiveIsoIndex K n)
  exact Finset.univ.sup (fun j : BoundedPositiveIsoIndex K n => index j.val + 1)

theorem sizeThreshold_ge (hK : K.InjectiveRelations) (hL : L.FinitePerArity)
    (index : PositiveIsoIndex K → ℕ) (n : ℕ) (j : PositiveIsoIndex K)
    (hj : positiveArity K j ≤ n) : index j + 1 ≤ sizeThreshold K hK hL index n := by
  classical
  letI := boundedPositiveIndex_finite K hK hL n
  letI := Fintype.ofFinite (BoundedPositiveIsoIndex K n)
  unfold sizeThreshold
  exact Finset.le_sup (f := fun j : BoundedPositiveIsoIndex K n => index j.val + 1)
    (Finset.mem_univ (⟨j, hj⟩ : BoundedPositiveIsoIndex K n))

theorem sizeThreshold_monotone (hK : K.InjectiveRelations) (hL : L.FinitePerArity)
    (index : PositiveIsoIndex K → ℕ) : Monotone (sizeThreshold K hK hL index) := by
  classical
  intro n m hnm
  unfold sizeThreshold
  apply Finset.sup_le
  intro j _
  exact sizeThreshold_ge K hK hL index m j.val (j.property.trans hnm)

theorem sizeThreshold_zero (hK : K.InjectiveRelations) (hL : L.FinitePerArity)
    (index : PositiveIsoIndex K → ℕ) : sizeThreshold K hK hL index 0 = 0 := by
  classical
  haveI := boundedPositiveIndex_zero K
  simp [sizeThreshold]

end RelationalRamsey632.Transfer
