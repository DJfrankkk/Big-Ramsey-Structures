import CombinedRamsey.Negative.Main

/-! The ordinary big Ramsey structure definition in Section 2 of the paper.
Degree one of expanded types is not part of this definition and is not
needed to refute it. Infinite singleton degree alone suffices. -/

namespace CombinedRamsey.Negative

open RelationalRamsey632 RelationalRamsey632.RelStructure RelationalRamsey632.Transfer

def OrdinaryBigRamseyExpansion {S : Language} (ι : LanguageInclusion Lstar S)
    (Z : RelStructure S ℕ) : Prop :=
  Z.reduct ι = Kstar ∧
    ∀ (F : Type) [Finite F] (A : RelStructure Lstar F)
      (_hA : Nonempty (RelEmbedding A Kstar)),
      (palette A Kstar Z).Finite ∧ Unavoidable A Kstar Z ∧
        ExactEmbeddingDegree A Kstar (palette A Kstar Z).ncard

theorem no_finite_optimal_singleton_expansion {S : Language} (Z : RelStructure S ℕ)
    (h : ExactEmbeddingDegree deltaStar Kstar (palette deltaStar Kstar Z).ncard) : False :=
  deltaStar_no_finite_embedding_degree _ h.1

theorem no_ordinary_big_ramsey_structure {S : Language} (ι : LanguageInclusion Lstar S)
    (Z : RelStructure S ℕ) : ¬ OrdinaryBigRamseyExpansion ι Z := by
  rintro ⟨_, h⟩
  exact no_finite_optimal_singleton_expansion Z ((h (Fin 1) deltaStar deltaStar_in_age).2.2)

theorem no_precompact_big_ramsey_structure {S : Language} (ι : LanguageInclusion Lstar S)
    (Z : RelStructure S ℕ) : ¬ OrdinaryBigRamseyExpansion ι Z :=
  no_ordinary_big_ramsey_structure ι Z

end CombinedRamsey.Negative
