import RelationalRamsey632.Existence.GenericLimit
import RelationalRamsey632.Existence.SingletonTypes
import RelationalRamsey632.Existence.LanguageRange

/-! Exact age and countable universality of the constructed generic model. -/

namespace RelationalRamsey632.Existence

variable {L : Language} {X Y : Type} {inj : Bool}

theorem admissible_of_embedding {A : RelStructure L X} {B : RelStructure L Y}
    (e : RelEmbedding A B) (hB : Admissible inj B) : Admissible inj A := by
  intro hi r R t hr hR i j hij
  have h := hB hi r R (e ∘ t) hr ((e.map_rel R t).mp hR)
  exact h (congrArg e hij)

theorem nullaryAgrees_of_embedding {A : RelStructure L X} {B : RelStructure L Y}
    (e : RelEmbedding A B) : NullaryAgrees A B := by
  intro R t u
  have ht : e ∘ t = u := by
    funext i
    exact i.elim0
  exact ht ▸ e.map_rel R t

namespace GenericConstruction

variable (L : Language) (inj : Bool) (hL : LocallyFiniteLanguage L inj)
variable (θ : L.Rel 0 → Prop)

theorem fixed_nullary : FixedNullary L θ (limitModel L inj hL θ) :=
  limit_nullary L inj hL θ

theorem universal {V : Type} [Countable V] (B : RelStructure L V)
    (hB : Admissible inj B) (hθ : FixedNullary L θ B) :
    Nonempty (RelEmbedding B (limitModel L inj hL θ)) := by
  have hnull : NullaryAgrees B (limitModel L inj hL θ) := by
    intro R t u
    exact (hθ R t).trans (limit_nullary L inj hL θ R u).symm
  exact ⟨countableEmbeddingOfNullary (limitModel L inj hL θ)
    (extension_property L inj hL θ) B hB hnull⟩

theorem finite_age_exact {V : Type} [Finite V] (B : RelStructure L V) :
    Nonempty (RelEmbedding B (limitModel L inj hL θ)) ↔
      Admissible inj B ∧ FixedNullary L θ B := by
  constructor
  · rintro ⟨e⟩
    refine ⟨admissible_of_embedding e (limit_admissible L inj hL θ), ?_⟩
    intro R t
    exact (nullaryAgrees_of_embedding e R t Fin.elim0).trans
      (limit_nullary L inj hL θ R Fin.elim0)
  · rintro ⟨hB, hθ⟩
    exact universal L inj hL θ B hB hθ

end GenericConstruction

theorem ordinary_singleton_continuum (L : Language) (hL : L.FinitePerArity)
    [Infinite L.PositiveSymbol] (θ : L.Rel 0 → Prop) :
    Cardinal.mk (OrdinarySingletonType L θ) = 2 ^ Cardinal.aleph0 := by
  haveI := L.countable_positive_symbols hL
  rw [ordinary_singleton_cardinal, Cardinal.mk_eq_aleph0]

end RelationalRamsey632.Existence
