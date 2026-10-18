import RelationalRamsey632.Source.CompleteRamsey
import RelationalRamsey632.Transfer.EmptyAndRelabelling

namespace RelationalRamsey632.Source

variable {A : ℕ → Type} [∀ j, Fintype (A j)] [∀ j, Nonempty (A j)]
    {U : Type}

theorem exact_source_embedding_degree {F : Type} [Finite F]
    (p : RelStructure (normalFormLanguage A U) F)
    (hp : Nonempty (RelEmbedding p (normalFormStructure A U))) :
    Transfer.ExactEmbeddingDegree p (normalFormStructure A U) 1 :=
  Transfer.exact_degree_one_of_source p (normalFormStructure A U) hp (sourceDegreeOne p hp)

end RelationalRamsey632.Source
