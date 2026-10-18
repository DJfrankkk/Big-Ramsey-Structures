import RelationalRamsey632.Source.RamseyReduction
import RelationalRamsey632.Milliken.SourceSpecialization

namespace RelationalRamsey632.Source

theorem sourceDegreeOne {A : ℕ → Type}
    [∀ j, Fintype (A j)] [∀ j, Nonempty (A j)] {U F : Type} [Finite F]
    (p : RelStructure (normalFormLanguage A U) F)
    (hp : Nonempty (RelEmbedding p (normalFormStructure A U))) :
    Transfer.SourceDegreeOne (normalFormStructure A U) p :=
  sourceDegreeOne_of_vectorMilliken Milliken.source_vector_milliken p hp

end RelationalRamsey632.Source
