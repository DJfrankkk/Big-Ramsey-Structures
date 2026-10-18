import RelationalRamsey632.Source.RelationalModel
import RelationalRamsey632.Source.ValuationSampling

namespace RelationalRamsey632.Source.StrongVector

variable {A : ℕ → Type} {U : Type} {e : ℕ → ℕ} {he : StrictMono e}
    (S : StrongVector A e he)

theorem mapVertices_injective : Function.Injective (S.mapVertices (U := U)) := by
  intro v w h
  apply Prod.ext
  · change (S.mapVertices v).fst = (S.mapVertices w).fst
    exact congrArg (fun z : Vertex A U => z.fst) h
  · exact S.mapNode_injective 0 (congrArg (fun z : Vertex A U => z.snd) h)

noncomputable def relationalEmbedding :
    RelEmbedding (normalFormStructure A U) (normalFormStructure A U) :=
  Transfer.embeddingOfMap _ ((embeddings_iff_normalForms A U S.mapVertices).mpr
    ⟨S.mapVertices_injective, fun _ _ t _ => S.normalForm_mapVertices t⟩)

@[simp] theorem relationalEmbedding_apply (v : Vertex A U) :
    S.relationalEmbedding v = S.mapVertices v := rfl

end RelationalRamsey632.Source.StrongVector
