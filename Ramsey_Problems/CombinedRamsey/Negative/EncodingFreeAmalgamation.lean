import CombinedRamsey.Negative.EncodingGenericRules
import RelationalRamsey632.Existence.FreeAmalgamation

/-! Genuine free amalgamation over any common finite (or infinite) base. -/

namespace CombinedRamsey.Negative

open RelationalRamsey632 RelationalRamsey632.Existence

theorem shared_clique_side {X Y Z : Type}
    (B : RelStructure language (X ⊕ Y)) (C : RelStructure language (X ⊕ Z))
    (hBC : B.pullback Sum.inl = C.pullback Sum.inl)
    {n : ℕ} (F : Table (Fin n)) (hF : CompleteAll F)
    (f : RelEmbedding F.toRel (SharedBaseAmalgam.model B C)) :
    (∀ i, f i ∈ Set.range (SharedBaseAmalgam.leftEmbedding B C hBC)) ∨
    (∀ i, f i ∈ Set.range (SharedBaseAmalgam.rightEmbedding B C hBC)) := by
  classical
  by_cases hex : ∃ i y, f i = Sum.inr (Sum.inl y)
  · obtain ⟨i,y,hi⟩ := hex
    left
    intro j
    cases hj : f j with
    | inl x => exact ⟨Sum.inl x,rfl⟩
    | inr yz =>
      cases yz with
      | inl y' => exact ⟨Sum.inr y',rfl⟩
      | inr z =>
        have hij : i ≠ j := by
          intro he
          have h := hi.symm.trans (he ▸ hj)
          cases h
        have ht := (f.map_rel (Symbol.binary .E) ![i,j]).mp (complete_pair_rel hF hij)
        rcases SharedBaseAmalgam.free B C hBC (Symbol.binary .E) (f ∘ ![i,j]) ht with hl | hr
        · obtain ⟨v,hv⟩ := hl 1
          cases v <;> simp [SharedBaseAmalgam.leftEmbedding, SharedBaseAmalgam.left, hj] at hv
        · obtain ⟨v,hv⟩ := hr 0
          cases v <;> simp [SharedBaseAmalgam.rightEmbedding, SharedBaseAmalgam.right, hi] at hv
  · right
    intro i
    cases hi : f i with
    | inl x => exact ⟨Sum.inl x,rfl⟩
    | inr yz =>
      cases yz with
      | inl y => exact (hex ⟨i,y,hi⟩).elim
      | inr z => exact ⟨Sum.inr z,rfl⟩

theorem legalModel_shared_free_amalgam {X Y Z : Type}
    (B : RelStructure language (X ⊕ Y)) (C : RelStructure language (X ⊕ Z))
    (hB : LegalModel B) (hC : LegalModel C)
    (hBC : B.pullback Sum.inl = C.pullback Sum.inl) :
    LegalModel (SharedBaseAmalgam.model B C) :=
  legalModel_of_image_choices B C (SharedBaseAmalgam.model B C) hB hC
    (SharedBaseAmalgam.model_admissible B C (inj := true) (fun _ => hB.1) (fun _ => hC.1) rfl)
    (SharedBaseAmalgam.leftEmbedding B C hBC) (SharedBaseAmalgam.rightEmbedding B C hBC)
    (fun _ F hF f => shared_clique_side B C hBC F hF f)

theorem legalModel_free_amalgam {X Y Z : Type} {A : RelStructure language X}
    {B : RelStructure language Y} {C : RelStructure language Z}
    (hB : LegalModel B) (hC : LegalModel C)
    (f : RelEmbedding A B) (g : RelEmbedding A C) :
    LegalModel (FreeAmalgamation.model f g) := by
  have hB' := legalModel_hereditary B hB (FreeAmalgamation.split f)
    (FreeAmalgamation.split f).injective
  have hC' := legalModel_hereditary C hC (FreeAmalgamation.split g)
    (FreeAmalgamation.split g).injective
  exact legalModel_shared_free_amalgam (FreeAmalgamation.splitModel f) (FreeAmalgamation.splitModel g)
    hB' hC' ((FreeAmalgamation.split_old_eq f).trans (FreeAmalgamation.split_old_eq g).symm)

end CombinedRamsey.Negative
