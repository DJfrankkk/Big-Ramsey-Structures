import CombinedRamsey.Negative.EncodingForbidden
import CombinedRamsey.Negative.ConstrainedGeneric

/-! Actual closure rules of the constrained class, using the proved four guards. -/

namespace CombinedRamsey.Negative

open RelationalRamsey632 RelationalRamsey632.Existence

def LegalModel {X : Type} (A : RelStructure language X) : Prop :=
  A.InjectiveRelations ∧ (Table.ofRel A).Legal

def Avoid {X : Type} (A : RelStructure language X) : Prop :=
  (∀ F : Table (Fin 3), forbidden3 F → ¬ Nonempty (RelEmbedding F.toRel A)) ∧
  (∀ F : Table (Fin 4), forbidden4 F → ¬ Nonempty (RelEmbedding F.toRel A))

theorem legalModel_iff_avoid {X : Type} (A : RelStructure language X)
    (hA : A.InjectiveRelations) : LegalModel A ↔ Avoid A := by
  have he := Table.toRel_ofRel A hA
  constructor
  · intro h
    have hf := (legal_iff_forb (Table.ofRel A)).mp h.2
    simpa only [Forb, Avoid, he] using hf
  · intro h
    refine ⟨hA, (legal_iff_forb (Table.ofRel A)).mpr ?_⟩
    simpa only [Forb, Avoid, he] using h

theorem legalModel_hereditary {X Y : Type} (A : RelStructure language X)
    (hA : LegalModel A) (f : Y → X) (hf : Function.Injective f) :
    LegalModel (A.pullback f) := by
  refine ⟨A.injectiveRelations_pullback hA.1 f, ?_⟩
  rw [Table.ofRel_pullback]
  exact Table.legal_pullback (Table.ofRel A) f hf hA.2

noncomputable def factorEmbedding {L : Language} {F X Y : Type}
    {A : RelStructure L F} {B : RelStructure L X} {C : RelStructure L Y}
    (f : RelEmbedding A C) (e : RelEmbedding B C)
    (hr : ∀ x, f x ∈ Set.range e) : RelEmbedding A B := by
  classical
  choose u hu using hr
  exact {
    toFun := u
    injective := fun x y h => f.injective ((hu x).symm.trans ((congrArg e h).trans (hu y)))
    map_rel := fun R t => by
      have he : e ∘ u ∘ t = f ∘ t := funext (fun i => hu (t i))
      exact (f.map_rel R t).trans (he ▸ (e.map_rel R (u ∘ t)).symm) }

theorem legalModel_of_image_choices {X Y Z : Type} (A : RelStructure language X)
    (B : RelStructure language Y) (M : RelStructure language Z)
    (hA : LegalModel A) (hB : LegalModel B) (hM : M.InjectiveRelations)
    (a : RelEmbedding A M) (b : RelEmbedding B M)
    (hclique : ∀ (n : ℕ) (F : Table (Fin n)), CompleteAll F →
      ∀ f : RelEmbedding F.toRel M,
        (∀ x, f x ∈ Set.range a) ∨ (∀ x, f x ∈ Set.range b)) : LegalModel M := by
  have ha := (legalModel_iff_avoid A hA.1).mp hA
  have hb := (legalModel_iff_avoid B hB.1).mp hB
  apply (legalModel_iff_avoid M hM).mpr
  constructor
  · intro F hF hf
    rcases hclique 3 F (forbidden3_complete hF) hf.some with h | h
    · exact ha.1 F hF ⟨factorEmbedding hf.some a h⟩
    · exact hb.1 F hF ⟨factorEmbedding hf.some b h⟩
  · intro F hF hf
    rcases hclique 4 F (forbidden4_complete hF) hf.some with h | h
    · exact ha.2 F hF ⟨factorEmbedding hf.some a h⟩
    · exact hb.2 F hF ⟨factorEmbedding hf.some b h⟩

theorem injective_of_finite_pullbacks {X : Type} (A : RelStructure language X)
    (h : ∀ n (f : Fin n → X), Function.Injective f → (A.pullback f).InjectiveRelations) :
    A.InjectiveRelations := by
  classical
  intro r R t hr ht i j hij
  let S := Set.range t
  haveI : Finite S := Set.finite_range t
  letI := Fintype.ofFinite S
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let f : Fin (Fintype.card S) → X := fun x => (e.symm x).val
  let u : Fin r → Fin (Fintype.card S) := fun a => e ⟨t a, ⟨a, rfl⟩⟩
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  have he : f ∘ u = t := by funext a; exact congrArg Subtype.val (e.symm_apply_apply _)
  have hu : (A.pullback f).rel R u := by
    change A.rel R (f ∘ u)
    rw [he]
    exact ht
  exact (h _ f hf) r R u hr hu (congrArg e (Subtype.ext hij))

theorem legalModel_finiteCharacter {X : Type} (A : RelStructure language X)
    (h : ∀ n (f : Fin n → X), Function.Injective f → LegalModel (A.pullback f)) :
    LegalModel A := by
  have hi := injective_of_finite_pullbacks A (fun n f hf => (h n f hf).1)
  apply (legalModel_iff_avoid A hi).mpr
  constructor
  · intro F hF he
    let f := he.some
    have hh := h 3 f f.injective
    have hp := f.pullback_eq
    rw [hp] at hh
    exact forbidden3_not_legal hF ((Table.canonical_legal_iff F).mp hh.2)
  · intro F hF he
    let f := he.some
    have hh := h 4 f f.injective
    have hp := f.pullback_eq
    rw [hp] at hh
    exact forbidden4_not_legal hF ((Table.canonical_legal_iff F).mp hh.2)

theorem legalModel_empty : LegalModel (nullaryOnly language (fun _ => False) Empty) := by
  constructor
  · intro r R t _
    cases R <;> exact Empty.elim (t 0)
  · constructor <;> intro a <;> exact Empty.elim a

theorem complete_pair_rel {n : ℕ} {F : Table (Fin n)} (hF : CompleteAll F)
    {i j : Fin n} (hij : i ≠ j) : F.toRel.rel (Symbol.binary .E) ![i,j] :=
  ⟨hij, (hF i j hij).2.1⟩

theorem isolated_clique_old {X : Type} (A : RelStructure language X)
    {n : ℕ} (F : Table (Fin n)) (hF : CompleteAll F)
    (hn : ∀ i : Fin n, ∃ j, i ≠ j)
    (f : RelEmbedding F.toRel (OnePointExtension.isolated A)) :
    ∀ i, f i ∈ Set.range (Sum.inl : X → X ⊕ Unit) := by
  intro i
  obtain ⟨j, hij⟩ := hn i
  have he := (f.map_rel (Symbol.binary .E) ![i,j]).mp (complete_pair_rel hF hij)
  obtain ⟨u, hu, _⟩ := he
  exact ⟨u 0, congrFun hu 0⟩

theorem legalModel_isolated {X : Type} (A : RelStructure language X)
    (hA : LegalModel A) : LegalModel (OnePointExtension.isolated A) := by
  have hi := OnePointExtension.isolated_admissible (inj := true) (fun _ => hA.1) rfl
  have ha := (legalModel_iff_avoid A hA.1).mp hA
  let old := (OnePointExtension.default (inj := true) (fun _ => hA.1)).inclusion
  apply (legalModel_iff_avoid _ hi).mpr
  constructor
  · intro F hF hf
    have hold := isolated_clique_old A F (forbidden3_complete hF)
      (fun i => by obtain ⟨j,hj⟩ := exists_ne i; exact ⟨j,hj.symm⟩) hf.some
    exact ha.1 F hF ⟨factorEmbedding hf.some old hold⟩
  · intro F hF hf
    have hold := isolated_clique_old A F (forbidden4_complete hF)
      (fun i => by obtain ⟨j,hj⟩ := exists_ne i; exact ⟨j,hj.symm⟩) hf.some
    exact ha.2 F hF ⟨factorEmbedding hf.some old hold⟩

theorem star_new_equal {X : Type} (A : RelStructure language X)
    (E F : ConstrainedGeneric.Extensions LegalModel A)
    (h : (ConstrainedGeneric.nextModel LegalModel A).rel (Symbol.binary .E)
      ![Sum.inr E, Sum.inr F]) : E = F := by
  obtain ⟨D, u, hu, _⟩ := h
  have h0 : OnePointStage.place A D (u 0) = Sum.inr E.val := congrFun hu 0
  have h1 : OnePointStage.place A D (u 1) = Sum.inr F.val := congrFun hu 1
  have he : D = E.val := by
    cases hq : u 0 with
    | inl x => simp [OnePointStage.place, hq] at h0
    | inr x => simpa [OnePointStage.place, hq] using h0
  have hf : D = F.val := by
    cases hq : u 1 with
    | inl x => simp [OnePointStage.place, hq] at h1
    | inr x => simpa [OnePointStage.place, hq] using h1
  exact Subtype.ext (he.symm.trans hf)

theorem star_clique_side {X : Type} (A : RelStructure language X)
    {n : ℕ} (F : Table (Fin n)) (hF : CompleteAll F)
    (f : RelEmbedding F.toRel (ConstrainedGeneric.nextModel LegalModel A)) :
    (∀ i, f i ∈ Set.range (Sum.inl : X → ConstrainedGeneric.NextDomain LegalModel A)) ∨
    ∃ E : ConstrainedGeneric.Extensions LegalModel A,
      ∀ i, f i ∈ Set.range (ConstrainedGeneric.extensionEmbedding LegalModel A E) := by
  classical
  by_cases hex : ∃ i E, f i = Sum.inr E
  · obtain ⟨i,E,hi⟩ := hex
    right
    refine ⟨E, ?_⟩
    intro j
    cases hj : f j with
    | inl x => exact ⟨Sum.inl x, rfl⟩
    | inr D =>
      have hED : E = D := by
        by_cases hij : i = j
        · simpa [hij, hj] using hi.symm
        · have ht := (f.map_rel (Symbol.binary .E) ![i,j]).mp (complete_pair_rel hF hij)
          have heq : f ∘ ![i,j] = ![Sum.inr E, Sum.inr D] := by
            funext q; fin_cases q <;> simp [hi, hj]
          rw [heq] at ht
          exact star_new_equal A E D ht
      exact ⟨Sum.inr (), by change Sum.inr E = Sum.inr D; rw [hED]⟩
  · left
    intro i
    cases hi : f i with
    | inl x => exact ⟨x, rfl⟩
    | inr E => exact (hex ⟨i,E,hi⟩).elim

theorem legalModel_star {X : Type} (A : RelStructure language X)
    (hA : LegalModel A) : LegalModel (ConstrainedGeneric.nextModel LegalModel A) := by
  have hi := ConstrainedGeneric.nextModel_injective LegalModel A
  have ha := (legalModel_iff_avoid A hA.1).mp hA
  let old := ConstrainedGeneric.oldEmbedding LegalModel A hA.1
  apply (legalModel_iff_avoid _ hi).mpr
  constructor
  · intro F hF hf
    rcases star_clique_side A F (forbidden3_complete hF) hf.some with hold | ⟨E,hE⟩
    · exact ha.1 F hF ⟨factorEmbedding hf.some old hold⟩
    · have he := (legalModel_iff_avoid E.val.model E.property.1).mp E.property
      exact he.1 F hF ⟨factorEmbedding hf.some (ConstrainedGeneric.extensionEmbedding LegalModel A E) hE⟩
  · intro F hF hf
    rcases star_clique_side A F (forbidden4_complete hF) hf.some with hold | ⟨E,hE⟩
    · exact ha.2 F hF ⟨factorEmbedding hf.some old hold⟩
    · have he := (legalModel_iff_avoid E.val.model E.property.1).mp E.property
      exact he.2 F hF ⟨factorEmbedding hf.some (ConstrainedGeneric.extensionEmbedding LegalModel A E) hE⟩

def amalgamOld {X : Type} {n : ℕ} (A : RelStructure language X)
    (B : RelStructure language (Fin (n+1)))
    (f : RelEmbedding (B.pullback Fin.castSucc) A) :
    RelEmbedding A (OnePointAmalgam.model A B f) where
  toFun := Sum.inl
  injective := Sum.inl_injective
  map_rel R t := (Iff.of_eq (congrArg (fun C => C.rel R t)
    (OnePointAmalgam.old_eq A B f))).symm

theorem amalgam_new_pair_range {X : Type} {n : ℕ} (A : RelStructure language X)
    (B : RelStructure language (Fin (n+1)))
    (f : RelEmbedding (B.pullback Fin.castSucc) A) (z : X ⊕ Unit)
    (h : (OnePointAmalgam.model A B f).rel (Symbol.binary .E) ![Sum.inr (),z]) :
    z ∈ Set.range (OnePointAmalgam.embedding A B f) := by
  rcases h with ⟨u,hu,_⟩ | ⟨v,hv,_⟩
  · have h0 := congrFun hu 0
    simp at h0
  · exact ⟨v 1, congrFun hv 1⟩

theorem amalgam_clique_side {X : Type} {n : ℕ} (A : RelStructure language X)
    (B : RelStructure language (Fin (n+1)))
    (f : RelEmbedding (B.pullback Fin.castSucc) A)
    {m : ℕ} (F : Table (Fin m)) (hF : CompleteAll F)
    (g : RelEmbedding F.toRel (OnePointAmalgam.model A B f)) :
    (∀ i, g i ∈ Set.range (amalgamOld A B f)) ∨
    (∀ i, g i ∈ Set.range (OnePointAmalgam.embedding A B f)) := by
  classical
  by_cases hex : ∃ i, g i = Sum.inr ()
  · obtain ⟨i,hi⟩ := hex
    right
    intro j
    by_cases hij : i = j
    · subst j
      exact ⟨Fin.last n, by simp [OnePointAmalgam.embedding, hi]⟩
    · have ht := (g.map_rel (Symbol.binary .E) ![i,j]).mp (complete_pair_rel hF hij)
      have heq : g ∘ ![i,j] = ![Sum.inr (),g j] := by
        funext q; fin_cases q <;> simp [hi]
      rw [heq] at ht
      exact amalgam_new_pair_range A B f (g j) ht
  · left
    intro i
    cases hi : g i with
    | inl x => exact ⟨x, rfl⟩
    | inr u => cases u; exact (hex ⟨i,hi⟩).elim

theorem legalModel_amalgam {X : Type} {n : ℕ} (A : RelStructure language X)
    (B : RelStructure language (Fin (n+1))) (hA : LegalModel A) (hB : LegalModel B)
    (f : RelEmbedding (B.pullback Fin.castSucc) A) :
    LegalModel (OnePointAmalgam.model A B f) :=
  legalModel_of_image_choices A B (OnePointAmalgam.model A B f) hA hB
    (OnePointAmalgam.model_admissible A B f (inj := true) (fun _ => hA.1) (fun _ => hB.1) rfl)
    (amalgamOld A B f) (OnePointAmalgam.embedding A B f)
    (fun _ F hF g => amalgam_clique_side A B f F hF g)

def legalRules : ConstrainedGeneric.Rules (@LegalModel) where
  injective _ h := h.1
  empty := legalModel_empty
  hereditary := legalModel_hereditary
  finiteCharacter := legalModel_finiteCharacter
  isolated := legalModel_isolated
  amalgam := legalModel_amalgam
  star := legalModel_star

end CombinedRamsey.Negative
