import RelationalRamsey632.Source.RelationalModel
import RelationalRamsey632.Source.FiniteCoreEquality
import RelationalRamsey632.Source.MarkedSampling

/-! Actual finite source embeddings from normalized marked patterns. -/

namespace RelationalRamsey632.Source

variable {A : ℕ → Type} {U F : Type}
    [Fintype F] (p : RelStructure (normalFormLanguage A U) F)
    (j : RelEmbedding p (normalFormStructure A U))

noncomputable def patternTuple : Fin (Fintype.card F) → Vertex A U :=
  j ∘ (Fintype.equivFin F).symm

noncomputable def patternMap (x : F) : Vertex A U :=
  normalForm (patternTuple p j) ((Fintype.equivFin F) x)

theorem patternMap_injective : Function.Injective (patternMap p j) :=
  (normalForm_injective (patternTuple p j)
    (j.injective.comp (Fintype.equivFin F).symm.injective)).comp
      (Fintype.equivFin F).injective

theorem patternMap_normalForms {r : ℕ} (t : Fin r → F) :
    normalForm (patternMap p j ∘ t) = normalForm (j ∘ t) := by
  have hn := normalForm_subtuple (patternTuple p j) ((Fintype.equivFin F) ∘ t)
  have heq : patternTuple p j ∘ (Fintype.equivFin F) ∘ t = j ∘ t := by
    funext k
    exact congrArg j ((Fintype.equivFin F).symm_apply_apply (t k))
  change normalForm (normalForm (patternTuple p j) ∘ ((Fintype.equivFin F) ∘ t)) =
    normalForm (j ∘ t)
  exact hn.trans (congrArg normalForm heq)

noncomputable def patternEmbedding : RelEmbedding p (normalFormStructure A U) where
  toFun := patternMap p j
  injective := patternMap_injective p j
  map_rel R t := by
    rw [j.map_rel R t]
    change (Function.Injective (j ∘ t) ∧ normalForm (j ∘ t) = R.val) ↔
      (Function.Injective (patternMap p j ∘ t) ∧ normalForm (patternMap p j ∘ t) = R.val)
    rw [j.injective.of_comp_iff t, (patternMap_injective p j).of_comp_iff t,
      patternMap_normalForms p j t]

@[simp] theorem patternEmbedding_apply (x : F) :
    patternEmbedding p j x = normalForm (patternTuple p j) ((Fintype.equivFin F) x) := rfl

theorem patternEmbedding_height (x : F) :
    (patternEmbedding p j x).2.height < (tupleLevels (patternTuple p j)).card :=
  normalForm_height_bound (patternTuple p j) ((Fintype.equivFin F) x)

namespace FiniteStrongVector

omit [Fintype F]

variable {e : ℕ → ℕ} {he : StrictMono e} {h : ℕ}
    (V : FiniteStrongVector A e he h)

theorem imageMap_injective (k : RelEmbedding p (normalFormStructure A U))
    (hk : ∀ x, (k x).2.height < h) :
    Function.Injective (V.mapVertices ∘ k) := by
  intro x y hxy
  apply k.injective
  apply Prod.ext
  · simpa only [mapVertices, Function.comp_apply] using
      congrArg (fun v : Vertex A U => v.1) hxy
  · have hs : 0 + (k x).2.height < h := by simpa only [Nat.zero_add] using hk x
    have ht : 0 + (k y).2.height < h := by simpa only [Nat.zero_add] using hk y
    apply V.mapNode_injective (k x).2 (k y).2 hs ht
    have hh := congrArg (fun v : Vertex A U => v.2) hxy
    simpa only [Function.comp_apply, mapVertices,
      V.mapNodeDefault_active _ hs, V.mapNodeDefault_active _ ht] using hh

noncomputable def imageEmbedding (k : RelEmbedding p (normalFormStructure A U))
    (hk : ∀ x, (k x).2.height < h) :
    RelEmbedding p (normalFormStructure A U) where
  toFun := V.mapVertices ∘ k
  injective := V.imageMap_injective p k hk
  map_rel R t := by
    rw [k.map_rel R t]
    have hnf := V.normalForm_mapVertices (k ∘ t) (fun x => hk (t x))
    change (Function.Injective (k ∘ t) ∧ normalForm (k ∘ t) = R.val) ↔
      (Function.Injective ((V.mapVertices ∘ k) ∘ t) ∧
        normalForm ((V.mapVertices ∘ k) ∘ t) = R.val)
    rw [k.injective.of_comp_iff t, (V.imageMap_injective p k hk).of_comp_iff t]
    exact and_congr_right (fun _ => by rw [Function.comp_assoc, hnf])

theorem imageEmbedding_eq_of_core {f : ℕ → ℕ} {hf : StrictMono f}
    (W : FiniteStrongVector A f hf h) (hc : V.core = W.core)
    (k : RelEmbedding p (normalFormStructure A U)) (hk : ∀ x, (k x).2.height < h) :
    V.imageEmbedding p k hk = W.imageEmbedding p k hk := by
  apply RelEmbedding.ext
  intro x
  exact V.mapVertices_eq_of_core W hc (k x) (hk x)

end FiniteStrongVector

end RelationalRamsey632.Source
