import CombinedRamsey.Negative.PersistenceLinkedAmalgam

namespace CombinedRamsey.Negative

open RelationalRamsey632 RelationalRamsey632.Existence

variable {L : Language} {X F : Type} {n : ℕ}
    {t : RelStructure L (Fin n ⊕ Unit)} {K : RelStructure L X}
    {b : RelEmbedding (t.pullback Sum.inl) K}

def linkedAnchorMap {a : RelStructure (LinkLanguage L (Fin n)) F}
    (e : RelEmbedding a (linkedModel t K b)) : Fin n ⊕ F → X :=
  Sum.elim b (linkedValue ∘ e)

theorem linkedAnchorMap_injective {a : RelStructure (LinkLanguage L (Fin n)) F}
    (e : RelEmbedding a (linkedModel t K b)) : Function.Injective (linkedAnchorMap e) := by
  apply Sum.elim_injective.mpr
  refine ⟨b.injective, (Subtype.val_injective.comp Subtype.val_injective).comp e.injective, ?_⟩
  intro i j h
  exact (e j).val.property ⟨i, h⟩

/-- The age of the linked realization set has actual free amalgamation.
Original amalgamation is over the named vertices together with the common
new base, and finite homogeneity fixes the named vertices in its realization. -/
theorem linked_age_shared_free (hh : FiniteEmbeddingHomogeneous K)
    (hfree : AgeSharedFree K) : AgeSharedFree (linkedModel t K b) := by
  classical
  intro B Y Z _ _ _ BL BR hbase hBL hBR
  obtain ⟨e⟩ := hBL
  obtain ⟨f⟩ := hBR
  let phiL : (Fin n ⊕ B) ⊕ Y → X := linkedAnchorMap e ∘ Equiv.sumAssoc (Fin n) B Y
  let phiR : (Fin n ⊕ B) ⊕ Z → X := linkedAnchorMap f ∘ Equiv.sumAssoc (Fin n) B Z
  let ML := K.pullback phiL
  let MR := K.pullback phiR
  let eL : RelEmbedding ML K := RelEmbedding.pullback K phiL
    ((linkedAnchorMap_injective e).comp (Equiv.sumAssoc (Fin n) B Y).injective)
  let eR : RelEmbedding MR K := RelEmbedding.pullback K phiR
    ((linkedAnchorMap_injective f).comp (Equiv.sumAssoc (Fin n) B Z).injective)
  have hLL : LinkedShared.leftModel ML = BL := by
    apply RelStructure.ext_rel
    intro r p v
    have heq : phiL ∘ anchoredTuple LinkedShared.anchorLeft LinkedShared.newLeft p v =
        linkTuple b p (Subtype.val ∘ e ∘ v) := by
      funext j
      change phiL (Sum.elim LinkedShared.anchorLeft (LinkedShared.newLeft ∘ v) (p.2.val j)) =
        Sum.elim b (linkedValue ∘ e ∘ v) (p.2.val j)
      cases p.2.val j with
      | inl a => rfl
      | inr i =>
        change phiL (LinkedShared.newLeft (v i)) = linkedValue (e (v i))
        cases v i <;> rfl
    change K.rel p.1.2 (phiL ∘ anchoredTuple LinkedShared.anchorLeft LinkedShared.newLeft p v) ↔ BL.rel p v
    rw [heq]
    exact (e.map_rel p v).symm
  have hRR : LinkedShared.rightModel MR = BR := by
    apply RelStructure.ext_rel
    intro r p v
    have heq : phiR ∘ anchoredTuple LinkedShared.anchorRight LinkedShared.newRight p v =
        linkTuple b p (Subtype.val ∘ f ∘ v) := by
      funext j
      change phiR (Sum.elim LinkedShared.anchorRight (LinkedShared.newRight ∘ v) (p.2.val j)) =
        Sum.elim b (linkedValue ∘ f ∘ v) (p.2.val j)
      cases p.2.val j with
      | inl a => rfl
      | inr i =>
        change phiR (LinkedShared.newRight (v i)) = linkedValue (f (v i))
        cases v i <;> rfl
    change K.rel p.1.2 (phiR ∘ anchoredTuple LinkedShared.anchorRight LinkedShared.newRight p v) ↔ BR.rel p v
    rw [heq]
    exact (f.map_rel p v).symm
  have hlinks : (linkModel b).pullback (Subtype.val ∘ e ∘ Sum.inl) =
      (linkModel b).pullback (Subtype.val ∘ f ∘ Sum.inl) := by
    exact (congrArg (fun a => a.pullback Sum.inl) e.pullback_eq).trans
      (hbase.trans (congrArg (fun a => a.pullback Sum.inl) f.pullback_eq).symm)
  have hactual : ML.pullback Sum.inl = MR.pullback Sum.inl := by
    have hfunL : phiL ∘ Sum.inl = Sum.elim b (linkedValue ∘ e ∘ Sum.inl) := by
      funext z
      cases z <;> rfl
    have hfunR : phiR ∘ Sum.inl = Sum.elim b (linkedValue ∘ f ∘ Sum.inl) := by
      funext z
      cases z <;> rfl
    dsimp only [ML, MR]
    rw [RelStructure.pullback_comp, RelStructure.pullback_comp, hfunL, hfunR]
    exact link_faithfulness b (Subtype.val ∘ e ∘ Sum.inl) (Subtype.val ∘ f ∘ Sum.inl) hlinks
  let W := SharedBaseAmalgam.model ML MR
  let lW := SharedBaseAmalgam.leftEmbedding ML MR hactual
  let rW := SharedBaseAmalgam.rightEmbedding ML MR hactual
  let anchorL : RelEmbedding (t.pullback Sum.inl) ML := {
    toFun := LinkedShared.anchorLeft
    injective := Sum.inl_injective.comp Sum.inl_injective
    map_rel := fun R v => b.map_rel R v }
  let anchorR : RelEmbedding (t.pullback Sum.inl) MR := {
    toFun := LinkedShared.anchorRight
    injective := Sum.inl_injective.comp Sum.inl_injective
    map_rel := fun R v => b.map_rel R v }
  let anchorW := lW.comp anchorL
  have hW : Nonempty (RelEmbedding W K) := hfree (Fin n ⊕ B) Y Z ML MR hactual ⟨eL⟩ ⟨eR⟩
  obtain ⟨v, hv⟩ := finite_age_extension hh anchorW b hW
  have hfix : ∀ a, v (LinkedShared.anchorWhole a) = b a := hv
  have hleftpoints : ∀ z : B ⊕ Y,
      LinkedShared.newWhole (SharedBaseAmalgam.left z) ∈ Realizations t W anchorW := by
    intro z
    have hz : eL (LinkedShared.newLeft z) ∈ Realizations t K b := by
      have heq : eL (LinkedShared.newLeft z) = linkedValue (e z) := by cases z <;> rfl
      rw [heq]
      exact (e z).property
    obtain ⟨p, hp, hs⟩ := realization_lifts_into_structure eL anchorL (fun _ => rfl)
      (LinkedShared.newLeft z) hz
    have heq : lW (LinkedShared.newLeft z) = LinkedShared.newWhole (SharedBaseAmalgam.left z) := by
      cases z <;> rfl
    exact ⟨lW.comp p, fun a => congrArg lW (hp a), (congrArg lW hs).trans heq⟩
  have hrightpoints : ∀ z : B ⊕ Z,
      LinkedShared.newWhole (SharedBaseAmalgam.right z) ∈ Realizations t W anchorW := by
    intro z
    have hz : eR (LinkedShared.newRight z) ∈ Realizations t K b := by
      have heq : eR (LinkedShared.newRight z) = linkedValue (f z) := by cases z <;> rfl
      rw [heq]
      exact (f z).property
    obtain ⟨p, hp, hs⟩ := realization_lifts_into_structure eR anchorR (fun _ => rfl)
      (LinkedShared.newRight z) hz
    have heq : rW (LinkedShared.newRight z) = LinkedShared.newWhole (SharedBaseAmalgam.right z) := by
      cases z <;> rfl
    exact ⟨rW.comp p, fun a => congrArg rW (hp a), (congrArg rW hs).trans heq⟩
  have hwholepoints : ∀ z : B ⊕ (Y ⊕ Z),
      v (LinkedShared.newWhole z) ∈ Realizations t K b := by
    intro z
    have hz : LinkedShared.newWhole z ∈ Realizations t W anchorW := by
      cases z with
      | inl z => exact hleftpoints (Sum.inl z)
      | inr z =>
        cases z with
        | inl z => exact hleftpoints (Sum.inr z)
        | inr z => exact hrightpoints (Sum.inr z)
    obtain ⟨p, hp, hs⟩ := hz
    exact ⟨v.comp p, fun a => (congrArg v (hp a)).trans (hv a), congrArg v hs⟩
  let new : B ⊕ (Y ⊕ Z) → LinkedVertices t K b := fun z =>
    ⟨⟨v (LinkedShared.newWhole z), realizes_outside_boundary (hwholepoints z)⟩, hwholepoints z⟩
  have htable := LinkedShared.linked_shared_free ML MR
  rw [hLL, hRR] at htable
  refine ⟨{
    toFun := new
    injective := by
      intro z w h
      have heq := v.injective (congrArg linkedValue h)
      exact (Sum.map_injective.mpr ⟨Sum.inr_injective, Function.injective_id⟩) heq
    map_rel := by
      intro r p u
      have hsrc := congrArg (fun a => a.rel p u) htable
      change W.rel p.1.2 (anchoredTuple LinkedShared.anchorWhole LinkedShared.newWhole p u) =
        (SharedBaseAmalgam.model BL BR).rel p u at hsrc
      have hmap := v.map_rel p.1.2 (anchoredTuple LinkedShared.anchorWhole LinkedShared.newWhole p u)
      have heq : v ∘ anchoredTuple LinkedShared.anchorWhole LinkedShared.newWhole p u =
          linkTuple b p (Subtype.val ∘ new ∘ u) := by
        funext j
        change v (Sum.elim LinkedShared.anchorWhole (LinkedShared.newWhole ∘ u) (p.2.val j)) =
          Sum.elim b (linkedValue ∘ new ∘ u) (p.2.val j)
        cases p.2.val j with
        | inl a => exact hfix a
        | inr i => rfl
      exact (Iff.of_eq hsrc).symm.trans (hmap.trans (Iff.of_eq (congrArg (K.rel p.1.2) heq))) }⟩

end CombinedRamsey.Negative
