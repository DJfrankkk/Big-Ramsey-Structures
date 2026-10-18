import CombinedRamsey.Negative.PersistenceAmalgam
import CombinedRamsey.Negative.Compactness

namespace CombinedRamsey.Negative

open RelationalRamsey632

variable {L : Language}

/-- The transitive-case finite-size induction in the paper, using actual
free point amalgams, supported greedy embeddings, and extension over their
whole old base. No weak-indivisibility conclusion is a hypothesis. -/
theorem weaklyIndivisible_of_free_age (K : RelStructure L ℕ)
    (hh : FiniteEmbeddingHomogeneous K)
    (hf : AgeFreeAmalgamation K) (hp : FreePosition K)
    (hs : TransitiveSingletons K) : WeaklyIndivisible K := by
  classical
  have hind : ∀ d (D : RelStructure L (Fin d)), InAgeOn K Set.univ D →
      ∀ R : Set ℕ, ¬ InAgeOn K R D →
        ∃ f : RelEmbedding K K, ∀ x, f x ∉ R := by
    intro d
    induction d with
    | zero =>
      intro D hD R hn
      obtain ⟨e, _⟩ := hD
      exact False.elim (hn ⟨e, fun i => Fin.elim0 i⟩)
    | succ d ih =>
      intro D hD R hn
      by_contra hno
      obtain ⟨n, old, hhalt⟩ := greedy_halt K Rᶜ hno
      obtain ⟨g, hdis, hcross⟩ := hp n old.val
      let Dold := D.pullback Fin.castSucc
      let R' : Set ℕ := {x | g x ∈ R}
      obtain ⟨uD, _⟩ := hD
      have hDold : InAgeOn K Set.univ Dold :=
        ⟨uD.comp (RelEmbedding.pullback D Fin.castSucc (Fin.castSucc_injective d)),
          fun _ => Set.mem_univ _⟩
      have hred : InAgeOn K R' Dold := by
        by_contra hred
        obtain ⟨f, hf⟩ := ih Dold hDold R' hred
        exact hno ⟨g.comp f, hf⟩
      obtain ⟨u, hu⟩ := hred
      let red := g.comp u
      have hredsupport : ∀ a, red a ∈ R := hu
      let B := initialStructure K (n + 1)
      have hepoint := congrArg (fun z => z.pullback (fun _ : Fin 1 => Fin.last d)) uD.pullback_eq
      have hpoint : B.pullback (fun _ : Fin 1 => Fin.last n) =
          D.pullback (fun _ : Fin 1 => Fin.last d) :=
        (hs n (uD (Fin.last d))).trans hepoint
      let W := PointAmalgam.model B D hpoint
      have hW : Nonempty (RelEmbedding W K) := hf (Fin 1) (Fin (n + 1)) (Fin (d + 1))
        (B.pullback (fun _ : Fin 1 => Fin.last n)) B D
        (PointAmalgam.leftPoint B) (PointAmalgam.rightPoint B D hpoint)
        ⟨RelEmbedding.pullback K Fin.val Fin.val_injective⟩ ⟨uD⟩
      have hcross' : ∀ r (T : L.Rel r) (t : Fin r → ℕ),
          (∀ k, t k ∈ Set.range old.val ∪ Set.range red) → ∀ (i j : Fin r),
          t i ∈ Set.range old.val → t j ∈ Set.range red → ¬ K.rel T t := by
        intro r T t hguard i j hi hj
        have hguard' : ∀ k, t k ∈ Set.range old.val ∪ Set.range g := by
          intro k
          rcases hguard k with hk | hk
          · exact Or.inl hk
          · obtain ⟨a, ha⟩ := hk
            exact Or.inr ⟨u a, ha⟩
        obtain ⟨a, ha⟩ := hj
        exact hcross r T t hguard' i j hi ⟨u a, ha⟩
      let oldBase := freeUnionEmbedding old.val red
        (fun a b => hdis a (u b)) hcross'
      obtain ⟨v, hv⟩ := finite_age_extension hh (PointAmalgam.oldEmbedding B D hpoint) oldBase hW
      let extend := v.comp (PointAmalgam.left B D hpoint)
      have heold : ∀ a : Fin n, extend a.castSucc = old.val a := fun a => hv (Sum.inl a)
      have hz : extend (Fin.last n) ∈ R := by
        by_contra hnot
        have hb : ∀ a : Fin (n + 1), extend a ∈ Rᶜ := by
          intro a
          refine Fin.lastCases ?_ (fun b => ?_) a
          · exact hnot
          · rw [heold]
            exact old.property b
        exact hhalt ⟨⟨extend, hb⟩, heold⟩
      let intoD := v.comp (PointAmalgam.right B D hpoint)
      have hzD : intoD (Fin.last d) ∈ R := by
        have heq := congrArg v (PointAmalgam.last_eq B D hpoint)
        exact heq ▸ hz
      have hDred : InAgeOn K R D := by
        refine ⟨intoD, ?_⟩
        intro a
        refine Fin.lastCases hzD (fun b => ?_) a
        have he : intoD b.castSucc = red b := hv (Sum.inr b)
        exact he ▸ hredsupport b
      exact hn hDred
  intro R hR
  have hmiss : ∃ (n : ℕ) (D : RelStructure L (Fin n)),
      InAgeOn K Set.univ D ∧ ¬ InAgeOn K R D := by
    unfold SameAgeOn at hR
    push Not at hR
    obtain ⟨n, D, hD⟩ := hR
    rcases hD with hD | hD
    · exact ⟨n, D, hD⟩
    · exact False.elim (hD.1 (inAgeOn_mono (fun _ _ => Set.mem_univ _) hD.2))
  obtain ⟨n, D, hD, hn⟩ := hmiss
  exact hind n D hD R hn

theorem transitive_free_age_indivisible (K : RelStructure L ℕ)
    (hh : FiniteEmbeddingHomogeneous K)
    (hf : AgeFreeAmalgamation K) (hp : FreePosition K)
    (hs : TransitiveSingletons K) : AgeIndivisibleOn K Set.univ :=
  ageIndivisible_of_weaklyIndivisible (weaklyIndivisible_of_free_age K hh hf hp hs)

end CombinedRamsey.Negative
