import RelationalRamsey632.Milliken.SourceFrames
import RelationalRamsey632.Source.FiniteValuations
import RelationalRamsey632.Source.FiniteCoreEquality

/-! Every actual finite source vector has a genuine infinite abstract
strong-frame prefix representation, with exactly its active core. -/

namespace RelationalRamsey632

open Generic3Ramsey.SourceTrees
open Generic3Ramsey.SourceTrees.FiniteLevelTree
open Source
open Milliken

namespace Source.FiniteStrongVector

variable {A : ℕ → Type} [∀ j, Fintype (A j)] [∀ j, Nonempty (A j)]
    {e : ℕ → ℕ} {he : StrictMono e} {h : ℕ}
    (V : FiniteStrongVector A e he h)

noncomputable def finiteNodes (i n : ℕ) : Finset (Node A i) := by
  classical
  exact (Finset.univ.filter (fun p : Level A i (e n) => p ∈ V.nodes i n)).image
    (fun p => Node.mk (e n) p)

omit [∀ j, Nonempty (A j)] in
theorem mem_finiteNodes (i n : ℕ) (t : Node A i) :
    t ∈ V.finiteNodes i n ↔ ∃ p ∈ V.nodes i n, Node.mk (e n) p = t := by
  classical
  simp only [finiteNodes, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def abstractPrefix (i : Fin h) :
    FiniteStrongPrefix (coordinateTree (A := A) i.val) e h where
  index_strictMono := he
  nodes := V.finiteNodes i.val
  root := Node.mk (e 0) (V.root i.val i.isLt)
  nodes_zero := by
    classical
    ext t
    rw [V.mem_finiteNodes, Finset.mem_singleton]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact congrArg (Node.mk (e 0)) (V.root_unique i.val i.isLt p hp)
    · rintro rfl
      exact ⟨V.root i.val i.isLt, V.root_mem i.val i.isLt, rfl⟩
  nodes_subset n _ := by
    rintro t ht
    obtain ⟨p, hp, rfl⟩ := (V.mem_finiteNodes i.val n t).mp ht
    exact (mem_finiteNodeLevel i.val (e n) _).mpr rfl
  parent n hn w hw := by
    obtain ⟨q, hq, rfl⟩ := (V.mem_finiteNodes i.val (n + 1) w).mp hw
    let p := q.restrict (he.monotone (Nat.le_succ n))
    have hp := V.parent i.val i.isLt n hn q hq
    exact ⟨Node.mk (e n) p,
      (V.mem_finiteNodes i.val n _).mpr ⟨p, hp, rfl⟩,
      he.monotone (Nat.le_succ n), rfl⟩
  successor n hn u hu v hv huv := by
    obtain ⟨p, hp, rfl⟩ := (V.mem_finiteNodes i.val n u).mp hu
    have hvheight := (mem_finiteNodeLevel i.val (e n + 1) v).mp hv
    cases v with
    | mk a t =>
      dsimp only [Node.height] at hvheight
      subst a
      obtain ⟨hle, hpred⟩ := huv
      have hpTable : t.restrict (Nat.le_succ (e n)) = p :=
        Node.mk_injective (e n) hpred
      let a := t.singleton (Nat.lt_succ_self (e n))
      let s := t.slice (Nat.lt_succ_self (e n))
      have hbranch : Level.extend p a s = t := by
        have hb := Level.reconstruct_step t (Nat.lt_succ_self (e n))
        simpa only [Level.restrict_refl, hpTable] using hb
      obtain ⟨q, ⟨hq, hcone⟩, huniq⟩ := V.successor i.val i.isLt n hn p hp a s
      refine ⟨Node.mk (e (n + 1)) q, ⟨?_, ?_⟩, ?_⟩
      · exact (V.mem_finiteNodes i.val (n + 1) _).mpr ⟨q, hq, rfl⟩
      · exact ⟨Nat.succ_le_of_lt (he (Nat.lt_succ_self n)),
          congrArg (Node.mk (e n + 1)) (hcone.trans hbranch)⟩
      · intro w hw
        obtain ⟨r, hr, rfl⟩ := (V.mem_finiteNodes i.val (n + 1) w).mp hw.1
        obtain ⟨hrle, hrestrict⟩ := hw.2
        have hrcone : r.restrict (Nat.succ_le_of_lt (he (Nat.lt_succ_self n))) =
            Level.extend p a s := (Node.mk_injective (e n + 1) hrestrict).trans hbranch.symm
        exact congrArg (Node.mk (e (n + 1))) (huniq r ⟨hr, hrcone⟩)

noncomputable def abstractExtension (hh : 0 < h) :
    SynchronizedFrame (fun i : Fin h => coordinateTree (A := A) i.val) where
  index := e
  index_strictMono := he
  frames i := (V.abstractPrefix i).extend hh
  frame_index _ := rfl

theorem abstractExtension_core (hh : 0 < h) (i n : Fin h) :
    (((V.abstractExtension hh).core h i n : Finset (Node A i.val)) : Set (Node A i.val)) =
      V.core i n := by
  change (((V.abstractPrefix i).extend hh).nodes n.val : Set (Node A i.val)) = _
  rw [FiniteStrongPrefix.extend_initial _ hh n.val n.isLt]
  ext t
  change t ∈ V.finiteNodes i.val n.val ↔ t ∈ V.core i n
  rw [V.mem_finiteNodes]
  constructor
  · rintro ⟨p, hp, heq⟩
    exact ⟨p, hp, heq.symm⟩
  · rintro ⟨p, hp, heq⟩
    exact ⟨p, hp, heq.symm⟩

end Source.FiniteStrongVector

end RelationalRamsey632
