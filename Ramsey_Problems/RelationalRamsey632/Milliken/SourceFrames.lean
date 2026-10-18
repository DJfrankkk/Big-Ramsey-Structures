import RelationalRamsey632.Milliken.SourceTrees
import RelationalRamsey632.Milliken.PrefixExtension
import RelationalRamsey632.Milliken.HeightFrames
import RelationalRamsey632.Source.CompressionConsequences
import RelationalRamsey632.Source.Valuations

/-! Abstract strong frames and literal all-arity source vector coordinates. -/

namespace RelationalRamsey632.Milliken

open Generic3Ramsey.SourceTrees
open Generic3Ramsey.SourceTrees.FiniteLevelTree
open Source

variable {A : ℕ → Type} [∀ j, Fintype (A j)] [∀ j, Nonempty (A j)]
    {e : ℕ → ℕ} (he : StrictMono e)
    (F : ∀ i, (coordinateTree (A := A) i).StrongFrame)
    (hF : ∀ i, (F i).index = e)

include hF in
theorem source_frame_height (i n : ℕ) (t : Node A i)
    (ht : t ∈ (F i).nodes n) : t.height = e n := by
  have hmem := (F i).nodes_subset n ht
  rw [hF] at hmem
  exact (mem_finiteNodeLevel i (e n) t).mp hmem

noncomputable def sourceFrameRoot (i : ℕ) : Level A i (e 0) :=
  cast (congrArg (Level A i) (source_frame_height F hF i 0 (F i).root
    (by rw [(F i).nodes_zero]; exact Finset.mem_singleton_self _))) (F i).root.table

theorem sourceFrameRoot_node (i : ℕ) :
    (Node.mk (e 0) (sourceFrameRoot F hF i) : Node A i) = (F i).root := by
  unfold sourceFrameRoot
  exact node_mk_cast
    (source_frame_height F hF i 0 (F i).root
      (by rw [(F i).nodes_zero]; exact Finset.mem_singleton_self _))
    (F i).root.table

noncomputable def framesToSource : StrongVector A e he where
  nodes i n := {p | Node.mk (e n) p ∈ (F i).nodes n}
  root := sourceFrameRoot F hF
  root_mem i := by
    change Node.mk (e 0) (sourceFrameRoot F hF i) ∈ (F i).nodes 0
    rw [sourceFrameRoot_node]
    rw [(F i).nodes_zero]
    exact Finset.mem_singleton_self _
  root_unique i p hp := by
    change Node.mk (e 0) p ∈ (F i).nodes 0 at hp
    rw [(F i).nodes_zero] at hp
    exact Node.mk_injective (e 0)
      ((Finset.mem_singleton.mp hp).trans (sourceFrameRoot_node F hF i).symm)
  successor i n p hp a v := by
    let branch : Node A i := ⟨e n + 1, Level.extend p a v⟩
    have hb : branch ∈ (coordinateTree (A := A) i).nodes ((F i).index n + 1) := by
      rw [hF]
      exact (mem_finiteNodeLevel i (e n + 1) branch).mpr rfl
    have hpb : Node.Prefix (Node.mk (e n) p) branch := by
      refine ⟨Nat.le_succ _, ?_⟩
      exact congrArg (fun u : Level A i (e n) => (Node.mk (e n) u : Node A i))
        (Level.extend_restrict p a v)
    obtain ⟨w, ⟨hw, hbw⟩, huniq⟩ := (F i).successor n (Node.mk (e n) p) hp branch hb hpb
    have hwh := source_frame_height F hF i (n + 1) w hw
    cases w with
    | mk w q =>
      dsimp only [Node.height] at hwh
      subst w
      obtain ⟨hle, hcone⟩ := hbw
      have hq : q.restrict (Nat.succ_le_of_lt (he (Nat.lt_succ_self n))) =
          Level.extend p a v := Node.mk_injective (e n + 1) hcone
      refine ⟨q, ⟨hw, hq⟩, ?_⟩
      intro r hr
      have hrpre : Node.Prefix branch (Node.mk (e (n + 1)) r) :=
        ⟨Nat.succ_le_of_lt (he (Nat.lt_succ_self n)),
          congrArg (fun u : Level A i (e n + 1) => (Node.mk (e n + 1) u : Node A i)) hr.2⟩
      exact Node.mk_injective (e (n + 1)) (huniq (Node.mk (e (n + 1)) r) ⟨hr.1, hrpre⟩)
  parent i n q hq := by
    obtain ⟨p, hp, hpq⟩ := (F i).parent n (Node.mk (e (n + 1)) q) hq
    have hph := source_frame_height F hF i n p hp
    cases p with
    | mk a p =>
      dsimp only [Node.height] at hph
      subst a
      obtain ⟨hle, hrestrict⟩ := hpq
      change Node.mk (e n) (q.restrict (he.monotone (Nat.le_succ n))) ∈ (F i).nodes n
      have hpred : Node.mk (e n) (q.restrict (he.monotone (Nat.le_succ n))) =
          Node.mk (e n) p := hrestrict
      exact hpred.symm ▸ hp

theorem framesToSource_nodes (i n : ℕ) (p : Level A i (e n)) :
    p ∈ (framesToSource he F hF).nodes i n ↔ Node.mk (e n) p ∈ (F i).nodes n := Iff.rfl

variable {h : ℕ}
    (G : SynchronizedFrame (fun i : Fin h => coordinateTree (A := A) i.val))

noncomputable def completeSourceFrames (i : ℕ) :
    (coordinateTree (A := A) i).StrongFrame := by
  classical
  exact if hi : i < h then G.frames ⟨i, hi⟩
    else LevelSelection.frame (coordinateTree (A := A) i) G.index G.index_strictMono

theorem completeSourceFrames_index (i : ℕ) :
    (completeSourceFrames G i).index = G.index := by
  classical
  by_cases hi : i < h
  · simpa only [completeSourceFrames, dif_pos hi] using G.frame_index ⟨i, hi⟩
  · simp only [completeSourceFrames, dif_neg hi, LevelSelection.frame_index]

noncomputable def sourceVectorCompletion : StrongVector A G.index G.index_strictMono :=
  framesToSource G.index_strictMono (completeSourceFrames G) (completeSourceFrames_index G)

theorem sourceVectorCompletion_active (i : Fin h) (n : ℕ)
    (p : Level A i.val (G.index n)) :
    p ∈ (sourceVectorCompletion G).nodes i.val n ↔ Node.mk (G.index n) p ∈ (G.frames i).nodes n := by
  classical
  change Node.mk (G.index n) p ∈ (completeSourceFrames G i.val).nodes n ↔ _
  simp only [completeSourceFrames, dif_pos i.isLt]

end RelationalRamsey632.Milliken
