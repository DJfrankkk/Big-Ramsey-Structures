import RelationalRamsey632.Milliken.SourceFinitePrefixes
import RelationalRamsey632.Source.RamseyReduction
import RelationalRamsey632.Milliken.HeightTheorem

/-! The finite-dimensional generic tree theorem specializes to every
actual source finite-vector core. Finite prefix realizability and passive
coordinate completion are constructed, rather than assumed. -/

namespace RelationalRamsey632.Milliken

open Generic3Ramsey.SourceTrees
open Generic3Ramsey.SourceTrees.FiniteLevelTree
open Source

variable {A : ℕ → Type} [∀ j, Fintype (A j)] [∀ j, Nonempty (A j)]

abbrev SourceTreeCore (h : ℕ) :=
  RealizedTreeCore (fun i : Fin h => coordinateTree (A := A) i.val) h

noncomputable def treeCoreToSource {h : ℕ} (C : SourceTreeCore (A := A) h) :
    RealizedVectorCore A h :=
  let G := Classical.choose C.property
  ((sourceVectorCompletion G).finitePrefix h).realizedCore

theorem treeCoreToSource_coe {h : ℕ} (C : SourceTreeCore (A := A) h) (i n : Fin h) :
    (treeCoreToSource C).val i n = (C.val i n : Set (Node A i.val)) := by
  let G := Classical.choose C.property
  have hG : G.core h = C.val := Classical.choose_spec C.property
  let V := (sourceVectorCompletion G).finitePrefix h
  ext t
  change t ∈ V.core i n ↔ t ∈ C.val i n
  have hcore : G.core h i n = C.val i n := congrFun (congrFun hG i) n
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hnode : Node.mk (G.index n.val) p ∈ (G.frames i).nodes n.val :=
      (sourceVectorCompletion_active G i n.val p).mp hp
    rw [← hcore]
    exact hnode
  · intro ht
    have hnode : t ∈ (G.frames i).nodes n.val := by
      rw [← hcore] at ht
      exact ht
    have hlevel := (G.frames i).nodes_subset n.val hnode
    rw [G.frame_index i] at hlevel
    have hheight := (mem_finiteNodeLevel i.val (G.index n.val) t).mp hlevel
    cases t with
    | mk a p =>
      dsimp only [Node.height] at hheight
      subst a
      exact ⟨p, (sourceVectorCompletion_active G i n.val p).mpr hnode, rfl⟩

noncomputable def sourceCoreToTree {h : ℕ} (C : RealizedVectorCore A h) (hh : 0 < h) :
    SourceTreeCore (A := A) h :=
  let F := Classical.choose C.property
  (F.vector.abstractExtension hh).realizedCore h

theorem sourceCoreToTree_coe {h : ℕ} (C : RealizedVectorCore A h) (hh : 0 < h)
    (i n : Fin h) :
    ((sourceCoreToTree C hh).val i n : Set (Node A i.val)) = C.val i n := by
  let F := Classical.choose C.property
  have hF : F.vector.core = C.val := Classical.choose_spec C.property
  change (((F.vector.abstractExtension hh).core h i n : Finset (Node A i.val)) :
    Set (Node A i.val)) = C.val i n
  exact (F.vector.abstractExtension_core hh i n).trans (congrFun (congrFun hF i) n)

theorem treeCoreToSource_sourceCoreToTree {h : ℕ}
    (C : RealizedVectorCore A h) (hh : 0 < h) :
    treeCoreToSource (sourceCoreToTree C hh) = C := by
  apply Subtype.ext
  funext i n
  exact (treeCoreToSource_coe (sourceCoreToTree C hh) i n).trans
    (sourceCoreToTree_coe C hh i n)

/-- No source occurrence is omitted: every actual finite source V appears
in the generic core theorem through its explicit infinite prefix extension. -/
theorem vectorMilliken_of_height_theorems
    (hHeight : ∀ h : ℕ, 0 < h → ∀ (D : Type) [Fintype D],
      MillikenHeight (fun i : Fin h => coordinateTree (A := A) i.val) h D) :
    VectorMilliken A := by
  classical
  intro h hh D _ c
  let d : SourceTreeCore (A := A) h → D := fun C => c (treeCoreToSource C)
  obtain ⟨G, color, hG⟩ := hHeight h hh D d
  let S := sourceVectorCompletion G
  refine ⟨G.index, G.index_strictMono, S, color, ?_⟩
  intro l hl V hrelative
  let C := sourceCoreToTree V.realizedCore hh
  have hC : RelativeCore (fun i : Fin h => coordinateTree (A := A) i.val) G C := by
    refine ⟨l, hl, ?_⟩
    intro i n t ht
    have hV : t ∈ V.core i n := by
      have heq := sourceCoreToTree_coe V.realizedCore hh i n
      change (C.val i n : Set (Node A i.val)) = V.core i n at heq
      exact heq ▸ ht
    obtain ⟨p, hp, rfl⟩ := hV
    have hpS : p ∈ S.nodes i.val (l n.val) :=
      hrelative i.val n.val i.isLt n.isLt hp
    exact (sourceVectorCompletion_active G i (l n.val) p).mp hpS
  have h := hG C hC
  change c (treeCoreToSource C) = color at h
  rw [treeCoreToSource_sourceCoreToTree] at h
  exact h

/-- Unconditional source vector Milliken, supplied by the internally
proved finite-dimensional arbitrary-height tree theorem. -/
theorem source_vector_milliken : VectorMilliken A := by
  apply vectorMilliken_of_height_theorems
  intro h _ D _
  exact vector_milliken_height (fun i : Fin h => coordinateTree (A := A) i.val) h D

end RelationalRamsey632.Milliken
