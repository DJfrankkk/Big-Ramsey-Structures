import RelationalRamsey632.Milliken.HeightCanonicalAPI

/-! The exact finite family of h-cores ending at a protected stage. -/

namespace RelationalRamsey632.Milliken

open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

variable {I : Type} [Fintype I] {α : I → Type} [∀ i, DecidableEq (α i)]
variable {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))

omit [Fintype I] in
theorem endedCore_code_bound {h : ℕ} (hh : 0 < h) (F : SynchronizedFrame T)
    (k : ℕ) (P : RealizedTreeCore T h) (hP : EndsAt T F k P) (i : I) (n : Fin h) :
    finiteCoreCode T P i n ⊆ boundedNodes (T i) (F.index k) := by
  obtain ⟨l, hl, hlast, hsub⟩ := hP
  intro u hu
  have hup : treeNodeValue (T i) u ∈ P.val i n := by
    rw [← finiteCoreCode_decode T P i n]
    exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  have hlevel := (F.frames i).nodes_subset (l n.val) (hsub i n hup)
  have hheight : (T i).nodeHeight u = (F.frames i).index (l n.val) :=
    (T i).nodeHeight_eq u _ hlevel
  apply (mem_boundedNodes (T i) (F.index k) u).mpr
  rw [hheight, F.frame_index]
  apply F.index_strictMono.monotone
  have hn : n.val ≤ h - 1 := by omega
  exact hlast ▸ hl.monotone hn

theorem endedCore_finite {h : ℕ} (hh : 0 < h) (F : SynchronizedFrame T) (k : ℕ) :
    Finite {P : RealizedTreeCore T h // EndsAt T F k P} := by
  classical
  let Code := (i : I) → Fin h →
    {s : Finset (T i).TreeNode // s ⊆ boundedNodes (T i) (F.index k)}
  letI : ∀ i, Fintype {s : Finset (T i).TreeNode // s ⊆ boundedNodes (T i) (F.index k)} :=
    fun i => Fintype.ofFinset (boundedNodes (T i) (F.index k)).powerset
      (fun _ => Finset.mem_powerset)
  let f : {P : RealizedTreeCore T h // EndsAt T F k P} → Code :=
    fun P i n => ⟨finiteCoreCode T P.val i n, endedCore_code_bound T hh F k P.val P.property i n⟩
  apply Finite.of_injective f
  intro P Q he
  apply Subtype.ext
  apply finiteCoreCode_injective T h
  funext i n
  exact congrArg (fun x : {s : Finset (T i).TreeNode // s ⊆ boundedNodes (T i) (F.index k)} => x.val)
    (congrFun (congrFun he i) n)

end RelationalRamsey632.Milliken
