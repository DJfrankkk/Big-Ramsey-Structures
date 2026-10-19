import RelationalRamsey632.Milliken.HeightFrames
import Mathlib.Data.Fintype.Sigma

/-! Finite strong-core obligations form a countable collection. -/

namespace RelationalRamsey632.Milliken

open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

variable {I : Type} {α : I → Type} [∀ i, DecidableEq (α i)]
variable {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))

def treeNodeValue {V : Type} [DecidableEq V] {P : V → V → Prop}
    (S : FiniteLevelTree V P) (x : S.TreeNode) : V := x.val

def frameNodeCode (F : SynchronizedFrame T) (i : I) (n : ℕ)
    (x : (F.frames i).nodes n) : (T i).TreeNode :=
  ⟨x.val, (F.frames i).index n, (F.frames i).nodes_subset n x.property⟩

noncomputable def frameLevelCode (F : SynchronizedFrame T) (i : I) (n : ℕ) :
    Finset (T i).TreeNode := by
  classical
  exact ((F.frames i).nodes n).attach.image (frameNodeCode T F i n)

theorem frameLevelCode_decode (F : SynchronizedFrame T) (i : I) (n : ℕ) :
    (frameLevelCode T F i n).image (treeNodeValue (T i)) = (F.frames i).nodes n := by
  classical
  rw [frameLevelCode, Finset.image_image]
  simp [frameNodeCode, treeNodeValue, Function.comp_def]

noncomputable def finiteCoreCode {h : ℕ} (C : RealizedTreeCore T h) :
    (i : I) → Fin h → Finset (T i).TreeNode :=
  fun i n => frameLevelCode T (Classical.choose C.property) i n.val

theorem finiteCoreCode_decode {h : ℕ} (C : RealizedTreeCore T h) (i : I) (n : Fin h) :
    (finiteCoreCode T C i n).image (treeNodeValue (T i)) = C.val i n := by
  rw [finiteCoreCode, frameLevelCode_decode]
  exact congrFun (congrFun (Classical.choose_spec C.property) i) n

theorem finiteCoreCode_injective (h : ℕ) :
    Function.Injective (finiteCoreCode T (h := h)) := by
  intro C D he
  apply Subtype.ext
  funext i n
  have hc := congrArg (fun f : (i : I) → Fin h → Finset (T i).TreeNode =>
    (f i n).image (treeNodeValue (T i))) he
  simpa only [finiteCoreCode_decode] using hc

instance realizedTreeCoreCountable [Fintype I] (h : ℕ) : Countable (RealizedTreeCore T h) :=
  (finiteCoreCode_injective T h).countable

end RelationalRamsey632.Milliken
