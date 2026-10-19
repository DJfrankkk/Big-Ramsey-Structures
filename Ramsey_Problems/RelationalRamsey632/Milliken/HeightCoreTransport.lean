import RelationalRamsey632.Milliken.HeightCanonicalAPI
import RelationalRamsey632.Milliken.RelativePrefixCompletion

/-! Finite strong cores transport exactly between a frame and its ambient trees. -/

namespace RelationalRamsey632.Milliken

open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

variable {I : Type} {α : I → Type} [∀ i, DecidableEq (α i)]
variable {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))

def liftCore (F : SynchronizedFrame T) {h : ℕ}
    (D : RealizedTreeCore (fun i => (F.frames i).toTree) h) : RealizedTreeCore T h :=
  ⟨D.val, by
    obtain ⟨G, hG⟩ := D.property
    exact ⟨F.comp G, hG⟩⟩

@[simp] theorem liftCore_value (F : SynchronizedFrame T) {h : ℕ}
    (D : RealizedTreeCore (fun i => (F.frames i).toTree) h) : (liftCore T F D).val = D.val := rfl

theorem lifted_core_relative (F : SynchronizedFrame T) {h : ℕ}
    (D : RealizedTreeCore (fun i => (F.frames i).toTree) h) :
    RelativeCore T F (liftCore T F D) := by
  obtain ⟨G, hG⟩ := D.property
  refine ⟨G.index, G.index_strictMono, ?_⟩
  intro i n
  change D.val i n ⊆ _
  rw [← hG]
  have hsub := (G.frames i).nodes_subset n.val
  rwa [G.frame_index] at hsub

theorem realize_relative_lift (F : SynchronizedFrame T) {h : ℕ}
    (hh : 0 < h) (C : RealizedTreeCore T h) (hC : RelativeCore T F C) :
    ∃ D : RealizedTreeCore (fun i => (F.frames i).toTree) h, liftCore T F D = C := by
  obtain ⟨D, hD⟩ := realize_relative_core T F C hh hC
  exact ⟨D, Subtype.ext hD⟩

theorem relative_composite_lift (F : SynchronizedFrame T)
    (G : SynchronizedFrame (fun i => (F.frames i).toTree)) {h : ℕ}
    (D : RealizedTreeCore (fun i => (F.frames i).toTree) h)
    (hD : RelativeCore T (F.comp G) (liftCore T F D)) :
    RelativeCore (fun i => (F.frames i).toTree) G D := hD

end RelationalRamsey632.Milliken
