import RelationalRamsey632.Milliken.HeightCoreTransport
import RelationalRamsey632.Milliken.HeightOne

/-! The finite-height induction step after genuine last-extension canonization. -/

namespace RelationalRamsey632.Milliken

open Generic3Ramsey.SourceTrees
open Generic3Ramsey.SourceTrees.FiniteLevelTree

variable {I : Type} {α : I → Type} [∀ i, DecidableEq (α i)]
variable {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))

theorem height_succ_of_factorization {h : ℕ} {K : Type} (hh : 0 < h)
    (hIH : ∀ S : ∀ i, FiniteLevelTree (α i) (R i), MillikenHeight S h K)
    (hFactor : HeightFactorization T h K) : MillikenHeight T (h + 1) K := by
  intro c
  obtain ⟨F, d, hF⟩ := hFactor c
  let S := fun i => (F.frames i).toTree
  obtain ⟨G, color, hG⟩ := hIH S (fun D => d (liftCore T F D))
  refine ⟨F.comp G, color, ?_⟩
  intro C hC
  let P := prefixCore T C
  have hP : RelativeCore T (F.comp G) P := relative_prefix T _ C hC
  obtain ⟨D, hD⟩ := realize_relative_lift T F hh P (relative_core_comp T F G P hP)
  have hDG : RelativeCore S G D := by
    apply relative_composite_lift T F G D
    rw [hD]
    exact hP
  have hd := hG D hDG
  change d (liftCore T F D) = color at hd
  rw [hD] at hd
  exact (hF C (relative_core_comp T F G C hC)).trans hd

end RelationalRamsey632.Milliken
