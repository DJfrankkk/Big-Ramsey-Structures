import RelationalRamsey632.Milliken.HeightCountability

/-! Exact prefix and refinement interfaces for the height fusion. -/

namespace RelationalRamsey632.Milliken

open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

variable {I : Type} {α : I → Type} [∀ i, DecidableEq (α i)]
variable {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))

def prefixCore {h : ℕ} (C : RealizedTreeCore T (h + 1)) : RealizedTreeCore T h :=
  ⟨fun i n => C.val i n.castSucc, by
    obtain ⟨F, hF⟩ := C.property
    refine ⟨F, ?_⟩
    funext i n
    exact congrFun (congrFun hF i) n.castSucc⟩

@[simp] theorem prefixCore_apply {h : ℕ} (C : RealizedTreeCore T (h + 1)) (i : I) (n : Fin h) :
    (prefixCore T C).val i n = C.val i n.castSucc := rfl

theorem relative_prefix {h : ℕ} (F : SynchronizedFrame T) (C : RealizedTreeCore T (h + 1))
    (hC : RelativeCore T F C) : RelativeCore T F (prefixCore T C) := by
  obtain ⟨l, hl, hsub⟩ := hC
  exact ⟨l, hl, fun i n => hsub i n.castSucc⟩

structure FrameRefinement (F : SynchronizedFrame T) where
  frame : SynchronizedFrame T
  selector : ℕ → ℕ
  selector_strictMono : StrictMono selector
  index_eq : frame.index = F.index ∘ selector
  subset : ∀ i n, (frame.frames i).nodes n ⊆ (F.frames i).nodes (selector n)

namespace FrameRefinement

variable {T} {F : SynchronizedFrame T} (G : FrameRefinement T F)

def Preserves (k : ℕ) : Prop :=
  ∀ n, n ≤ k → G.selector n = n ∧ ∀ i, (G.frame.frames i).nodes n = (F.frames i).nodes n

def identity (F : SynchronizedFrame T) : FrameRefinement T F :=
  ⟨F, id, strictMono_id, rfl, fun _ _ => Finset.Subset.refl _⟩

theorem identity_preserves (F : SynchronizedFrame T) (k : ℕ) :
    (identity F).Preserves k := fun _ _ => ⟨rfl, fun _ => rfl⟩

theorem relative_mono {h : ℕ} (C : RealizedTreeCore T h)
    (hC : RelativeCore T G.frame C) : RelativeCore T F C := by
  obtain ⟨l, hl, hsub⟩ := hC
  exact ⟨G.selector ∘ l, G.selector_strictMono.comp hl,
    fun i n => (hsub i n).trans (G.subset i (l n.val))⟩

def trans (H : FrameRefinement T G.frame) : FrameRefinement T F where
  frame := H.frame
  selector := G.selector ∘ H.selector
  selector_strictMono := G.selector_strictMono.comp H.selector_strictMono
  index_eq := by rw [H.index_eq, G.index_eq]; rfl
  subset i n := (H.subset i n).trans (G.subset i (H.selector n))

end FrameRefinement

def EndsAt {h : ℕ} (F : SynchronizedFrame T) (k : ℕ) (P : RealizedTreeCore T h) : Prop :=
  ∃ l : ℕ → ℕ, StrictMono l ∧ l (h - 1) = k ∧
    ∀ i (n : Fin h), P.val i n ⊆ (F.frames i).nodes (l n.val)

def EndHomogeneous {h : ℕ} {K : Type} (c : RealizedTreeCore T (h + 1) → K)
    (F : SynchronizedFrame T) (P : RealizedTreeCore T h) : Prop :=
  ∃ color : K, ∀ C : RealizedTreeCore T (h + 1),
    RelativeCore T F C → prefixCore T C = P → c C = color

def CanonicalStep {h : ℕ} {K : Type} (c : RealizedTreeCore T (h + 1) → K) : Prop :=
  ∀ F : SynchronizedFrame T, ∀ k : ℕ,
    ∃ G : FrameRefinement T F, G.Preserves k ∧
      ∀ P : RealizedTreeCore T h, EndsAt T F k P → EndHomogeneous T c G.frame P

def HeightFactorization (h : ℕ) (K : Type) : Prop :=
  ∀ c : RealizedTreeCore T (h + 1) → K,
    ∃ F : SynchronizedFrame T, ∃ d : RealizedTreeCore T h → K,
      ∀ C : RealizedTreeCore T (h + 1), RelativeCore T F C → c C = d (prefixCore T C)

theorem endHomogeneous_refinement {h : ℕ} {K : Type}
    {c : RealizedTreeCore T (h + 1) → K} {F : SynchronizedFrame T}
    (G : FrameRefinement T F) {P : RealizedTreeCore T h} (hP : EndHomogeneous T c F P) :
    EndHomogeneous T c G.frame P := by
  obtain ⟨a, ha⟩ := hP
  exact ⟨a, fun C hC he => ha C (G.relative_mono C hC) he⟩

end RelationalRamsey632.Milliken
