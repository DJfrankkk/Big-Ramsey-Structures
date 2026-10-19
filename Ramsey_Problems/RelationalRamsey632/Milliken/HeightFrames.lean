import RelationalRamsey632.Milliken.HalpernLauchli
import RelationalRamsey632.Milliken.LevelSelection
import Mathlib.Logic.Encodable.Basic

/-!
Actual finite strong-tree cores for the height induction.  A color sees
exactly `h` finite node levels in every coordinate, and no frame tail data.
-/

namespace RelationalRamsey632.Milliken

open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

variable {I : Type}
variable {α : I → Type} [∀ i, DecidableEq (α i)]
variable {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))

structure SynchronizedFrame where
  index : ℕ → ℕ
  index_strictMono : StrictMono index
  frames : ∀ i, (T i).StrongFrame
  frame_index : ∀ i, (frames i).index = index

abbrev FiniteTreeCore (_T : ∀ i, FiniteLevelTree (α i) (R i)) (h : ℕ) :=
  (i : I) → Fin h → Finset (α i)

namespace SynchronizedFrame

variable {T}

def core (F : SynchronizedFrame T) (h : ℕ) : FiniteTreeCore T h :=
  fun i n => (F.frames i).nodes n.val

def identity : SynchronizedFrame T where
  index := id
  index_strictMono := strictMono_id
  frames i := StrongFrame.identity (T i)
  frame_index _ := rfl

def comp (F : SynchronizedFrame T) (G : SynchronizedFrame (fun i => (F.frames i).toTree)) :
    SynchronizedFrame T where
  index := F.index ∘ G.index
  index_strictMono := F.index_strictMono.comp G.index_strictMono
  frames i := (F.frames i).comp (G.frames i)
  frame_index i := by
    funext n
    change (F.frames i).index ((G.frames i).index n) = F.index (G.index n)
    rw [F.frame_index, G.frame_index]

theorem comp_nodes_subset (F : SynchronizedFrame T)
    (G : SynchronizedFrame (fun i => (F.frames i).toTree)) (i : I) (n : ℕ) :
    ((F.comp G).frames i).nodes n ⊆ (F.frames i).nodes (G.index n) := by
  have h := (G.frames i).nodes_subset n
  rwa [G.frame_index] at h

end SynchronizedFrame

def HomogeneousStrongVector.toSynchronizedFrame {K : Type} {c : VectorNode T → K}
    (H : HomogeneousStrongVector T c) : SynchronizedFrame T :=
  ⟨H.index, H.index_strictMono, H.frames, H.frame_index⟩

abbrev RealizedTreeCore (h : ℕ) :=
  {C : FiniteTreeCore T h // ∃ F : SynchronizedFrame T, F.core h = C}

namespace SynchronizedFrame

variable {T}

def realizedCore (F : SynchronizedFrame T) (h : ℕ) : RealizedTreeCore T h :=
  ⟨F.core h, F, rfl⟩

end SynchronizedFrame

def RelativeCore {h : ℕ} (F : SynchronizedFrame T) (C : RealizedTreeCore T h) : Prop :=
  ∃ l : ℕ → ℕ, StrictMono l ∧ ∀ i (n : Fin h), C.val i n ⊆ (F.frames i).nodes (l n.val)

def MillikenHeight (h : ℕ) (K : Type) : Prop :=
  ∀ c : RealizedTreeCore T h → K, ∃ F : SynchronizedFrame T, ∃ color : K,
    ∀ C : RealizedTreeCore T h, RelativeCore T F C → c C = color

theorem height_zero (K : Type) : MillikenHeight T 0 K := by
  intro c
  let F : SynchronizedFrame T := SynchronizedFrame.identity
  refine ⟨F, c (F.realizedCore 0), ?_⟩
  intro C _
  apply congrArg c
  apply Subtype.ext
  funext i n
  exact n.elim0

theorem relative_core_refl (F : SynchronizedFrame T) (h : ℕ) :
    RelativeCore T F (F.realizedCore h) :=
  ⟨id, strictMono_id, fun _ _ => Finset.Subset.refl _⟩

theorem relative_core_comp {h : ℕ} (F : SynchronizedFrame T)
    (G : SynchronizedFrame (fun i => (F.frames i).toTree)) (C : RealizedTreeCore T h)
    (hC : RelativeCore T (F.comp G) C) : RelativeCore T F C := by
  obtain ⟨l, hl, hsub⟩ := hC
  exact ⟨G.index ∘ l, G.index_strictMono.comp hl, fun i n =>
    (hsub i n).trans (SynchronizedFrame.comp_nodes_subset F G i (l n.val))⟩

end RelationalRamsey632.Milliken
