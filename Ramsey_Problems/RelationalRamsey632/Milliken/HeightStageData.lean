import RelationalRamsey632.Milliken.HeightEndedCores
import RelationalRamsey632.Milliken.HeightCoreTransport
import RelationalRamsey632.Milliken.HeightFrontier

/-! Actual ended-prefix witnesses and their actual last-frontier extensions. -/

namespace RelationalRamsey632.Milliken

open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

variable {I : Type} {α : I → Type} [∀ i, DecidableEq (α i)]
variable {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))
variable (F : SynchronizedFrame T) (k : ℕ) {h : ℕ}

abbrev EndedCore (h : ℕ) := {P : RealizedTreeCore T h // EndsAt T F k P}

noncomputable def endedSelector (P : EndedCore T F k h) : ℕ → ℕ := Classical.choose P.property

theorem endedSelector_strictMono (P : EndedCore T F k h) : StrictMono (endedSelector T F k P) :=
  (Classical.choose_spec P.property).1

theorem endedSelector_last (P : EndedCore T F k h) : endedSelector T F k P (h - 1) = k :=
  (Classical.choose_spec P.property).2.1

noncomputable def endedFrame (P : EndedCore T F k h) : SynchronizedFrame T :=
  Classical.choose P.val.property

theorem endedFrame_core (P : EndedCore T F k h) : (endedFrame T F k P).core h = P.val.val :=
  Classical.choose_spec P.val.property

theorem endedFrame_subset (P : EndedCore T F k h) (i : I) (n : ℕ) (hn : n < h) :
    ((endedFrame T F k P).frames i).nodes n ⊆ (F.frames i).nodes (endedSelector T F k P n) := by
  have hc := congrFun (congrFun (endedFrame_core T F k P) i) (⟨n, hn⟩ : Fin h)
  change ((endedFrame T F k P).frames i).nodes n = P.val.val i ⟨n, hn⟩ at hc
  rw [hc]
  exact (Classical.choose_spec P.property).2.2 i ⟨n, hn⟩

noncomputable def endedPrefix (P : EndedCore T F k h) (i : I) :
    FiniteStrongPrefix (F.frames i).toTree (endedSelector T F k P) h :=
  relativeFinitePrefix (F.frames i) ((endedFrame T F k P).frames i)
    (endedSelector T F k P) (endedSelector_strictMono T F k P) h (endedFrame_subset T F k P i)

theorem endedPrefix_core (P : EndedCore T F k h) (i : I) (n : Fin h) :
    (endedPrefix T F k P i).nodes n.val = P.val.val i n :=
  congrFun (congrFun (endedFrame_core T F k P) i) n

noncomputable def appendEndedCore (P : EndedCore T F k h) (hh : 0 < h) (m : ℕ)
    (x : ∀ i, ConeAnchor (F.frames i).toTree (k + 1) → α i)
    (hxLevel : ∀ i a, x i a ∈ (F.frames i).nodes m)
    (hxCone : ∀ i a, R i a.val (x i a)) (hkm : k < m) : RealizedTreeCore T (h + 1) :=
  liftCore T F ((HeightFrontier.synchronizedExtension (fun i => (F.frames i).toTree)
    h k m hh (endedSelector T F k P) (endedSelector_strictMono T F k P)
    (endedSelector_last T F k P) (endedPrefix T F k P) x hxLevel hxCone hkm).realizedCore (h + 1))

theorem appendEndedCore_initial (P : EndedCore T F k h) (hh : 0 < h) (m : ℕ)
    (x : ∀ i, ConeAnchor (F.frames i).toTree (k + 1) → α i)
    (hxLevel : ∀ i a, x i a ∈ (F.frames i).nodes m)
    (hxCone : ∀ i a, R i a.val (x i a)) (hkm : k < m) (i : I) (n : Fin h) :
    (appendEndedCore T F k P hh m x hxLevel hxCone hkm).val i n.castSucc = P.val.val i n := by
  change ((HeightFrontier.synchronizedExtension (fun i => (F.frames i).toTree)
    h k m hh (endedSelector T F k P) (endedSelector_strictMono T F k P)
    (endedSelector_last T F k P) (endedPrefix T F k P) x hxLevel hxCone hkm).frames i).nodes n.val = _
  rw [HeightFrontier.synchronizedExtension_initial]
  · exact endedPrefix_core T F k P i n
  · exact n.isLt

theorem appendEndedCore_last (P : EndedCore T F k h) (hh : 0 < h) (m : ℕ)
    (x : ∀ i, ConeAnchor (F.frames i).toTree (k + 1) → α i)
    (hxLevel : ∀ i a, x i a ∈ (F.frames i).nodes m)
    (hxCone : ∀ i a, R i a.val (x i a)) (hkm : k < m) (i : I) :
    (appendEndedCore T F k P hh m x hxLevel hxCone hkm).val i (Fin.last h) =
      HeightFrontier.lastNodes (F.frames i).toTree (endedSelector T F k P) h k (endedPrefix T F k P i) (x i) :=
  HeightFrontier.synchronizedExtension_last (fun i => (F.frames i).toTree) h k m hh
    (endedSelector T F k P) (endedSelector_strictMono T F k P)
    (endedSelector_last T F k P) (endedPrefix T F k P) x hxLevel hxCone hkm i

theorem appendEndedCore_prefix (P : EndedCore T F k h) (hh : 0 < h) (m : ℕ)
    (x : ∀ i, ConeAnchor (F.frames i).toTree (k + 1) → α i)
    (hxLevel : ∀ i a, x i a ∈ (F.frames i).nodes m)
    (hxCone : ∀ i a, R i a.val (x i a)) (hkm : k < m) :
    prefixCore T (appendEndedCore T F k P hh m x hxLevel hxCone hkm) = P.val := by
  apply Subtype.ext
  funext i n
  exact appendEndedCore_initial T F k P hh m x hxLevel hxCone hkm i n

theorem appendEndedCore_eq (P : EndedCore T F k h) (hh : 0 < h) (m : ℕ)
    (x : ∀ i, ConeAnchor (F.frames i).toTree (k + 1) → α i)
    (hxLevel : ∀ i a, x i a ∈ (F.frames i).nodes m)
    (hxCone : ∀ i a, R i a.val (x i a)) (hkm : k < m)
    (C : RealizedTreeCore T (h + 1)) (hprefix : prefixCore T C = P.val)
    (hlast : ∀ i, HeightFrontier.lastNodes (F.frames i).toTree (endedSelector T F k P) h k
      (endedPrefix T F k P i) (x i) = C.val i (Fin.last h)) :
    appendEndedCore T F k P hh m x hxLevel hxCone hkm = C := by
  apply Subtype.ext
  funext i n
  refine Fin.lastCases ?_ (fun j => ?_) n
  · exact (appendEndedCore_last T F k P hh m x hxLevel hxCone hkm i).trans (hlast i)
  · exact (appendEndedCore_initial T F k P hh m x hxLevel hxCone hkm i j).trans
      (congrFun (congrFun (congrArg Subtype.val hprefix).symm i) j)

end RelationalRamsey632.Milliken


