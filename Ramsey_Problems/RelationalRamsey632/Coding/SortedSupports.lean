import RelationalRamsey632.Source.Nodes
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic

namespace RelationalRamsey632.Coding

open Source

def supportSet (v : ℕ) (s : Coordinate v) : Finset ℕ := insert v s.val

theorem support_not_mem (v : ℕ) (s : Coordinate v) : v ∉ s.val := by
  intro hv
  exact Nat.lt_irrefl v (Finset.mem_range.mp (s.property.2 hv))

theorem support_card (v : ℕ) (s : Coordinate v) :
    (supportSet v s).card = s.val.card + 1 :=
  Finset.card_insert_of_notMem (support_not_mem v s)

noncomputable def supportTuple (v : ℕ) (s : Coordinate v) : Fin (s.val.card + 1) ↪o ℕ :=
  (supportSet v s).orderEmbOfFin (support_card v s)

theorem supportTuple_mem (v : ℕ) (s : Coordinate v) (j : Fin (s.val.card + 1)) :
    supportTuple v s j ∈ supportSet v s :=
  Finset.orderEmbOfFin_mem _ _ j

theorem supportTuple_last (v : ℕ) (s : Coordinate v) :
    supportTuple v s (Fin.last s.val.card) = v := by
  have hmax : (supportSet v s).max' (by simp [supportSet]) = v := by
    apply le_antisymm
    · apply Finset.max'_le
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact le_rfl
      · exact Nat.le_of_lt (Finset.mem_range.mp (s.property.2 hx))
    · exact Finset.le_max' _ v (Finset.mem_insert_self _ _)
  have hh := Finset.orderEmbOfFin_last (support_card v s) (Nat.zero_lt_succ s.val.card)
  convert hh.trans hmax using 1
  congr 1

def lowerSupport {r : ℕ} (u : Fin (r + 1) → ℕ) (hu : StrictMono u) (hr : 0 < r) :
    Coordinate (u (Fin.last r)) :=
  ⟨Finset.univ.image (fun j : Fin r => u j.castSucc), by
    exact ⟨u (⟨0, hr⟩ : Fin r).castSucc,
        Finset.mem_image.mpr ⟨⟨0, hr⟩, Finset.mem_univ _, rfl⟩⟩
    , by
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (hu (Fin.castSucc_lt_last j))⟩

theorem lowerSupport_card {r : ℕ} (u : Fin (r + 1) → ℕ) (hu : StrictMono u) (hr : 0 < r) :
    (lowerSupport u hu hr).val.card = r := by
  change (Finset.univ.image (u ∘ Fin.castSucc)).card = r
  rw [Finset.card_image_of_injective _ (hu.injective.comp (Fin.castSucc_injective r))]
  exact Finset.card_fin r

theorem supportSet_lowerSupport {r : ℕ} (u : Fin (r + 1) → ℕ)
    (hu : StrictMono u) (hr : 0 < r) :
    supportSet (u (Fin.last r)) (lowerSupport u hu hr) = Finset.univ.image u := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_image.mpr ⟨Fin.last r, Finset.mem_univ _, rfl⟩
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨j.castSucc, Finset.mem_univ _, rfl⟩
  · intro hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    induction j using Fin.lastCases with
    | last => exact Finset.mem_insert_self _ _
    | cast j => exact Finset.mem_insert.mpr (Or.inr
        (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))

theorem supportTuple_lowerSupport {r : ℕ} (u : Fin (r + 1) → ℕ)
    (hu : StrictMono u) (hr : 0 < r) :
    supportTuple (u (Fin.last r)) (lowerSupport u hu hr) =
      u ∘ Fin.cast (congrArg (fun k => k + 1) (lowerSupport_card u hu hr)) := by
  apply Eq.symm
  apply Finset.orderEmbOfFin_unique
  · intro j
    rw [supportSet_lowerSupport]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · exact hu.comp (Fin.cast_strictMono _)

theorem exists_sorted_tuple {n : ℕ} (t : Fin n → ℕ) (ht : Function.Injective t) :
    ∃ u : Fin n → ℕ, ∃ σ : Equiv.Perm (Fin n), StrictMono u ∧ t = u ∘ σ := by
  classical
  let s := Finset.univ.image t
  have hs : s.card = n := by
    rw [Finset.card_image_of_injective _ ht]
    exact Finset.card_fin n
  let f : Fin n → s := fun j => ⟨t j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact ht (congrArg Subtype.val h)
    · intro x
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp x.property
      exact ⟨j, Subtype.ext hj⟩
  let E := Equiv.ofBijective f hf
  let U := s.orderIsoOfFin hs
  let σ := E.trans U.toEquiv.symm
  refine ⟨s.orderEmbOfFin hs, σ, (s.orderEmbOfFin hs).strictMono, ?_⟩
  funext j
  change t j = (U (U.symm (E j))).val
  rw [U.apply_symm_apply]
  rfl

end RelationalRamsey632.Coding
