import CombinedRamsey.Positive.ProfileDecoder
import RelationalRamsey632.Source.MarkedSampling
import RelationalRamsey632.Source.ValuationModel

namespace CombinedRamsey.Positive.Relational

open RelationalRamsey632 RelationalRamsey632.Source RelationalRamsey632.Coding

variable (L : Language) [∀ r, Fintype (L.Rel r)]

theorem finite_val_of_heq {n m : ℕ} {x : Fin n} {y : Fin m} (h : HEq x y) : x.val = y.val := by
  have hnm : n = m := by
    simpa using congrArg Nat.card (type_eq_of_heq h)
  subst m
  exact congrArg Fin.val (eq_of_heq h)

theorem normalForm_injective_iff {r : ℕ} (t : Fin r → DecoderVertex L) :
    Function.Injective (normalForm t) ↔ Function.Injective t := by
  constructor
  · intro h i j hij
    apply h
    apply Prod.ext
    · change (t i).fst = (t j).fst
      exact congrArg Prod.fst hij
    · exact congrArg (fun v : DecoderVertex L => canonicalCompression (tupleLevels t) v.2) hij
  · exact normalForm_injective t

theorem normalForm_strictHeights_iff {r : ℕ} (t : Fin r → DecoderVertex L) :
    StrictMono (decoderHeight L ∘ normalForm t) ↔ StrictMono (decoderHeight L ∘ t) := by
  constructor
  · intro h i j hij
    exact (normalForm_height_lt_iff t i j).mp (h hij)
  · intro h i j hij
    exact (normalForm_height_lt_iff t i j).mpr (h hij)

theorem passingValue_normalForm {r : ℕ} (u : Fin (r + 1) → DecoderVertex L)
    (hu : StrictMono (decoderHeight L ∘ u)) (hr : 0 < r) :
    passingValue L (normalForm u) ((normalForm_strictHeights_iff L u).mpr hu) hr =
      passingValue L u hu hr := by
  let hu' := (normalForm_strictHeights_iff L u).mpr hu
  let c := passingCoordinate L u hu hr
  let d := passingCoordinate L (normalForm u) hu' hr
  have hcoords : d.val.image (levelEnumeration (tupleLevels u)) = c.val := by
    change (Finset.univ.image (fun j : Fin r => (normalForm u j.castSucc).2.height)).image
      (levelEnumeration (tupleLevels u)) =
      Finset.univ.image (fun j : Fin r => (u j.castSucc).2.height)
    rw [Finset.image_image]
    apply Finset.image_congr
    intro j _
    exact canonicalCompression_height_recover (tupleLevels u) (u j.castSucc).2
      (marked_height_mem u j.castSucc)
  have h := canonicalCompression_evaluation (tupleLevels u) (u (Fin.last r)).2
    (marked_height_mem u (Fin.last r)) c d hcoords
  apply Fin.ext
  rw [passingValue_val, passingValue_val]
  exact finite_val_of_heq h

theorem passingProfile_normalForm {r : ℕ} (u : Fin (r + 1) → DecoderVertex L)
    (hu : StrictMono (decoderHeight L ∘ u)) (hr : 0 < r) :
    decodeProfile L r
      (passingValue L (normalForm u) ((normalForm_strictHeights_iff L u).mpr hu) hr) =
      decodeProfile L r (passingValue L u hu hr) := by
  rw [passingValue_normalForm]

theorem decoder_normalForm {r : ℕ} (R : L.Rel r) (t : Fin r → DecoderVertex L) :
    (decoder L).rel R (normalForm t) ↔ (decoder L).rel R t := by
  cases r with
  | zero => rfl
  | succ r =>
    cases r with
    | zero => rfl
    | succ r =>
      constructor
      · rintro ⟨hi, w, σ, hw, ht, hd⟩
        let u := t ∘ σ.symm
        have hwu : w = normalForm u := by
          change w = normalForm (t ∘ σ.symm)
          rw [normalForm_permutation]
          funext j
          have h := congrFun ht (σ.symm j)
          simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h.symm
        have hu : StrictMono (decoderHeight L ∘ u) := by
          apply (normalForm_strictHeights_iff L u).mp
          simpa only [← hwu] using hw
        refine ⟨(normalForm_injective_iff L t).mp hi, u, σ, hu, ?_, ?_⟩
        · funext j
          exact congrArg t (σ.symm_apply_apply j).symm
        · have hd' : decodeProfile L (r + 1)
              (passingValue L (normalForm u) ((normalForm_strictHeights_iff L u).mpr hu)
                (Nat.zero_lt_succ r)) R σ = true := by
            simpa only [hwu] using hd
          rw [passingProfile_normalForm] at hd'
          exact hd'
      · rintro ⟨hi, u, σ, hu, ht, hd⟩
        refine ⟨(normalForm_injective_iff L t).mpr hi, normalForm u, σ,
          (normalForm_strictHeights_iff L u).mpr hu, ?_, ?_⟩
        · rw [ht]
          exact normalForm_permutation (ProfileAlphabet L) (UnaryProfile L) u σ
        · rw [passingProfile_normalForm]
          exact hd

theorem decoder_normalForm_determined {r : ℕ} (R : L.Rel r)
    (t u : Fin r → DecoderVertex L) (h : normalForm t = normalForm u) :
    (decoder L).rel R t ↔ (decoder L).rel R u := by
  calc
    (decoder L).rel R t ↔ (decoder L).rel R (normalForm t) := (decoder_normalForm L R t).symm
    _ ↔ (decoder L).rel R (normalForm u) := h ▸ Iff.rfl
    _ ↔ (decoder L).rel R u := decoder_normalForm L R u

end CombinedRamsey.Positive.Relational


