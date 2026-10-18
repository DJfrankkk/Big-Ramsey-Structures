import RelationalRamsey632.Coding.SliceLibrary
import Mathlib.Order.WellFounded

/-!
Exact all-sort slice-library counting. A valid slicing sequence is strictly
decreasing and is uniquely determined by its finite set of slicing heights.
Thus the entire library, rather than each depth separately, is bounded by
the number of generators times the number of subsets of the allowed heights.
-/

namespace CombinedRamsey.Positive

open RelationalRamsey632.Source RelationalRamsey632.Coding

theorem evaluateSlices_strictAnti {A : ℕ → Type} (s : Node A 0) (i : ℕ)
    (coords : Fin i → ℕ) (t : Node A i) (h : evaluateSlices s i coords = some t) :
    StrictAnti coords := by
  induction i with
  | zero => intro a; exact a.elim0
  | succ i ih =>
    cases hp : evaluateSlices s i (fun j => coords j.castSucc) with
    | none => simp [evaluateSlices, hp] at h
    | some u =>
      by_cases hn : coords (Fin.last i) < u.height
      · have hi := ih _ u hp
        have habove := (evaluateSlices_invariant s i (fun j => coords j.castSucc) u hp).2.1
        intro a b hab
        revert b
        refine Fin.lastCases ?_ (fun a => ?_) a
        · intro b
          refine Fin.lastCases ?_ (fun b => ?_) b
          · intro hlt; exact False.elim ((lt_irrefl _) hlt)
          · intro hlt
            have hval : (Fin.last i).val < b.castSucc.val := hlt
            have hb := b.isLt
            simp only [Fin.val_last, Fin.val_castSucc] at hval
            omega
        · intro b
          refine Fin.lastCases ?_ (fun b => ?_) b
          · intro _
            exact hn.trans_le (habove a)
          · intro hlt
            exact hi hlt
      · simp [evaluateSlices, hp, hn] at h

theorem decreasing_coordinates_image_injective {i : ℕ}
    {f g : Fin i → ℕ} (hf : StrictAnti f) (hg : StrictAnti g)
    (h : Finset.univ.image f = Finset.univ.image g) : f = g := by
  apply (hf.range_inj hg).mp
  have e := congrArg (fun s : Finset ℕ => (s : Set ℕ)) h
  simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using e

variable (A : ℕ → Type) (X : Set (Node A 0)) (H : Finset ℕ)

abbrev TaggedSliceLibrary := (i : ℕ) × sliceLibrary A X H i

theorem all_sort_sliceLibrary_finite_card (hX : X.Finite) :
    Finite (TaggedSliceLibrary A X H) ∧
      Nat.card (TaggedSliceLibrary A X H) ≤ Nat.card X * 2 ^ H.card := by
  classical
  let Code := X × {P : Finset ℕ // P ∈ H.powerset}
  haveI : Finite X := hX.to_subtype
  haveI : Finite Code := inferInstance
  have witnesses : ∀ q : TaggedSliceLibrary A X H,
      ∃ s : X, ∃ coords : Fin q.1 → ℕ,
        (∀ j, coords j ∈ H) ∧ evaluateSlices s.val q.1 coords = some q.2.val := by
    intro q
    obtain ⟨s, hs, coords, hcoords, he⟩ := q.2.property
    exact ⟨⟨s, hs⟩, coords, hcoords, he⟩
  choose generator coords mem_coords evaluate using witnesses
  have anti (q : TaggedSliceLibrary A X H) : StrictAnti (coords q) :=
    evaluateSlices_strictAnti (generator q).val q.1 (coords q) q.2.val (evaluate q)
  let code : TaggedSliceLibrary A X H → Code := fun q =>
    ⟨generator q, ⟨Finset.univ.image (coords q), Finset.mem_powerset.mpr (by
      intro n hn
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hn
      exact mem_coords q j)⟩⟩
  have hinj : Function.Injective code := by
    intro q r he
    have hgenerator : generator q = generator r := congrArg Prod.fst he
    have hcoords : Finset.univ.image (coords q) = Finset.univ.image (coords r) :=
      congrArg (fun c : Code => c.2.val) he
    have hdepth : q.1 = r.1 := by
      have hc := congrArg Finset.card hcoords
      simpa only [Finset.card_image_of_injective _ (anti q).injective,
        Finset.card_image_of_injective _ (anti r).injective,
        Finset.card_univ, Fintype.card_fin] using hc
    cases q with
    | mk i q =>
      cases r with
      | mk j r =>
        dsimp only at hdepth
        subst j
        have hc := decreasing_coordinates_image_injective (anti ⟨i, q⟩) (anti ⟨i, r⟩) hcoords
        have hs : (generator ⟨i, q⟩).val = (generator ⟨i, r⟩).val := congrArg Subtype.val hgenerator
        have ht : q.val = r.val := by
          apply Option.some.inj
          calc
            some q.val = evaluateSlices (generator ⟨i, q⟩).val i (coords ⟨i, q⟩) :=
              (evaluate ⟨i, q⟩).symm
            _ = evaluateSlices (generator ⟨i, r⟩).val i (coords ⟨i, r⟩) := by rw [hs, hc]
            _ = some r.val := evaluate ⟨i, r⟩
        exact congrArg (Sigma.mk i) (Subtype.ext ht)
  haveI : Finite (TaggedSliceLibrary A X H) := Finite.of_injective code hinj
  refine ⟨inferInstance, ?_⟩
  have hc := Nat.card_le_card_of_injective code hinj
  simpa only [Code, Nat.card_prod, Nat.card_eq_finsetCard, Finset.card_powerset] using hc

theorem all_sort_sliceLibrary_four_power {k : ℕ}
    (hX : X.Finite) (hk : Nat.card X ≤ k) (hH : H.card ≤ 2 * k) :
    Nat.card (TaggedSliceLibrary A X H) ≤ k * 4 ^ k := by
  apply (all_sort_sliceLibrary_finite_card A X H hX).2.trans
  calc
    Nat.card X * 2 ^ H.card ≤ k * 2 ^ (2 * k) :=
      Nat.mul_le_mul hk (Nat.pow_le_pow_right (by decide) hH)
    _ = k * 4 ^ k := by rw [pow_mul]; rfl

end CombinedRamsey.Positive
