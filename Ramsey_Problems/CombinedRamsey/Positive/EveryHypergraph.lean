import CombinedRamsey.Positive.OriginalHypergraph

/-! Every enumerated symmetric injective hypergraph with mutually exclusive colours is covered. -/

namespace CombinedRamsey.Positive.Marker

open RelationalRamsey632 RelationalRamsey632.Source RelationalRamsey632.Coding

variable {colours : ℕ → ℕ}

structure IsColouredHypergraph (H : RelStructure (hypergraphLanguage colours) ℕ) : Prop where
  injective : H.InjectiveRelations
  symmetric : ∀ r (R : (hypergraphLanguage colours).Rel r) (t : Fin r → ℕ)
    (sigma : Equiv.Perm (Fin r)), H.rel R (t ∘ sigma) ↔ H.rel R t
  exclusive : ∀ r (R S : (hypergraphLanguage colours).Rel r) (t : Fin r → ℕ),
    H.rel R t → H.rel S t → R = S

noncomputable def genuineColours (H : RelStructure (hypergraphLanguage colours) ℕ)
    (v : ℕ) (s : Coordinate v) : Fin (colours s.val.card + 1) := by
  classical
  by_cases h : ∃ R : (hypergraphLanguage colours).Rel (s.val.card + 1),
      H.rel R (supportTuple v s)
  · let R := Classical.choose h
    have hr := R.val.isLt
    simp only [Nat.add_sub_cancel] at hr
    exact ⟨R.val.val + 1, by omega⟩
  · exact 0

theorem genuineColours_true (H : RelStructure (hypergraphLanguage colours) ℕ)
    (hH : IsColouredHypergraph H) (v : ℕ) (s : Coordinate v)
    (R : (hypergraphLanguage colours).Rel (s.val.card + 1)) :
    (genuineColours H v s).val = R.val.val + 1 ↔ H.rel R (supportTuple v s) := by
  classical
  unfold genuineColours
  split_ifs with h
  · let S := Classical.choose h
    have hS : H.rel S (supportTuple v s) := Classical.choose_spec h
    constructor
    · intro hc
      change S.val.val + 1 = R.val.val + 1 at hc
      have hval : S.val.val = R.val.val := by omega
      have hSR : S = R := Subtype.ext (Fin.ext hval)
      exact hSR ▸ hS
    · intro hR
      have hSR := hH.exclusive _ S R (supportTuple v s) hS hR
      exact congrArg (fun T : (hypergraphLanguage colours).Rel (s.val.card + 1) => T.val.val + 1) hSR
  · constructor
    · intro hc
      have hr := R.val.isLt
      change 0 = R.val.val + 1 at hc
      omega
    · intro hR
      exact False.elim (h ⟨R, hR⟩)

theorem symbol_cast_val {r q : ℕ} (h : q = r)
    (R : (hypergraphLanguage colours).Rel r) :
    (cast (congrArg (hypergraphLanguage colours).Rel h.symm) R).val.val = R.val.val := by
  cases h
  rfl

theorem rel_cast_iff (H : RelStructure (hypergraphLanguage colours) ℕ)
    {r q : ℕ} (h : q = r) (R : (hypergraphLanguage colours).Rel r) (u : Fin r → ℕ) :
    H.rel (cast (congrArg (hypergraphLanguage colours).Rel h.symm) R) (u ∘ Fin.cast h) ↔
      H.rel R u := by
  cases h
  rfl

theorem genuineColours_sorted (H : RelStructure (hypergraphLanguage colours) ℕ)
    (hH : IsColouredHypergraph H) {r : ℕ} (u : Fin (r + 1) → ℕ)
    (hu : StrictMono u) (hr : 0 < r) (R : (hypergraphLanguage colours).Rel (r + 1)) :
    (genuineColours H (u (Fin.last r)) (lowerSupport u hu hr)).val = R.val.val + 1 ↔ H.rel R u := by
  let s := lowerSupport u hu hr
  have hcard : s.val.card + 1 = r + 1 := congrArg (fun n => n + 1) (lowerSupport_card u hu hr)
  let Q := cast (congrArg (hypergraphLanguage colours).Rel hcard.symm) R
  have h := genuineColours_true H hH (u (Fin.last r)) s Q
  have hQ : Q.val.val = R.val.val := symbol_cast_val hcard R
  rw [hQ] at h
  have hsupp : supportTuple (u (Fin.last r)) s = u ∘ Fin.cast hcard := supportTuple_lowerSupport u hu hr
  rw [hsupp] at h
  exact h.trans (rel_cast_iff H hcard R u)

theorem genuineColours_represents (H : RelStructure (hypergraphLanguage colours) ℕ)
    (hH : IsColouredHypergraph H) : enumeratedHypergraph colours (genuineColours H) = H := by
  apply RelStructure.ext_rel
  intro k R t
  cases k with
  | zero => have hr := R.property; omega
  | succ r =>
    cases r with
    | zero => have hr := R.property; omega
    | succ r =>
      constructor
      · rintro ⟨_, u, sigma, hu, ht, hc⟩
        have h := (genuineColours_sorted H hH u hu (Nat.zero_lt_succ r) R).mp hc
        rw [ht]
        exact (hH.symmetric _ R u sigma).mpr h
      · intro ht
        have hinj := hH.injective _ R t (by omega) ht
        obtain ⟨u, sigma, hu, htu⟩ := exists_sorted_tuple t hinj
        have hU : H.rel R u := (hH.symmetric _ R u sigma).mp (htu ▸ ht)
        exact ⟨hinj, u, sigma, hu, htu,
          (genuineColours_sorted H hH u hu (Nat.zero_lt_succ r) R).mpr hU⟩

noncomputable def everyHypergraphEmbedding
    (H : RelStructure (hypergraphLanguage colours) ℕ) (hH : IsColouredHypergraph H) :
    RelEmbedding H (originalValuationHypergraph colours) where
  toFun := family colours (genuineColours H)
  injective := family_injective colours (genuineColours H)
  map_rel R t := by
    have h := family_rel colours (genuineColours H) R t
    rw [genuineColours_represents H hH] at h
    exact h

theorem every_hypergraph_uniform_closure
    (H : RelStructure (hypergraphLanguage colours) ℕ) (hH : IsColouredHypergraph H) :
    ∃ phi : RelEmbedding H (originalValuationHypergraph colours),
      StrictMono (fun v => (phi v).height) ∧
      ∀ S : Finset ℕ, S.Nonempty →
        Nat.card (closureLevels (Alphabet colours) (phi '' (S : Set ℕ))) ≤
          CombinedRamsey.Positive.originalEnvelopeBound S.card := by
  classical
  refine ⟨everyHypergraphEmbedding H hH, originalHeight_strictMono colours, ?_⟩
  intro S hne
  have himage : (everyHypergraphEmbedding H hH) '' (S : Set ℕ) =
      (imageSet colours (genuineColours H) S : Set (Node (Alphabet colours) 0)) :=
    (Finset.coe_image (s := S) (f := family colours (genuineColours H))).symm
  rw [himage]
  exact uniform_closure_level_bound colours (genuineColours H) S hne

theorem every_hypergraph_uniform_envelopes
    (H : RelStructure (hypergraphLanguage colours) ℕ) (hH : IsColouredHypergraph H) :
    ∃ phi : RelEmbedding H (originalValuationHypergraph colours),
      StrictMono (fun v => (phi v).height) ∧
      ∀ S : Finset ℕ, S.Nonempty →
        ∃ h : ℕ, h ≤ CombinedRamsey.Positive.originalEnvelopeBound S.card ∧
          ∃ (e : ℕ → ℕ) (he : StrictMono e),
          ∃ V : FiniteStrongVector (Alphabet colours) e he h,
          ∀ i (t : Node (Alphabet colours) i),
            t ∈ closureNodes (Alphabet colours) (phi '' (S : Set ℕ)) i →
              ∃ (n : ℕ) (hn : i + n < h) (p : Level (Alphabet colours) i n),
                V.mapNode (Node.mk n p) hn = t := by
  classical
  refine ⟨everyHypergraphEmbedding H hH, originalHeight_strictMono colours, ?_⟩
  intro S hne
  have himage : (everyHypergraphEmbedding H hH) '' (S : Set ℕ) =
      (imageSet colours (genuineColours H) S : Set (Node (Alphabet colours) 0)) :=
    (Finset.coe_image (s := S) (f := family colours (genuineColours H))).symm
  rw [himage]
  exact CombinedRamsey.Positive.uniform_original_valuation_envelope colours (genuineColours H) S hne

end CombinedRamsey.Positive.Marker
