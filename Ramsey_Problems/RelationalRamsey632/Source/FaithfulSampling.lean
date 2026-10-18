import RelationalRamsey632.Source.Successors

/-!
# Faithful sampling on a genuinely closed family

The proof needs actual retained full slices in the next sort and actual
retained meet heights. Sampling arbitrary unrelated tables would not be
injective; no such false assumption is made.
-/

namespace RelationalRamsey632.Source

variable {A : ℕ → Type} {e : ℕ → ℕ} (he : StrictMono e)
    (E : (i : ℕ) → Set (Node A i)) (L : Set ℕ)
    (hclosed : Closed A E L)
    (hgrid : ∀ i t, t ∈ E i → ∃ n, t.height = e n)

include hclosed hgrid

theorem faithful_sampling (n i : ℕ) (s t : Level A i (e n))
    (hs : (Node.mk (e n) s : Node A i) ∈ E i)
    (ht : (Node.mk (e n) t : Node A i) ∈ E i)
    (hF : s.sample e he = t.sample e he) : s = t := by
  induction n using Nat.strong_induction_on generalizing i with
  | h n ih =>
    let sn : Node A i := ⟨e n, s⟩
    let tn : Node A i := ⟨e n, t⟩
    by_cases hsame : sn = tn
    · exact Node.mk_injective (e n) hsame
    have hst : ¬ Node.Prefix sn tn := by
      intro h
      exact hsame (Node.prefix_eq_of_height_eq h rfl)
    have hts : ¬ Node.Prefix tn sn := by
      intro h
      exact hsame (Node.prefix_eq_of_height_eq h rfl).symm
    have hm := hclosed.meet i sn tn hs ht
    obtain ⟨k, hk⟩ := hgrid i (sn.meet tn) hm
    change Node.meetHeight sn tn = e k at hk
    have hproper := Node.meetHeight_lt_of_incomparable hst hts
    have hkn : k < n := by
      apply he.lt_iff_lt.mp
      change Node.meetHeight sn tn < min (e n) (e n) at hproper
      simpa only [hk, min_self] using hproper
    have hke : e k < e n := he hkn
    have hLevel : e k ∈ L := by
      have h := hclosed.height i (sn.meet tn) hm
      simpa only [Node.height_meet, hk] using h
    have hSlices :
        s.slice hke = t.slice hke := by
      apply ih k hkn (i + 1)
      · exact hclosed.slice i sn (e k) hs hLevel hke
      · exact hclosed.slice i tn (e k) ht hLevel hke
      · have h := congrArg (fun p : Level A i n => p.slice hkn) hF
        simpa only [Level.sample_slice] using h
    have hSingletons : s.singleton hke = t.singleton hke := by
      have h := congrArg (fun p : Level A i n => p.singleton hkn) hF
      simpa only [Level.sample_singleton] using h
    have hPreds : s.restrict (Nat.le_of_lt hke) =
        t.restrict (Nat.le_of_lt hke) := by
      obtain ⟨h1, h2, hp⟩ := Node.commonHeight_meetHeight sn tn
      have hp' : sn.restrict (e k) (Nat.le_of_lt hke) =
          tn.restrict (e k) (Nat.le_of_lt hke) := by
        simpa only [hk] using hp
      exact Node.mk_injective (e k) hp'
    have hstep : s.restrict (Nat.succ_le_of_lt hke) =
        t.restrict (Nat.succ_le_of_lt hke) := by
      apply Level.successor_ext
      · simpa only [Level.restrict_restrict] using hPreds
      · simpa only [Level.singleton_restrict] using hSingletons
      · simpa only [Level.slice_restrict] using hSlices
    have hNodes : sn.restrict (e k + 1) (Nat.succ_le_of_lt hke) =
        tn.restrict (e k + 1) (Nat.succ_le_of_lt hke) :=
      congrArg (fun p : Level A i (e k + 1) =>
        (Node.mk (e k + 1) p : Node A i)) hstep
    have hbad := Node.commonHeight_le_meetHeight
      ⟨Nat.succ_le_of_lt hke, Nat.succ_le_of_lt hke, hNodes⟩
    rw [hk] at hbad
    omega

end RelationalRamsey632.Source
