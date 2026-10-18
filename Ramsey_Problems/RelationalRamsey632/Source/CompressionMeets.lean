import RelationalRamsey632.Source.Compression

/-! Meet preservation by faithful compression, proved for the actual nodes. -/

namespace RelationalRamsey632.Source

theorem sampled_prefix {A : ℕ → Type} {e : ℕ → ℕ} (he : StrictMono e)
    (i n m : ℕ) (s : Level A i (e n)) (t : Level A i (e m))
    (h : Node.Prefix (Node.mk (e n) s) (Node.mk (e m) t)) :
    Node.Prefix (Node.mk n (s.sample e he)) (Node.mk m (t.sample e he)) := by
  obtain ⟨hle, hEq⟩ := h
  have hnm : n ≤ m := he.le_iff_le.mp hle
  have ht : t.restrict (he.monotone hnm) = s := Node.mk_injective (e n) hEq
  refine ⟨hnm, ?_⟩
  apply congrArg (fun p : Level A i n => (Node.mk n p : Node A i))
  exact (Level.sample_restrict e he t hnm).trans (congrArg (Level.sample e he) ht)

theorem compressOn_meet_mk {A : ℕ → Type} {e : ℕ → ℕ} (he : StrictMono e)
    (E : (i : ℕ) → Set (Node A i)) (L : Set ℕ)
    (hclosed : Closed A E L) (hgrid : ∀ i t, t ∈ E i → ∃ n, t.height = e n)
    (i n m : ℕ) (s : Level A i (e n)) (t : Level A i (e m))
    (hs : (Node.mk (e n) s : Node A i) ∈ E i)
    (ht : (Node.mk (e m) t : Node A i) ∈ E i) :
    compressOn e he ((Node.mk (e n) s).meet (Node.mk (e m) t)) =
      (compressOn e he (Node.mk (e n) s)).meet
        (compressOn e he (Node.mk (e m) t)) := by
  let sn : Node A i := ⟨e n, s⟩
  let tn : Node A i := ⟨e m, t⟩
  let sc : Node A i := ⟨n, s.sample e he⟩
  let tc : Node A i := ⟨m, t.sample e he⟩
  have hm := hclosed.meet i sn tn hs ht
  obtain ⟨k, hk⟩ := hgrid i (sn.meet tn) hm
  change Node.meetHeight sn tn = e k at hk
  have hkn : k ≤ n := he.le_iff_le.mp (hk ▸ Node.meetHeight_le_left sn tn)
  have hkm : k ≤ m := he.le_iff_le.mp (hk ▸ Node.meetHeight_le_right sn tn)
  have hsourceMeet :
      sn.meet tn = Node.mk (e k) (s.restrict (he.monotone hkn)) := by
    simp only [Node.meet, hk]
    rfl
  let pc : Node A i := ⟨k, (s.restrict (he.monotone hkn)).sample e he⟩
  have hpreS : Node.Prefix pc sc := sampled_prefix he i k n _ s
    (hsourceMeet ▸ Node.meet_prefix_left sn tn)
  have hpreT : Node.Prefix pc tc := sampled_prefix he i k m _ t
    (hsourceMeet ▸ Node.meet_prefix_right sn tn)
  have hpre := Node.common_prefix_prefix_meet hpreS hpreT
  have hlo : k ≤ Node.meetHeight sc tc := Node.prefix_height_le hpre
  have hLevel : e k ∈ L := by
    simpa only [Node.height_meet, hk] using hclosed.height i (sn.meet tn) hm
  have hhi : Node.meetHeight sc tc ≤ k := by
    by_contra hnot
    have hsucc : k + 1 ≤ Node.meetHeight sc tc := by omega
    obtain ⟨h1, h2, hcut⟩ := Node.commonHeight_downward
      (Node.commonHeight_meetHeight sc tc) hsucc
    have hkn' : k < n := by change k + 1 ≤ n at h1; omega
    have hkm' : k < m := by change k + 1 ≤ m at h2; omega
    have hcutTable : (s.sample e he).restrict h1 =
        (t.sample e he).restrict h2 := Node.mk_injective (k + 1) hcut
    have ha : s.singleton (he hkn') = t.singleton (he hkm') := by
      have hh := congrArg (fun p : Level A i (k + 1) =>
        p.singleton (Nat.lt_succ_self k)) hcutTable
      simpa only [Level.singleton_restrict, Level.sample_singleton] using hh
    have hv : s.slice (he hkn') = t.slice (he hkm') := by
      apply faithful_sampling he E L hclosed hgrid k (i + 1)
      · exact hclosed.slice i sn (e k) hs hLevel (he hkn')
      · exact hclosed.slice i tn (e k) ht hLevel (he hkm')
      · have hh := congrArg (fun p : Level A i (k + 1) =>
          p.slice (Nat.lt_succ_self k)) hcutTable
        simpa only [Level.slice_restrict, Level.sample_slice] using hh
    have hp : s.restrict (he.monotone hkn) = t.restrict (he.monotone hkm) := by
      obtain ⟨h1', h2', hEq⟩ := Node.commonHeight_meetHeight sn tn
      have hEq' : sn.restrict (e k) (he.monotone hkn) =
          tn.restrict (e k) (he.monotone hkm) := by simpa only [hk] using hEq
      exact Node.mk_injective (e k) hEq'
    have hstep : s.restrict (Nat.succ_le_of_lt (he hkn')) =
        t.restrict (Nat.succ_le_of_lt (he hkm')) := by
      apply Level.successor_ext
      · simpa only [Level.restrict_restrict] using hp
      · simpa only [Level.singleton_restrict] using ha
      · simpa only [Level.slice_restrict] using hv
    have hstepNodes : sn.restrict (e k + 1) (Nat.succ_le_of_lt (he hkn')) =
        tn.restrict (e k + 1) (Nat.succ_le_of_lt (he hkm')) :=
      congrArg (fun p : Level A i (e k + 1) =>
        (Node.mk (e k + 1) p : Node A i)) hstep
    have hbad := Node.commonHeight_le_meetHeight
      ⟨Nat.succ_le_of_lt (he hkn'), Nat.succ_le_of_lt (he hkm'), hstepNodes⟩
    rw [hk] at hbad
    omega
  have hEq : pc = sc.meet tc :=
    Node.prefix_eq_of_height_eq hpre (Nat.le_antisymm hlo hhi)
  calc
    compressOn e he (sn.meet tn) = pc := by
      rw [hsourceMeet]
      exact compressOn_mk e he i k _
    _ = sc.meet tc := hEq
    _ = (compressOn e he sn).meet (compressOn e he tn) := by
      rw [compressOn_mk, compressOn_mk]

end RelationalRamsey632.Source
