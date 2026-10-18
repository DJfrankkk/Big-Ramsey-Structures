import RelationalRamsey632.Source.Successors

namespace RelationalRamsey632.Source.Node

variable {A : ℕ → Type} {i : ℕ}

/-- Incomparable nodes first disagree on a coordinate whose largest
argument is the height of their greatest common restriction. -/
theorem meet_disagreement (s t : Node A i)
    (hst : ¬ Prefix s t) (hts : ¬ Prefix t s) :
    ∃ c : Coordinate (meetHeight s t + 1),
      meetHeight s t ∈ c.val ∧
      (s.table.restrict (by
        have h := meetHeight_lt_of_incomparable hst hts
        omega)) c ≠
      (t.table.restrict (by
        have h := meetHeight_lt_of_incomparable hst hts
        omega)) c := by
  classical
  let m := meetHeight s t
  have hproper := meetHeight_lt_of_incomparable hst hts
  have hs : m + 1 ≤ s.height := by dsimp [m]; omega
  have ht : m + 1 ≤ t.height := by dsimp [m]; omega
  have hneq : s.table.restrict hs ≠ t.table.restrict ht := by
    intro he
    have hn : s.restrict (m + 1) hs = t.restrict (m + 1) ht :=
      congrArg (fun p : Level A i (m + 1) => (Node.mk (m + 1) p : Node A i)) he
    have hbad := commonHeight_le_meetHeight ⟨hs, ht, hn⟩
    change m + 1 ≤ m at hbad
    omega
  have hex : ∃ c : Coordinate (m + 1), s.table.restrict hs c ≠ t.table.restrict ht c := by
    by_contra h
    apply hneq
    funext c
    by_contra hc
    exact h ⟨c, hc⟩
  obtain ⟨c, hc⟩ := hex
  have htop : m ∈ c.val := by
    by_contra hm
    obtain ⟨hs0, ht0, hp⟩ := commonHeight_meetHeight s t
    have hpTable : s.table.restrict hs0 = t.table.restrict ht0 := mk_injective m hp
    have he := congrFun hpTable (c.lower hm)
    exact hc he
  exact ⟨c, htop, hc⟩

end RelationalRamsey632.Source.Node
