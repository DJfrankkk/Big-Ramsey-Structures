import CombinedRamsey.Positive.UniformClosureBound
import RelationalRamsey632.Source.Envelopes
import RelationalRamsey632.Source.NormalForms

/-! Genuine valuation envelopes in the original ambient alphabet, uniformly at every size. -/

namespace CombinedRamsey.Positive

open RelationalRamsey632.Source

def ambientVector (A : ℕ → Type) : StrongVector A id strictMono_id where
  nodes _ _ := Set.univ
  root i := (Node.root (A := A) i).table
  root_mem _ := Set.mem_univ _
  root_unique i p _ := by
    have h := Node.height_zero_unique (Node.mk 0 p : Node A i) rfl
    exact Node.mk_injective 0 h
  successor i n p _ a v := by
    refine ⟨Level.extend p a v, ⟨Set.mem_univ _, ?_⟩, ?_⟩
    · exact Level.restrict_refl _
    · intro q hq
      have hcone := hq.2
      change q.restrict (Nat.le_refl (n + 1)) = Level.extend p a v at hcone
      exact (Level.restrict_refl q).symm.trans hcone
  parent _ _ _ _ := Set.mem_univ _

theorem ambientVector_source_contains (A : ℕ → Type) (i : ℕ) :
    sourceNodes (ambientVector A) i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro t
  exact ⟨t.height, t.table, Set.mem_univ _, rfl⟩

variable (colours : ℕ → ℕ) (c : ∀ v, Marker.GenuineColours colours v)

/-- Every node of the full intrinsic closure, hence every generator, belongs
to one actual finite valuation envelope of height at most the stated R(k). -/
theorem uniform_original_valuation_envelope (S : Finset ℕ) (hne : S.Nonempty) :
    ∃ h : ℕ, h ≤ originalEnvelopeBound S.card ∧
      ∃ (e : ℕ → ℕ) (he : StrictMono e),
      ∃ V : FiniteStrongVector (Marker.Alphabet colours) e he h,
      ∀ i (t : Node (Marker.Alphabet colours) i),
        t ∈ closureNodes (Marker.Alphabet colours)
          (Marker.imageSet colours c S : Set (Node (Marker.Alphabet colours) 0)) i →
          ∃ (n : ℕ) (hn : i + n < h) (p : Level (Marker.Alphabet colours) i n),
            V.mapNode (Node.mk n p) hn = t := by
  classical
  let X : Set (Node (Marker.Alphabet colours) 0) := Marker.imageSet colours c S
  let hfin := closureLevels_finite_of_finite (Marker.imageSet_finite colours c S)
  let L := hfin.toFinset
  let e := levelEnumeration L
  have hlevels : closureLevels (Marker.Alphabet colours) X =
      Set.range (fun n : Fin L.card => id (e n.val)) := by
    ext m
    constructor
    · intro hm
      have hmL : m ∈ L := hfin.mem_toFinset.mpr hm
      obtain ⟨n, hn⟩ := levelEnumeration_range_contains L hmL
      have hnL : n < L.card := (levelEnumeration_mem_iff L n).mp (hn ▸ hmL)
      exact ⟨⟨n, hnL⟩, hn.symm⟩
    · rintro ⟨n, rfl⟩
      exact hfin.mem_toFinset.mp ((levelEnumeration_mem_iff L n.val).mpr n.isLt)
  have hsource : ∀ i, closureNodes (Marker.Alphabet colours) X i ⊆
      sourceNodes (ambientVector (Marker.Alphabet colours)) i := by
    intro i t _
    rw [ambientVector_source_contains]
    exact Set.mem_univ _
  obtain ⟨V, _, _, hmarked⟩ := closure_marked_envelope
    (ambientVector (Marker.Alphabet colours)) X e (levelEnumeration_strictMono L) L.card hsource hlevels
  have hbound : L.card ≤ originalEnvelopeBound S.card := by
    rw [← Nat.card_eq_card_finite_toFinset hfin]
    exact Marker.uniform_closure_level_bound colours c S hne
  refine ⟨L.card, hbound, id ∘ e, strictMono_id.comp (levelEnumeration_strictMono L), V, ?_⟩
  intro i t ht
  have hm : t.height ∈ closureLevels (Marker.Alphabet colours) X := Generated.height t ht
  rw [hlevels] at hm
  obtain ⟨n, hn⟩ := hm
  cases t with
  | mk a table =>
    dsimp only [Node.height, id] at hn
    subst a
    obtain ⟨hd, _, heq⟩ := hmarked i n.val table ht
    refine ⟨n.val, hd, table.sample (id ∘ e) (strictMono_id.comp (levelEnumeration_strictMono L)), ?_⟩
    exact congrArg (Node.mk (e n.val)) heq

include c in
/-- Quantifier order: this one node family works for all finite S. -/
theorem single_embedding_all_sizes :
    ∃ phi : ℕ → Node (Marker.Alphabet colours) 0,
      Function.Injective phi ∧ StrictMono (fun v => (phi v).height) ∧
      (∀ v, (phi v).height = Marker.originalHeight colours v) ∧
      ∀ S : Finset ℕ, S.Nonempty →
        Nat.card (closureLevels (Marker.Alphabet colours) (phi '' (S : Set ℕ))) ≤
          originalEnvelopeBound S.card := by
  classical
  refine ⟨Marker.family colours c, Marker.family_injective colours c,
    Marker.originalHeight_strictMono colours, (fun _ => rfl), ?_⟩
  intro S hne
  have himage : Marker.family colours c '' (S : Set ℕ) =
      (Marker.imageSet colours c S : Set (Node (Marker.Alphabet colours) 0)) :=
    (Finset.coe_image (s := S) (f := Marker.family colours c)).symm
  rw [himage]
  exact Marker.uniform_closure_level_bound colours c S hne

end CombinedRamsey.Positive
