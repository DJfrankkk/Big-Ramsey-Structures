import CombinedRamsey.Positive.EveryHypergraph
import Mathlib.Data.Finset.Preimage

/-!
The literal envelope-height quantifier pattern of Conjecture 4.7 in
Braunfeld et al., Big Ramsey Degrees and Infinite Languages (2024), p. 12.
Envelopes mean containment in genuine finite valuation trees (Definition 4.3).
The conjecture's additional unbounded-language and universality assumptions
are unnecessary for disproving its consequent for every coloured H.
-/

namespace CombinedRamsey.Positive

open RelationalRamsey632 RelationalRamsey632.Source

def EnvelopedAt (A : ℕ → Type) (X : Set (Node A 0)) (h : ℕ) : Prop :=
  ∃ (e : ℕ → ℕ) (he : StrictMono e),
    ∃ V : FiniteStrongVector A e he h,
      ∀ t ∈ X, ∃ (n : ℕ) (hn : 0 + n < h) (p : Level A 0 n),
        V.mapNode (Node.mk n p) hn = t

theorem empty_envelopedAt_zero (A : ℕ → Type) : EnvelopedAt A ∅ 0 := by
  refine ⟨id, strictMono_id, (ambientVector A).finitePrefix 0, ?_⟩
  intro t ht
  exact False.elim ht

def Conjecture47Pattern (colours : ℕ → ℕ)
    (H : RelStructure (Marker.hypergraphLanguage colours) ℕ) : Prop :=
  ∀ phi : RelEmbedding H (Marker.originalValuationHypergraph colours),
    ∃ k : ℕ, ∀ R : ℕ,
      ∃ S : Finset (Node (Marker.Alphabet colours) 0),
        (S : Set (Node (Marker.Alphabet colours) 0)) ⊆ Set.range phi ∧ S.card = k ∧
          ∀ h, EnvelopedAt (Marker.Alphabet colours) (S : Set (Node (Marker.Alphabet colours) 0)) h → R ≤ h

/-- The precise envelope-height quantifier consequent is false, even without
requiring universality or the unboundedness of the number of relation symbols. -/
theorem conjecture47_pattern_false {colours : ℕ → ℕ}
    (H : RelStructure (Marker.hypergraphLanguage colours) ℕ) (hH : Marker.IsColouredHypergraph H) :
    ¬ Conjecture47Pattern colours H := by
  classical
  obtain ⟨phi, _, hphi⟩ := Marker.every_hypergraph_uniform_envelopes H hH
  intro hbad
  obtain ⟨k, hk⟩ := hbad phi
  obtain ⟨S, hsub, hcard, hlarge⟩ := hk (originalEnvelopeBound k + 1)
  by_cases hk0 : k = 0
  · have hS : S = ∅ := Finset.card_eq_zero.mp (hcard.trans hk0)
    have he : EnvelopedAt (Marker.Alphabet colours)
        (S : Set (Node (Marker.Alphabet colours) 0)) 0 := by
      rw [hS, Finset.coe_empty]
      exact empty_envelopedAt_zero _
    have h := hlarge 0 he
    omega
  · let T := S.preimage phi phi.injective.injOn
    have hfilter : S.filter (fun t => t ∈ Set.range phi) = S :=
      Finset.filter_eq_self.mpr (fun t ht => hsub ht)
    have himage : T.image phi = S := (Finset.image_preimage phi S phi.injective.injOn).trans hfilter
    have hTcard : T.card = k := (Finset.card_preimage S phi phi.injective.injOn).trans
      ((congrArg Finset.card hfilter).trans hcard)
    have hT : T.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨h, hbound, e, he, V, hV⟩ := hphi T hT
    have hbound' : h ≤ originalEnvelopeBound k := hTcard ▸ hbound
    have himageSet : phi '' (T : Set ℕ) = (S : Set (Node (Marker.Alphabet colours) 0)) := by
      rw [← Finset.coe_image, himage]
    have henv : EnvelopedAt (Marker.Alphabet colours)
        (S : Set (Node (Marker.Alphabet colours) 0)) h := by
      refine ⟨e, he, V, ?_⟩
      intro t ht
      apply hV 0 t
      exact Generated.generator t (himageSet.symm ▸ ht)
    have h := hlarge h henv
    omega

end CombinedRamsey.Positive
