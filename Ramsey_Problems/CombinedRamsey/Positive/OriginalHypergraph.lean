import CombinedRamsey.Positive.UniformEnvelopes
import RelationalRamsey632.Coding.SortedSupports
import RelationalRamsey632.Model

/-!
Literal original valuation-hypergraph semantics, with one genuine colour on
each support. Relation symbols at arity r >= 2 are Fin(n_r); zero and the
reserved value n_r+1 induce no relation, and height ties induce no relation.
-/

namespace CombinedRamsey.Positive.Marker

open RelationalRamsey632 RelationalRamsey632.Source RelationalRamsey632.Coding

variable (colours : ℕ → ℕ)

def hypergraphLanguage : Language where
  Rel r := {_R : Fin (colours (r - 1)) // 2 ≤ r}

instance hypergraphLanguage_positive : IsEmpty ((hypergraphLanguage colours).Rel 0) :=
  ⟨fun R => by have := R.property; omega⟩

instance hypergraphLanguage_finite_per_arity (r : ℕ) :
    Fintype ((hypergraphLanguage colours).Rel r) := inferInstanceAs (Fintype {_R : Fin _ // 2 ≤ r})

def nodeHeight (t : Node (Alphabet colours) 0) : ℕ := t.height

def valuationValue {r : ℕ} (u : Fin (r + 1) → Node (Alphabet colours) 0)
    (hu : StrictMono (nodeHeight colours ∘ u)) (hr : 0 < r) : ℕ :=
  ((u (Fin.last r)).table (lowerSupport (nodeHeight colours ∘ u) hu hr)).val

noncomputable def originalValuationHypergraph : RelStructure (hypergraphLanguage colours) (Node (Alphabet colours) 0) where
  rel {k} R t := match k with
    | 0 => False
    | 1 => False
    | r + 2 => Function.Injective t ∧
      ∃ u : Fin (r + 2) → Node (Alphabet colours) 0, ∃ sigma : Equiv.Perm (Fin (r + 2)),
      ∃ hu : StrictMono (nodeHeight colours ∘ u),
        t = u ∘ sigma ∧ valuationValue colours u hu (Nat.zero_lt_succ r) = R.val.val + 1

noncomputable def enumeratedHypergraph (c : ∀ v, GenuineColours colours v) :
    RelStructure (hypergraphLanguage colours) ℕ where
  rel {k} R t := match k with
    | 0 => False
    | 1 => False
    | r + 2 => Function.Injective t ∧
      ∃ u : Fin (r + 2) → ℕ, ∃ sigma : Equiv.Perm (Fin (r + 2)),
      ∃ hu : StrictMono u,
        t = u ∘ sigma ∧
          (c (u (Fin.last (r + 1))) (lowerSupport u hu (Nat.zero_lt_succ r))).val = R.val.val + 1

theorem mapped_lowerSupport (c : ∀ v, GenuineColours colours v)
    {r : ℕ} (u : Fin (r + 1) → ℕ) (hu : StrictMono u) (hr : 0 < r) :
    lowerSupport (nodeHeight colours ∘ family colours c ∘ u)
      ((originalHeight_strictMono colours).comp hu) hr = mapOriginal colours (lowerSupport u hu hr) := by
  apply Subtype.ext
  change Finset.univ.image (fun j : Fin r => originalHeight colours (u j.castSucc)) =
    (Finset.univ.image (fun j : Fin r => u j.castSucc)).image (originalHeight colours)
  rw [Finset.image_image]
  rfl

theorem valuationValue_coding (c : ∀ v, GenuineColours colours v)
    {r : ℕ} (u : Fin (r + 1) → ℕ) (hu : StrictMono u) (hr : 0 < r) :
    valuationValue colours (family colours c ∘ u) ((originalHeight_strictMono colours).comp hu) hr =
      (c (u (Fin.last r)) (lowerSupport u hu hr)).val := by
  unfold valuationValue
  rw [mapped_lowerSupport colours c u hu hr]
  exact original_value colours c _

theorem originalValuationHypergraph_injective :
    (originalValuationHypergraph colours).InjectiveRelations := by
  intro r R t _ ht
  cases r with
  | zero => exact False.elim ht
  | succ r =>
    cases r with
    | zero => exact False.elim ht
    | succ r => exact ht.1

theorem enumeratedHypergraph_injective (c : ∀ v, GenuineColours colours v) :
    (enumeratedHypergraph colours c).InjectiveRelations := by
  intro r R t _ ht
  cases r with
  | zero => exact False.elim ht
  | succ r =>
    cases r with
    | zero => exact False.elim ht
    | succ r => exact ht.1

theorem family_rel (c : ∀ v, GenuineColours colours v)
    {r : ℕ} (R : (hypergraphLanguage colours).Rel r) (t : Fin r → ℕ) :
    (enumeratedHypergraph colours c).rel R t ↔
      (originalValuationHypergraph colours).rel R (family colours c ∘ t) := by
  classical
  cases r with
  | zero => exact Iff.rfl
  | succ r =>
    cases r with
    | zero => exact Iff.rfl
    | succ r =>
      constructor
      · rintro ⟨ht, u, sigma, hu, htu, hc⟩
        refine ⟨(family_injective colours c).comp ht, family colours c ∘ u, sigma,
          (originalHeight_strictMono colours).comp hu, ?_, ?_⟩
        · rw [htu]; rfl
        · rw [valuationValue_coding colours c u hu]; exact hc
      · rintro ⟨_, w, sigma, hw, ht, hd⟩
        let u := t ∘ sigma.symm
        have hwu : w = family colours c ∘ u := by
          funext j
          have h := congrFun ht (sigma.symm j)
          simpa only [Function.comp_apply, Equiv.apply_symm_apply, u] using h.symm
        have hu : StrictMono u := by
          intro i j hij
          have h := hw hij
          rw [hwu] at h
          exact (originalHeight_strictMono colours).lt_iff_lt.mp h
        have htinj : Function.Injective t := by
          have hcomp : u ∘ sigma = t := by
            funext j
            exact congrArg t (sigma.symm_apply_apply j)
          rw [← hcomp]
          exact hu.injective.comp sigma.injective
        refine ⟨htinj, u, sigma, hu, ?_, ?_⟩
        · funext j
          exact (congrArg t (sigma.symm_apply_apply j)).symm
        · have hdc : valuationValue colours (family colours c ∘ u)
              ((originalHeight_strictMono colours).comp hu) (Nat.zero_lt_succ r) = R.val.val + 1 := by
            simpa only [hwu] using hd
          rw [valuationValue_coding colours c u hu] at hdc
          exact hdc

noncomputable def originalHypergraphEmbedding (c : ∀ v, GenuineColours colours v) :
    RelEmbedding (enumeratedHypergraph colours c) (originalValuationHypergraph colours) where
  toFun := family colours c
  injective := family_injective colours c
  map_rel := family_rel colours c

/-- Exact fixed ambient G_sigma, a genuine full relational embedding, and all-size closure bound. -/
theorem original_uniform_embedding (c : ∀ v, GenuineColours colours v) :
    ∃ phi : RelEmbedding (enumeratedHypergraph colours c) (originalValuationHypergraph colours),
      StrictMono (fun v => (phi v).height) ∧
      ∀ S : Finset ℕ, S.Nonempty →
        Nat.card (closureLevels (Alphabet colours) (phi '' (S : Set ℕ))) ≤
          CombinedRamsey.Positive.originalEnvelopeBound S.card := by
  classical
  refine ⟨originalHypergraphEmbedding colours c, originalHeight_strictMono colours, ?_⟩
  intro S hne
  have himage : (originalHypergraphEmbedding colours c) '' (S : Set ℕ) =
      (imageSet colours c S : Set (Node (Alphabet colours) 0)) :=
    (Finset.coe_image (s := S) (f := family colours c)).symm
  rw [himage]
  exact uniform_closure_level_bound colours c S hne

end CombinedRamsey.Positive.Marker
