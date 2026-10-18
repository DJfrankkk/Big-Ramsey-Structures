import RelationalRamsey632.Source.FaithfulSampling
import RelationalRamsey632.Source.Enumeration

/-! Compression is actual typed coordinate sampling, with a verified strictly
increasing enumeration of the retained levels. The fallback on off-grid
nodes is irrelevant to, and never used on, a retained closure. -/

namespace RelationalRamsey632.Source

noncomputable def compressOn {A : ℕ → Type} (e : ℕ → ℕ) (he : StrictMono e)
    {i : ℕ} (t : Node A i) : Node A i := by
  classical
  exact
  if h : ∃ n, t.height = e n then
    let n := Classical.choose h
    let u : Level A i (e n) :=
      cast (congrArg (Level A i) (Classical.choose_spec h)) t.table
    ⟨n, u.sample e he⟩
  else Node.root i

theorem compressCast_eq {A : ℕ → Type} (e : ℕ → ℕ) (he : StrictMono e)
    (i n k : ℕ) (h : e n = e k) (t : Level A i (e n)) :
    Node.mk k ((cast (congrArg (Level A i) h) t).sample e he) =
      Node.mk n (t.sample e he) := by
  have hk : k = n := he.injective h.symm
  subst k
  rfl

theorem compressOn_mk {A : ℕ → Type} (e : ℕ → ℕ) (he : StrictMono e)
    (i n : ℕ) (t : Level A i (e n)) :
    compressOn e he (Node.mk (e n) t) = Node.mk n (t.sample e he) := by
  have h : ∃ m, (Node.mk (e n) t : Node A i).height = e m := ⟨n, rfl⟩
  unfold compressOn
  rw [dif_pos h]
  dsimp only
  exact compressCast_eq e he i n (Classical.choose h) (Classical.choose_spec h) t

theorem compressOn_injective_on_closed {A : ℕ → Type}
    (e : ℕ → ℕ) (he : StrictMono e)
    (E : (i : ℕ) → Set (Node A i)) (L : Set ℕ)
    (hclosed : Closed A E L)
    (hgrid : ∀ i t, t ∈ E i → ∃ n, t.height = e n) (i : ℕ) :
    Set.InjOn (compressOn e he) (E i) := by
  intro s hs t ht h
  cases s with
  | mk a s =>
    cases t with
    | mk b t =>
      obtain ⟨n, hn⟩ := hgrid i (Node.mk a s) hs
      obtain ⟨m, hm⟩ := hgrid i (Node.mk b t) ht
      dsimp only [Node.height] at hn hm
      subst a
      subst b
      rw [compressOn_mk, compressOn_mk] at h
      have hnm : n = m := congrArg Node.height h
      subst m
      have hF := Node.mk_injective n h
      have hst := faithful_sampling he E L hclosed hgrid n i s t hs ht hF
      cases hst
      rfl

theorem compressOn_restrict_mk {A : ℕ → Type}
    (e : ℕ → ℕ) (he : StrictMono e) (i n m : ℕ)
    (t : Level A i (e n)) (hm : m ≤ n) :
    compressOn e he ((Node.mk (e n) t).restrict (e m) (he.monotone hm)) =
      (Node.mk n (t.sample e he)).restrict m hm := by
  change compressOn e he (Node.mk (e m) (t.restrict (he.monotone hm))) = _
  rw [compressOn_mk]
  exact congrArg (fun p : Level A i m => (Node.mk m p : Node A i))
    (Level.sample_restrict e he t hm).symm

theorem compressOn_slice_mk {A : ℕ → Type}
    (e : ℕ → ℕ) (he : StrictMono e) (i n m : ℕ)
    (t : Level A i (e n)) (hm : m < n) :
    compressOn e he ((Node.mk (e n) t).slice (e m) (he hm)) =
      (Node.mk n (t.sample e he)).slice m hm := by
  change compressOn e he (Node.mk (e m) (t.slice (he hm))) = _
  rw [compressOn_mk]
  exact congrArg (fun p : Level A (i + 1) m => (Node.mk m p : Node A (i + 1)))
    (Level.sample_slice e he t hm).symm

theorem compressOn_singleton_mk {A : ℕ → Type}
    (e : ℕ → ℕ) (he : StrictMono e) (i n m : ℕ)
    (t : Level A i (e n)) (hm : m < n) :
    (Node.mk n (t.sample e he)).singleton m hm =
      (Node.mk (e n) t).singleton (e m) (he hm) := by
  exact Level.sample_singleton e he t hm

noncomputable def canonicalCompression {A : ℕ → Type} (L : Finset ℕ)
    {i : ℕ} (t : Node A i) : Node A i :=
  compressOn (levelEnumeration L) (levelEnumeration_strictMono L) t

theorem closure_levels_on_grid {A : ℕ → Type} {X : Set (Node A 0)}
    (L : Finset ℕ) (hL : closureLevels A X = (L : Set ℕ)) :
    ∀ i t, t ∈ closureNodes A X i → ∃ n, t.height = levelEnumeration L n := by
  intro i t ht
  have hh : t.height ∈ L := by
    change t.height ∈ (L : Set ℕ)
    rw [← hL]
    exact Generated.height t ht
  exact levelEnumeration_range_contains L hh

theorem canonicalCompression_injective_on_closure {A : ℕ → Type}
    {X : Set (Node A 0)} (L : Finset ℕ)
    (hL : closureLevels A X = (L : Set ℕ)) (i : ℕ) :
    Set.InjOn (canonicalCompression L) (closureNodes A X i) :=
  compressOn_injective_on_closed (levelEnumeration L) (levelEnumeration_strictMono L)
    (closureNodes A X) (closureLevels A X)
    (generatedClosure_closed A X) (closure_levels_on_grid L hL) i

end RelationalRamsey632.Source
