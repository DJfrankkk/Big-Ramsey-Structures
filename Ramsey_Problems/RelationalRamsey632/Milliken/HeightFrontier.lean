import RelationalRamsey632.Milliken.HeightCanonicalAPI
import RelationalRamsey632.Milliken.PrefixExtension
import RelationalRamsey632.Milliken.ConeTrees

namespace RelationalRamsey632.Milliken.HeightFrontier

open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

def appendedIndex (e : ℕ → ℕ) (h m : ℕ) (n : ℕ) : ℕ :=
  if n < h then e n else m + (n - h)

theorem index_initial (e : ℕ → ℕ) (h m n : ℕ) (hn : n < h) :
    appendedIndex e h m n = e n := if_pos hn

@[simp] theorem index_last (e : ℕ → ℕ) (h m : ℕ) : appendedIndex e h m h = m := by
  simp [appendedIndex]

theorem index_strictMono (e : ℕ → ℕ) (he : StrictMono e) (h m : ℕ)
    (hm : e (h - 1) < m) : StrictMono (appendedIndex e h m) := by
  intro a b hab
  by_cases hb : b < h
  · rw [index_initial e h m a (hab.trans hb), index_initial e h m b hb]
    exact he hab
  · by_cases ha : a < h
    · rw [index_initial e h m a ha]
      have hb' : h ≤ b := Nat.le_of_not_gt hb
      have ha' : a ≤ h - 1 := by omega
      have hea := he.monotone ha'
      simp only [appendedIndex, if_neg hb]
      omega
    · simp only [appendedIndex, if_neg ha, if_neg hb]
      omega

variable {α : Type} [DecidableEq α] {R : α → α → Prop}
    (T : FiniteLevelTree α R) (e : ℕ → ℕ) (h k m : ℕ)
    (P : FiniteStrongPrefix T e h)

noncomputable def requiredAnchors : Finset (ConeAnchor T (k + 1)) := by
  classical
  exact Finset.univ.filter (fun a => ∃ u ∈ P.nodes (h - 1), R u a.val)

theorem mem_requiredAnchors (a : ConeAnchor T (k + 1)) :
    a ∈ requiredAnchors T e h k P ↔ ∃ u ∈ P.nodes (h - 1), R u a.val := by
  classical
  simp only [requiredAnchors, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def lastNodes (x : ConeAnchor T (k + 1) → α) : Finset α :=
  (requiredAnchors T e h k P).image x

noncomputable def appendedNodes (x : ConeAnchor T (k + 1) → α) (n : ℕ) : Finset α :=
  if n < h then P.nodes n else lastNodes T e h k P x

theorem nodes_initial (x : ConeAnchor T (k + 1) → α) (n : ℕ) (hn : n < h) :
    appendedNodes T e h k P x n = P.nodes n := if_pos hn

@[simp] theorem nodes_last (x : ConeAnchor T (k + 1) → α) :
    appendedNodes T e h k P x h = lastNodes T e h k P x := by
  simp only [appendedNodes, lt_self_iff_false, if_false]

noncomputable def appendPrefix (hh : 0 < h) (hLast : e (h - 1) = k)
    (x : ConeAnchor T (k + 1) → α)
    (hxLevel : ∀ a, x a ∈ T.nodes m) (hxCone : ∀ a, R a.val (x a)) (hkm : k < m) :
    FiniteStrongPrefix T (appendedIndex e h m) (h + 1) where
  index_strictMono := index_strictMono e P.index_strictMono h m (hLast ▸ hkm)
  nodes := appendedNodes T e h k P x
  root := P.root
  nodes_zero := by rw [nodes_initial T e h k P x 0 hh, P.nodes_zero]
  nodes_subset := by
    intro n hn
    by_cases hn' : n < h
    · rw [nodes_initial T e h k P x n hn', index_initial e h m n hn']
      exact P.nodes_subset n hn'
    · have hnh : n = h := by omega
      subst n
      rw [nodes_last, index_last]
      intro w hw
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hw
      exact hxLevel a
  parent := by
    intro n hn w hw
    by_cases hn' : n + 1 < h
    · rw [nodes_initial T e h k P x (n + 1) hn'] at hw
      obtain ⟨u, hu, huw⟩ := P.parent n hn' w hw
      exact ⟨u, by rw [nodes_initial T e h k P x n (by omega)]; exact hu, huw⟩
    · have hnh : n + 1 = h := by omega
      have hnl : n = h - 1 := by omega
      rw [hnh, nodes_last] at hw
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨u, hu, hua⟩ := (mem_requiredAnchors T e h k P a).mp ha
      exact ⟨u, by rw [nodes_initial T e h k P x n (by omega), hnl]; exact hu,
        T.rel_trans hua (hxCone a)⟩
  successor := by
    classical
    intro n hn u hu v hv huv
    have hn0 : n < h := by omega
    rw [nodes_initial T e h k P x n hn0] at hu
    rw [index_initial e h m n hn0] at hv
    by_cases hn' : n + 1 < h
    · rw [nodes_initial T e h k P x (n + 1) hn']
      exact P.successor n hn' u hu v hv huv
    · have hnh : n + 1 = h := by omega
      have hnl : n = h - 1 := by omega
      have hnk : e n = k := hnl ▸ hLast
      rw [hnk] at hv
      rw [hnh, nodes_last]
      let a : ConeAnchor T (k + 1) := ⟨v, hv⟩
      refine ⟨x a, ⟨?_, hxCone a⟩, ?_⟩
      · apply Finset.mem_image.mpr
        refine ⟨a, (mem_requiredAnchors T e h k P a).mpr ?_, rfl⟩
        exact ⟨u, hnl ▸ hu, huv⟩
      · intro w hw
        obtain ⟨a', _, rfl⟩ := Finset.mem_image.mp hw.1
        have haa : a = a' := by
          apply Subtype.ext
          exact T.node_eq_of_common_extension (k + 1) m v a'.val (x a')
            hv a'.property (hxLevel a') hw.2 (hxCone a')
        exact congrArg x haa.symm

theorem prefix_initial (hh : 0 < h) (hLast : e (h - 1) = k)
    (x : ConeAnchor T (k + 1) → α)
    (hxLevel : ∀ a, x a ∈ T.nodes m) (hxCone : ∀ a, R a.val (x a)) (hkm : k < m)
    (n : ℕ) (hn : n < h) :
    (appendPrefix T e h k m P hh hLast x hxLevel hxCone hkm).nodes n = P.nodes n :=
  nodes_initial T e h k P x n hn

theorem prefix_last (hh : 0 < h) (hLast : e (h - 1) = k)
    (x : ConeAnchor T (k + 1) → α)
    (hxLevel : ∀ a, x a ∈ T.nodes m) (hxCone : ∀ a, R a.val (x a)) (hkm : k < m) :
    (appendPrefix T e h k m P hh hLast x hxLevel hxCone hkm).nodes h =
      lastNodes T e h k P x := nodes_last T e h k P x

end RelationalRamsey632.Milliken.HeightFrontier

namespace RelationalRamsey632.Milliken.HeightFrontier

open RamseyCommon.SourceTrees
open RamseyCommon.SourceTrees.FiniteLevelTree

variable {I : Type} {α : I → Type} [∀ i, DecidableEq (α i)]
    {R : ∀ i, α i → α i → Prop} (T : ∀ i, FiniteLevelTree (α i) (R i))

noncomputable def synchronizedExtension (h k m : ℕ) (hh : 0 < h)
    (e : ℕ → ℕ) (he : StrictMono e) (hLast : e (h - 1) = k)
    (P : ∀ i, FiniteStrongPrefix (T i) e h)
    (x : ∀ i, ConeAnchor (T i) (k + 1) → α i)
    (hxLevel : ∀ i a, x i a ∈ (T i).nodes m)
    (hxCone : ∀ i a, R i a.val (x i a)) (hkm : k < m) : SynchronizedFrame T where
  index := appendedIndex e h m
  index_strictMono := index_strictMono e he h m (hLast ▸ hkm)
  frames i := (appendPrefix (T i) e h k m (P i) hh hLast (x i)
    (hxLevel i) (hxCone i) hkm).extend (Nat.zero_lt_succ h)
  frame_index _ := rfl

theorem synchronizedExtension_initial (h k m : ℕ) (hh : 0 < h)
    (e : ℕ → ℕ) (he : StrictMono e) (hLast : e (h - 1) = k)
    (P : ∀ i, FiniteStrongPrefix (T i) e h)
    (x : ∀ i, ConeAnchor (T i) (k + 1) → α i)
    (hxLevel : ∀ i a, x i a ∈ (T i).nodes m)
    (hxCone : ∀ i a, R i a.val (x i a)) (hkm : k < m) (i : I) (n : ℕ) (hn : n < h) :
    ((synchronizedExtension T h k m hh e he hLast P x hxLevel hxCone hkm).frames i).nodes n =
      (P i).nodes n := by
  dsimp only [synchronizedExtension]
  rw [FiniteStrongPrefix.extend_initial _ (Nat.zero_lt_succ h) n (by omega)]
  exact prefix_initial (T i) e h k m (P i) hh hLast (x i) (hxLevel i) (hxCone i) hkm n hn

theorem synchronizedExtension_last (h k m : ℕ) (hh : 0 < h)
    (e : ℕ → ℕ) (he : StrictMono e) (hLast : e (h - 1) = k)
    (P : ∀ i, FiniteStrongPrefix (T i) e h)
    (x : ∀ i, ConeAnchor (T i) (k + 1) → α i)
    (hxLevel : ∀ i a, x i a ∈ (T i).nodes m)
    (hxCone : ∀ i a, R i a.val (x i a)) (hkm : k < m) (i : I) :
    ((synchronizedExtension T h k m hh e he hLast P x hxLevel hxCone hkm).frames i).nodes h =
      lastNodes (T i) e h k (P i) (x i) := by
  dsimp only [synchronizedExtension]
  rw [FiniteStrongPrefix.extend_initial _ (Nat.zero_lt_succ h) h (Nat.lt_succ_self h)]
  exact prefix_last (T i) e h k m (P i) hh hLast (x i) (hxLevel i) (hxCone i) hkm

end RelationalRamsey632.Milliken.HeightFrontier
