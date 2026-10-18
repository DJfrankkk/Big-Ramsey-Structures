import RelationalRamsey632.Existence.OnePointStage

/-! Free amalgamation with an arbitrary finite one-point extension. -/

namespace RelationalRamsey632.Existence
namespace OnePointAmalgam

variable {L : Language} {X : Type} {n : ℕ}
variable (A : RelStructure L X) (B : RelStructure L (Fin (n + 1)))
variable (f : RelEmbedding (B.pullback Fin.castSucc) A)

def place : Fin (n + 1) → X ⊕ Unit :=
  Fin.lastCases (Sum.inr ()) (fun i => Sum.inl (f i))

@[simp] theorem place_old (i : Fin n) : place A B f i.castSucc = Sum.inl (f i) :=
  by simp [place]

@[simp] theorem place_new : place A B f (Fin.last n) = Sum.inr () :=
  by simp [place]

theorem place_injective : Function.Injective (place A B f) := by
  intro i
  revert i
  refine Fin.lastCases ?_ (fun a => ?_)
  · intro j
    refine Fin.lastCases ?_ (fun b => ?_) j
    · intro _
      rfl
    · intro h
      simp at h
  · intro j
    refine Fin.lastCases ?_ (fun b => ?_) j
    · intro h
      simp at h
    · intro h
      have hab : f a = f b := by simpa using h
      exact congrArg Fin.castSucc (f.injective hab)

theorem old_preimage {r : ℕ} (u : Fin r → X) (v : Fin r → Fin (n + 1))
    (h : Sum.inl ∘ u = place A B f ∘ v) :
    ∃ w : Fin r → Fin n, u = f ∘ w ∧ v = Fin.castSucc ∘ w := by
  classical
  have hw : ∀ i, ∃ j : Fin n, v i = j.castSucc ∧ u i = f j := by
    intro i
    have hp := congrFun h i
    by_cases hj : (v i).val < n
    · let j : Fin n := ⟨(v i).val, hj⟩
      have hvj : v i = j.castSucc := Fin.ext rfl
      refine ⟨j, hvj, ?_⟩
      simpa [hvj] using hp
    · have hvj : v i = Fin.last n := by
        apply Fin.ext
        have := (v i).isLt
        simp only [Fin.val_last]
        omega
      simp [hvj] at hp
  choose w hvw huw using hw
  exact ⟨w, funext huw, funext hvw⟩

def model : RelStructure L (X ⊕ Unit) where
  rel R t := (OnePointExtension.isolated A).rel R t ∨
    ∃ v : Fin _ → Fin (n + 1), place A B f ∘ v = t ∧ B.rel R v

theorem old_eq : (model A B f).pullback Sum.inl = A := by
  apply RelStructure.ext_rel
  intro r R u
  constructor
  · intro h
    rcases h with h | ⟨v, hv, hR⟩
    · have he := congrArg (fun Z : RelStructure L X => Z.rel R u)
        (OnePointExtension.isolated_old_eq A)
      exact (Iff.of_eq he).mp h
    · obtain ⟨w, huw, hvw⟩ := old_preimage A B f u v hv.symm
      rw [hvw] at hR
      have hbase : A.rel R (f ∘ w) := (f.map_rel R w).mp hR
      exact huw.symm ▸ hbase
  · intro h
    exact Or.inl ⟨u, rfl, h⟩

theorem model_admissible {inj : Bool} (hA : Admissible inj A) (hB : Admissible inj B) :
    Admissible inj (model A B f) := by
  intro hi r R t hr ht i j hij
  rcases ht with ht | ⟨v, hv, hR⟩
  · exact OnePointExtension.isolated_admissible hA hi r R t hr ht hij
  · apply hB hi r R v hr hR
    apply place_injective A B f
    exact (congrFun hv i).trans (hij.trans (congrFun hv j).symm)

theorem place_reflects {r : ℕ} (R : L.Rel r) (v : Fin r → Fin (n + 1)) :
    (model A B f).rel R (place A B f ∘ v) → B.rel R v := by
  intro h
  rcases h with ⟨u, hu, hR⟩ | ⟨w, hw, hR⟩
  · obtain ⟨w, huw, hvw⟩ := old_preimage A B f u v hu
    rw [huw] at hR
    have hB : (B.pullback Fin.castSucc).rel R w := (f.map_rel R w).mpr hR
    exact hvw.symm ▸ hB
  · have hwv : w = v := funext (fun i => place_injective A B f (congrFun hw i))
    exact hwv ▸ hR

def embedding : RelEmbedding B (model A B f) where
  toFun := place A B f
  injective := place_injective A B f
  map_rel R t := ⟨fun hR => Or.inr ⟨t, rfl, hR⟩, place_reflects A B f R t⟩

def extension {inj : Bool} (hA : Admissible inj A) (hB : Admissible inj B) :
    OnePointExtension inj A where
  model := model A B f
  old_eq := old_eq A B f
  admissible := model_admissible A B f hA hB

end OnePointAmalgam
end RelationalRamsey632.Existence
