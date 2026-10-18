import CombinedRamsey.Negative.PersistenceLinks

namespace CombinedRamsey.Negative

open RelationalRamsey632 RelationalRamsey632.Existence

variable {L : Language} {A B Y Z U : Type}

def anchoredTuple (anchor : A → U) (new : B → U)
    {r : ℕ} (p : LinkSymbol L A r) (t : Fin r → B) : Fin p.1.1 → U :=
  Sum.elim anchor (new ∘ t) ∘ p.2.val

def AnchoredLinks (M : RelStructure L U) (anchor : A → U) (new : B → U) :
    RelStructure (LinkLanguage L A) B where
  rel p t := M.rel p.1.2 (anchoredTuple anchor new p t)

def AgeSharedFree {X : Type} (K : RelStructure L X) : Prop :=
  ∀ (B Y Z : Type) [Finite B] [Finite Y] [Finite Z]
    (ML : RelStructure L (B ⊕ Y)) (MR : RelStructure L (B ⊕ Z)),
    ML.pullback Sum.inl = MR.pullback Sum.inl →
    Nonempty (RelEmbedding ML K) → Nonempty (RelEmbedding MR K) →
    Nonempty (RelEmbedding (SharedBaseAmalgam.model ML MR) K)

theorem ageFree_of_sharedFree (K : RelStructure L ℕ) (h : AgeSharedFree K) :
    AgeFreeAmalgamation K := by
  intro A B C _ _ _ a b c f g hb hc
  obtain ⟨eb⟩ := hb
  obtain ⟨ec⟩ := hc
  apply h A (FreeAmalgamation.Complement f) (FreeAmalgamation.Complement g)
    (FreeAmalgamation.splitModel f) (FreeAmalgamation.splitModel g)
    (FreeAmalgamation.base_eq f g)
  · exact ⟨eb.comp (RelEmbedding.pullback b (FreeAmalgamation.split f)
      (FreeAmalgamation.split f).injective)⟩
  · exact ⟨ec.comp (RelEmbedding.pullback c (FreeAmalgamation.split g)
      (FreeAmalgamation.split g).injective)⟩

theorem realization_lifts_into_structure {X V : Type} {n : ℕ}
    {t : RelStructure L (Fin n ⊕ Unit)} {K : RelStructure L X}
    {b : RelEmbedding (t.pullback Sum.inl) K}
    {M : RelStructure L V} (e : RelEmbedding M K)
    (anchor : RelEmbedding (t.pullback Sum.inl) M)
    (ha : ∀ a, e (anchor a) = b a) (u : V)
    (hu : e u ∈ Realizations t K b) : u ∈ Realizations t M anchor := by
  obtain ⟨p, hp, hs⟩ := hu
  let q : Fin n ⊕ Unit → V := Sum.elim anchor (fun _ => u)
  have heq : e ∘ q = p := by
    funext x
    cases x with
    | inl a => exact (ha a).trans (hp a).symm
    | inr a => exact hs.symm
  let v : RelEmbedding t M := {
    toFun := q
    injective := by
      intro x y hxy
      apply p.injective
      exact (congrFun heq x).symm.trans ((congrArg e hxy).trans (congrFun heq y))
    map_rel := by
      intro r R w
      have ht : e ∘ q ∘ w = p ∘ w := by rw [← Function.comp_assoc, heq]
      exact (p.map_rel R w).trans (ht ▸ (e.map_rel R (q ∘ w)).symm) }
  exact ⟨v, fun _ => rfl, rfl⟩

namespace LinkedShared

variable (ML : RelStructure L ((A ⊕ B) ⊕ Y))
    (MR : RelStructure L ((A ⊕ B) ⊕ Z))

def anchorLeft (a : A) : (A ⊕ B) ⊕ Y := Sum.inl (Sum.inl a)
def anchorRight (a : A) : (A ⊕ B) ⊕ Z := Sum.inl (Sum.inl a)
def newLeft : B ⊕ Y → (A ⊕ B) ⊕ Y := Sum.map Sum.inr id
def newRight : B ⊕ Z → (A ⊕ B) ⊕ Z := Sum.map Sum.inr id
def anchorWhole (a : A) : (A ⊕ B) ⊕ (Y ⊕ Z) := Sum.inl (Sum.inl a)
def newWhole : B ⊕ (Y ⊕ Z) → (A ⊕ B) ⊕ (Y ⊕ Z) := Sum.map Sum.inr id

def leftModel := AnchoredLinks ML anchorLeft newLeft
def rightModel := AnchoredLinks MR anchorRight newRight

theorem left_commute {r : ℕ} (p : LinkSymbol L A r)
    (t : Fin r → B ⊕ (Y ⊕ Z)) (u : Fin r → B ⊕ Y)
    (hu : SharedBaseAmalgam.left ∘ u = t) :
    SharedBaseAmalgam.left ∘ anchoredTuple anchorLeft newLeft p u =
      anchoredTuple anchorWhole newWhole p t := by
  funext j
  change SharedBaseAmalgam.left (Sum.elim anchorLeft (newLeft ∘ u) (p.2.val j)) =
    Sum.elim anchorWhole (newWhole ∘ t) (p.2.val j)
  cases p.2.val j with
  | inl a => rfl
  | inr i =>
    have hi := congrFun hu i
    change SharedBaseAmalgam.left (newLeft (u i)) = newWhole (t i)
    rw [← hi]
    change SharedBaseAmalgam.left (newLeft (u i)) = newWhole (SharedBaseAmalgam.left (u i))
    cases u i <;> rfl

theorem right_commute {r : ℕ} (p : LinkSymbol L A r)
    (t : Fin r → B ⊕ (Y ⊕ Z)) (u : Fin r → B ⊕ Z)
    (hu : SharedBaseAmalgam.right ∘ u = t) :
    SharedBaseAmalgam.right ∘ anchoredTuple anchorRight newRight p u =
      anchoredTuple anchorWhole newWhole p t := by
  funext j
  change SharedBaseAmalgam.right (Sum.elim anchorRight (newRight ∘ u) (p.2.val j)) =
    Sum.elim anchorWhole (newWhole ∘ t) (p.2.val j)
  cases p.2.val j with
  | inl a => rfl
  | inr i =>
    have hi := congrFun hu i
    change SharedBaseAmalgam.right (newRight (u i)) = newWhole (t i)
    rw [← hi]
    change SharedBaseAmalgam.right (newRight (u i)) = newWhole (SharedBaseAmalgam.right (u i))
    cases u i <;> rfl

/-- Lifting the free amalgam of linked structures is the original free
amalgam over the named base together with the shared new vertices. -/
theorem linked_shared_free :
    AnchoredLinks (SharedBaseAmalgam.model ML MR) anchorWhole newWhole =
      SharedBaseAmalgam.model (leftModel ML) (rightModel MR) := by
  classical
  apply RelStructure.ext_rel
  intro r p t
  constructor
  · rintro (⟨u, hu, hR⟩ | ⟨u, hu, hR⟩)
    · have hshape : ∀ i, ∃ x : B ⊕ Y, SharedBaseAmalgam.left x = t i := by
        intro i
        obtain ⟨j, hj⟩ := p.2.property i
        have hji := congrFun hu j
        change SharedBaseAmalgam.left (u j) =
          Sum.elim anchorWhole (newWhole ∘ t) (p.2.val j) at hji
        rw [hj] at hji
        cases ht : t i with
        | inl b => exact ⟨Sum.inl b, rfl⟩
        | inr yz =>
          cases yz with
          | inl y => exact ⟨Sum.inr y, rfl⟩
          | inr z =>
            change SharedBaseAmalgam.left (u j) = newWhole (t i) at hji
            rw [ht] at hji
            cases huj : u j <;> simp [SharedBaseAmalgam.left, newWhole, huj] at hji
      choose v hv using hshape
      have hvt : SharedBaseAmalgam.left ∘ v = t := funext hv
      have htu := left_commute p t v hvt
      have heq : anchoredTuple anchorLeft newLeft p v = u := by
        funext j
        exact SharedBaseAmalgam.left_injective ((congrFun htu j).trans (congrFun hu j).symm)
      refine Or.inl ⟨v, hvt, ?_⟩
      change ML.rel p.1.2 (anchoredTuple anchorLeft newLeft p v)
      rw [heq]
      exact hR
    · have hshape : ∀ i, ∃ x : B ⊕ Z, SharedBaseAmalgam.right x = t i := by
        intro i
        obtain ⟨j, hj⟩ := p.2.property i
        have hji := congrFun hu j
        change SharedBaseAmalgam.right (u j) =
          Sum.elim anchorWhole (newWhole ∘ t) (p.2.val j) at hji
        rw [hj] at hji
        cases ht : t i with
        | inl b => exact ⟨Sum.inl b, rfl⟩
        | inr yz =>
          cases yz with
          | inr z => exact ⟨Sum.inr z, rfl⟩
          | inl y =>
            change SharedBaseAmalgam.right (u j) = newWhole (t i) at hji
            rw [ht] at hji
            cases huj : u j <;> simp [SharedBaseAmalgam.right, newWhole, huj] at hji
      choose v hv using hshape
      have hvt : SharedBaseAmalgam.right ∘ v = t := funext hv
      have htu := right_commute p t v hvt
      have heq : anchoredTuple anchorRight newRight p v = u := by
        funext j
        exact SharedBaseAmalgam.right_injective ((congrFun htu j).trans (congrFun hu j).symm)
      refine Or.inr ⟨v, hvt, ?_⟩
      change MR.rel p.1.2 (anchoredTuple anchorRight newRight p v)
      rw [heq]
      exact hR
  · rintro (⟨u, hu, hR⟩ | ⟨u, hu, hR⟩)
    · exact Or.inl ⟨anchoredTuple anchorLeft newLeft p u, left_commute p t u hu, hR⟩
    · exact Or.inr ⟨anchoredTuple anchorRight newRight p u, right_commute p t u hu, hR⟩

end LinkedShared

end CombinedRamsey.Negative
