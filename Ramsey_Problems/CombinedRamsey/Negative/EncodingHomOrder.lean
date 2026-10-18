import CombinedRamsey.Negative.EncodingNecessity
import CombinedRamsey.Negative.EncodingRelational

/-! The induced realization-age order contains the actual directed-graph hom order. -/

namespace CombinedRamsey.Negative

variable {k k' : ℕ}

def HasCompletion (H : Digraph (Fin k)) {X : Type} (B : Table X) : Prop :=
  ∃ Y, Y.Legal ∧ Completion H B Y

def CompletionAgeInclusion (H : Digraph (Fin k)) (H' : Digraph (Fin k')) : Prop :=
  ∀ (X : Type) [Finite X] (B : Table X), HasCompletion H B → HasCompletion H' B

def hubTable (H : Digraph (Fin k)) : Table (Unit ⊕ Fin k) where
  unary u _ := u = .V
  binary r x y := match r, x, y with
    | .E, x, y => x ≠ y
    | .Q, .inl _, .inr _ => True
    | .G, .inr v, .inr w => H.arc v w
    | _, _, _ => False
  ternary _ _ _ _ := False

theorem hubTable_delta (H : Digraph (Fin k)) : (hubTable H).PureDelta :=
  fun _ _ => Iff.rfl

theorem hubTable_canonical (H : Digraph (Fin k)) : (hubTable H).Canonical := by
  constructor
  · intro r x y h
    cases r with
    | E => exact h
    | Q => cases x <;> cases y <;> simp_all [hubTable]
    | G =>
      cases x with
      | inl x => cases y <;> simp [hubTable] at h
      | inr x =>
        cases y with
        | inl y => simp [hubTable] at h
        | inr y =>
          intro hn
          have he := Sum.inr.inj hn
          exact H.loopless x (he ▸ h)
    | N => cases x <;> cases y <;> simp [hubTable] at h
    | L => cases x <;> cases y <;> simp [hubTable] at h
    | R => cases x <;> cases y <;> simp [hubTable] at h
  · intro r x y z h
    exact h.elim

theorem hubTable_domain (H : Digraph (Fin k)) (v : Fin k) :
    (hubTable H).Domain (.inl ()) (.inr v) := by
  simp [Table.Domain, Table.Edge, hubTable]

def hubHom (H : Digraph (Fin k)) : Hom H ((hubTable H).localGraph (.inl ())) where
  toFun v := ⟨.inr v, hubTable_domain H v⟩
  map_arc v w ha := by
    have hn : v ≠ w := fun h => H.loopless v (h ▸ ha)
    have hn' : (Sum.inr v : Unit ⊕ Fin k) ≠ Sum.inr w := fun h => hn (Sum.inr.inj h)
    exact ⟨⟨hn', hn', hn'.symm⟩, ha⟩

theorem hubTable_completion (hk : 0 < k) (H : Digraph (Fin k)) :
    HasCompletion H (hubTable H) := by
  let c : (Unit ⊕ Fin k) → (Unit ⊕ Fin k) → Fin k := fun _ v => match v with
    | .inl _ => ⟨0, hk⟩
    | .inr v => v
  have hc : GoodColors (hubTable H) H c := by
    intro h v w ha
    cases h with
    | inr h => cases v <;> simp [Table.LocalArc, Table.Domain, hubTable] at ha
    | inl h =>
      cases v with
      | inl v => simp [Table.LocalArc, Table.Domain, hubTable] at ha
      | inr v =>
        cases w with
        | inl w => simp [Table.LocalArc, Table.Domain, hubTable] at ha
        | inr w => exact ha.2.2.2
  exact ⟨completionTable H (hubTable H) c,
    completionTable_legal H (hubTable H) c (hubTable_delta H) hc,
    completionTable_completion H (hubTable H) c (hubTable_delta H)⟩

theorem completion_age_inclusion_of_hom (hk : 0 < k) (hk' : 0 < k')
    (H : Digraph (Fin k)) (H' : Digraph (Fin k')) (f : Hom H H') :
    CompletionAgeInclusion H H' := by
  intro X _ B hB
  have h := (legal_completion_iff hk H B).mp hB
  apply (legal_completion_iff hk' H' B).mpr
  refine ⟨h.1, ?_⟩
  intro hub
  exact ⟨f.comp (Classical.choice (h.2 hub))⟩

theorem hom_of_completion_age_inclusion (hk : 0 < k) (hk' : 0 < k')
    (H : Digraph (Fin k)) (H' : Digraph (Fin k'))
    (h : CompletionAgeInclusion H H') : Nonempty (Hom H H') := by
  have h' := h (Unit ⊕ Fin k) (hubTable H) (hubTable_completion hk H)
  have hh := ((legal_completion_iff hk' H' (hubTable H)).mp h').2 (.inl ())
  exact ⟨(Classical.choice hh).comp (hubHom H)⟩

theorem completion_age_hom_order (hk : 0 < k) (hk' : 0 < k')
    (H : Digraph (Fin k)) (H' : Digraph (Fin k')) :
    CompletionAgeInclusion H H' ↔ Nonempty (Hom H H') := by
  constructor
  · exact hom_of_completion_age_inclusion hk hk' H H'
  · rintro ⟨f⟩
    exact completion_age_inclusion_of_hom hk hk' H H' f

end CombinedRamsey.Negative
