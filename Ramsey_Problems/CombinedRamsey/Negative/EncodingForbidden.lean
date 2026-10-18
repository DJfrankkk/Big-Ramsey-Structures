import CombinedRamsey.Negative.EncodingRelational

/-! The fixed finite forbidden family consists of all complete violating tables. -/

namespace CombinedRamsey.Negative

open RelationalRamsey632

def forbidden3 (B : Table (Fin 3)) : Prop :=
  B.Complete3 0 1 2 ∧ B.unary .O 0 ∧ B.unary .path 0 ∧
  B.unary .V 1 ∧ B.unary .V 2 ∧ B.binary .Q 1 2 ∧
  ¬ (B.ExactlyState 0 1 2 ∧
    (B.unary .first 0 → B.ternary (.S .zero) 0 1 2) ∧
    (B.unary .last 0 → B.ternary (.S .two) 0 1 2))

def forbidden4 (B : Table (Fin 4)) : Prop :=
  B.Complete4 0 1 2 3 ∧
  ((B.unary .O 0 ∧ B.unary .path 0 ∧ B.unary .O 1 ∧ B.unary .path 1 ∧
    B.unary .V 2 ∧ B.unary .V 3 ∧ B.binary .N 0 1 ∧ B.binary .Q 2 3 ∧
    ∃ s t, B.ternary (.S s) 0 2 3 ∧ B.ternary (.S t) 1 2 3 ∧ ¬ Table.Transition s t) ∨
  (B.unary .O 0 ∧ B.unary .test 0 ∧ B.unary .O 1 ∧ B.unary .path 1 ∧
    B.unary .V 2 ∧ B.unary .V 3 ∧ B.binary .Q 2 3 ∧
    ¬ ((B.binary .L 0 1 → (B.ternary .UL 0 2 3 ↔ B.ternary (.S .one) 1 2 3)) ∧
       (B.binary .R 0 1 → (B.ternary .UR 0 2 3 ↔ B.ternary (.S .one) 1 2 3)))) ∨
  (B.unary .O 0 ∧ B.unary .test 0 ∧ B.unary .V 1 ∧ B.unary .V 2 ∧ B.unary .V 3 ∧
    B.binary .Q 1 2 ∧ B.binary .Q 1 3 ∧ B.binary .G 2 3 ∧
    B.ternary .UL 0 1 2 ∧ B.ternary .UR 0 1 3))

abbrev ForbiddenFamily := {B : Table (Fin 3) // forbidden3 B} ⊕
  {B : Table (Fin 4) // forbidden4 B}

theorem forbiddenFamily_finite : Finite ForbiddenFamily := by
  letI := Table.finite_tables (X := Fin 3)
  letI := Table.finite_tables (X := Fin 4)
  infer_instance

def Forb {X : Type} (B : Table X) : Prop :=
  (∀ A : Table (Fin 3), forbidden3 A → ¬ Nonempty (RelEmbedding A.toRel B.toRel)) ∧
  (∀ A : Table (Fin 4), forbidden4 A → ¬ Nonempty (RelEmbedding A.toRel B.toRel))

theorem forbidden3_not_legal {B : Table (Fin 3)} (h : forbidden3 B) : ¬ B.Legal := by
  rintro hB
  exact h.2.2.2.2.2.2 (hB.states 0 1 2 h.1 h.2.1 h.2.2.1 h.2.2.2.1
    h.2.2.2.2.1 h.2.2.2.2.2.1)

theorem forbidden4_not_legal {B : Table (Fin 4)} (h : forbidden4 B) : ¬ B.Legal := by
  rintro hB
  rcases h.2 with ht | hb | hc
  · obtain ⟨hO,hP,haO,haP,hV,hv,hN,hQ,s,t,hs,htt,hnot⟩ := ht
    exact hnot (hB.transition 0 1 2 3 h.1 hO hP haO haP hV hv hN hQ s t hs htt)
  · obtain ⟨hO,hT,haO,haP,hV,hv,hQ,hnot⟩ := hb
    exact hnot (hB.bits 0 1 2 3 h.1 hO hT haO haP hV hv hQ)
  · obtain ⟨hO,hT,hV,hv,hw,hQ,hQw,hG,hs,hr⟩ := hc
    exact hB.conflict 0 1 2 3 h.1 hO hT hV hv hw hQ hQw hG ⟨hs,hr⟩

def CompleteAll {X : Type} (B : Table X) : Prop := ∀ x y, x ≠ y → B.Edge x y

theorem complete3_all {B : Table (Fin 3)} (h : B.Complete3 0 1 2) : CompleteAll B := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;>
    first | exact (hxy rfl).elim | exact h.1 | exact h.2.1 | exact h.2.2 |
      exact B.edge_symm h.1 | exact B.edge_symm h.2.1 | exact B.edge_symm h.2.2

theorem complete4_all {B : Table (Fin 4)} (h : B.Complete4 0 1 2 3) : CompleteAll B := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;>
    first | exact (hxy rfl).elim | exact h.1 | exact h.2.1 | exact h.2.2.1 |
      exact h.2.2.2.1 | exact h.2.2.2.2.1 | exact h.2.2.2.2.2 |
      exact B.edge_symm h.1 | exact B.edge_symm h.2.1 | exact B.edge_symm h.2.2.1 |
      exact B.edge_symm h.2.2.2.1 | exact B.edge_symm h.2.2.2.2.1 |
      exact B.edge_symm h.2.2.2.2.2

theorem forbidden3_complete {B : Table (Fin 3)} (h : forbidden3 B) : CompleteAll B :=
  complete3_all h.1

theorem forbidden4_complete {B : Table (Fin 4)} (h : forbidden4 B) : CompleteAll B :=
  complete4_all h.1

def Irreducible {L : Language} {X : Type} (A : RelStructure L X) : Prop :=
  ∀ x y, x ≠ y → ∃ (r : ℕ) (R : L.Rel r) (t : Fin r → X) (i j : Fin r),
    A.rel R t ∧ t i = x ∧ t j = y

theorem complete_irreducible {X : Type} {B : Table X} (h : CompleteAll B) :
    Irreducible B.toRel := by
  intro x y hxy
  exact ⟨2, Symbol.binary .E, ![x,y], 0, 1, ⟨hxy, (h x y hxy).2.1⟩, rfl, rfl⟩

theorem forbidden3_irreducible {B : Table (Fin 3)} (h : forbidden3 B) :
    Irreducible B.toRel := complete_irreducible (forbidden3_complete h)

theorem forbidden4_irreducible {B : Table (Fin 4)} (h : forbidden4 B) :
    Irreducible B.toRel := complete_irreducible (forbidden4_complete h)

theorem tuple3_injective {X : Type} {B : Table X} {a h v : X}
    (hc : B.Complete3 a h v) : Function.Injective ![a,h,v] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [Table.Complete3, Table.Edge]

theorem tuple4_injective {X : Type} {B : Table X} {a b h v : X}
    (hc : B.Complete4 a b h v) : Function.Injective ![a,b,h,v] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [Table.Complete4, Table.Edge]

theorem legal_iff_forb {X : Type} (B : Table X) : B.Legal ↔ Forb B := by
  classical
  constructor
  · intro hB
    constructor
    · intro A hA hf
      exact forbidden3_not_legal hA (Table.legal_of_embedding hf.some hB)
    · intro A hA hf
      exact forbidden4_not_legal hA (Table.legal_of_embedding hf.some hB)
  · intro hf
    constructor
    · intro a h v hc hO hP hV hv hQ
      by_contra hn
      let f : Fin 3 → X := ![a,h,v]
      have ha : forbidden3 (B.pullback f) := by
        exact ⟨⟨⟨by decide, hc.1.2⟩, ⟨by decide, hc.2.1.2⟩,
          ⟨by decide, hc.2.2.2⟩⟩, hO, hP, hV, hv, hQ, hn⟩
      exact hf.1 (B.pullback f) ha ⟨Table.pullbackEmbedding B f (tuple3_injective hc)⟩
    · intro a b h v hc hO hP hbO hbP hV hv hN hQ s t hs ht
      by_contra hn
      let f : Fin 4 → X := ![a,b,h,v]
      have ha : forbidden4 (B.pullback f) := by
        apply And.intro
        · exact ⟨⟨by decide, hc.1.2⟩, ⟨by decide, hc.2.1.2⟩,
            ⟨by decide, hc.2.2.1.2⟩, ⟨by decide, hc.2.2.2.1.2⟩,
            ⟨by decide, hc.2.2.2.2.1.2⟩, ⟨by decide, hc.2.2.2.2.2.2⟩⟩
        · left
          exact ⟨hO,hP,hbO,hbP,hV,hv,hN,hQ,s,t,hs,ht,hn⟩
      exact hf.2 (B.pullback f) ha ⟨Table.pullbackEmbedding B f (tuple4_injective hc)⟩
    · intro b a h v hc hO hT haO haP hV hv hQ
      by_contra hn
      let f : Fin 4 → X := ![b,a,h,v]
      have ha : forbidden4 (B.pullback f) := by
        apply And.intro
        · exact ⟨⟨by decide, hc.1.2⟩, ⟨by decide, hc.2.1.2⟩,
            ⟨by decide, hc.2.2.1.2⟩, ⟨by decide, hc.2.2.2.1.2⟩,
            ⟨by decide, hc.2.2.2.2.1.2⟩, ⟨by decide, hc.2.2.2.2.2.2⟩⟩
        · right; left
          exact ⟨hO,hT,haO,haP,hV,hv,hQ,hn⟩
      exact hf.2 (B.pullback f) ha ⟨Table.pullbackEmbedding B f (tuple4_injective hc)⟩
    · intro b h v w hc hO hT hV hv hw hQ hQw hG hs
      let f : Fin 4 → X := ![b,h,v,w]
      have ha : forbidden4 (B.pullback f) := by
        apply And.intro
        · exact ⟨⟨by decide, hc.1.2⟩, ⟨by decide, hc.2.1.2⟩,
            ⟨by decide, hc.2.2.1.2⟩, ⟨by decide, hc.2.2.2.1.2⟩,
            ⟨by decide, hc.2.2.2.2.1.2⟩, ⟨by decide, hc.2.2.2.2.2.2⟩⟩
        · right; right
          exact ⟨hO,hT,hV,hv,hw,hQ,hQw,hG,hs.1,hs.2⟩
      exact hf.2 (B.pullback f) ha ⟨Table.pullbackEmbedding B f (tuple4_injective hc)⟩

end CombinedRamsey.Negative
