import RelationalRamsey632.Model
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-! Actual ordered relation tables and all four guarded forbidden conditions. -/

namespace CombinedRamsey.Negative

inductive Unary
  | O | V | path | test | first | last
  deriving DecidableEq, Fintype

inductive Binary
  | E | N | Q | G | L | R
  deriving DecidableEq, Fintype

inductive State
  | zero | one | two
  deriving DecidableEq, Fintype

inductive Ternary
  | S (s : State) | UL | UR
  deriving DecidableEq, Fintype

inductive Symbol : ℕ → Type
  | unary (u : Unary) : Symbol 1
  | binary (b : Binary) : Symbol 2
  | ternary (t : Ternary) : Symbol 3

def language : RelationalRamsey632.Language := ⟨Symbol⟩

structure Table (X : Type) where
  unary : Unary → X → Prop
  binary : Binary → X → X → Prop
  ternary : Ternary → X → X → X → Prop

namespace Table

variable {X Y : Type}

def pullback (B : Table Y) (f : X → Y) : Table X where
  unary u x := B.unary u (f x)
  binary r x y := B.binary r (f x) (f y)
  ternary r x y z := B.ternary r (f x) (f y) (f z)

def toRel (B : Table X) : RelationalRamsey632.RelStructure language X where
  rel R t := match R with
    | .unary u => B.unary u (t 0)
    | .binary r => t 0 ≠ t 1 ∧ B.binary r (t 0) (t 1)
    | .ternary r => t 0 ≠ t 1 ∧ t 0 ≠ t 2 ∧ t 1 ≠ t 2 ∧
        B.ternary r (t 0) (t 1) (t 2)

theorem toRel_injective (B : Table X) : B.toRel.InjectiveRelations := by
  intro r R t _ ht i j he
  cases R with
  | unary u => exact Subsingleton.elim i j
  | binary b =>
    have h := ht.1
    fin_cases i <;> fin_cases j <;> simp_all [toRel]
  | ternary b =>
    have h01 := ht.1
    have h02 := ht.2.1
    have h12 := ht.2.2.1
    fin_cases i <;> fin_cases j <;> simp_all [toRel]

theorem finite_tables [Finite X] : Finite (Table X) := by
  classical
  let code : Table X → (Unary → X → Prop) ×
      (Binary → X → X → Prop) × (Ternary → X → X → X → Prop) :=
    fun B => (B.unary, B.binary, B.ternary)
  apply Finite.of_injective code
  intro A B h
  cases A
  cases B
  simp_all [code]

def Edge (B : Table X) (x y : X) : Prop :=
  x ≠ y ∧ B.binary .E x y ∧ B.binary .E y x

theorem edge_symm (B : Table X) {x y : X} (h : B.Edge x y) : B.Edge y x :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

def Complete3 (B : Table X) (a h v : X) : Prop :=
  B.Edge a h ∧ B.Edge a v ∧ B.Edge h v

def Complete4 (B : Table X) (a b h v : X) : Prop :=
  B.Edge a b ∧ B.Edge a h ∧ B.Edge a v ∧
  B.Edge b h ∧ B.Edge b v ∧ B.Edge h v

def ExactlyState (B : Table X) (a h v : X) : Prop :=
  ∃ s : State, B.ternary (.S s) a h v ∧
    ∀ t : State, B.ternary (.S t) a h v → t = s

def Transition (s t : State) : Prop :=
  (s = .zero ∧ t = .zero) ∨ (s = .zero ∧ t = .one) ∨
  (s = .one ∧ t = .two) ∨ (s = .two ∧ t = .two)

structure Legal (B : Table X) : Prop where
  states : ∀ a h v, B.Complete3 a h v →
    B.unary .O a → B.unary .path a → B.unary .V h → B.unary .V v →
    B.binary .Q h v → B.ExactlyState a h v ∧
      (B.unary .first a → B.ternary (.S .zero) a h v) ∧
      (B.unary .last a → B.ternary (.S .two) a h v)
  transition : ∀ a b h v, B.Complete4 a b h v →
    B.unary .O a → B.unary .path a → B.unary .O b → B.unary .path b →
    B.unary .V h → B.unary .V v → B.binary .N a b → B.binary .Q h v →
    ∀ s t, B.ternary (.S s) a h v → B.ternary (.S t) b h v → Transition s t
  bits : ∀ b a h v, B.Complete4 b a h v →
    B.unary .O b → B.unary .test b → B.unary .O a → B.unary .path a →
    B.unary .V h → B.unary .V v → B.binary .Q h v →
    (B.binary .L b a → (B.ternary .UL b h v ↔ B.ternary (.S .one) a h v)) ∧
    (B.binary .R b a → (B.ternary .UR b h v ↔ B.ternary (.S .one) a h v))
  conflict : ∀ b h v w, B.Complete4 b h v w →
    B.unary .O b → B.unary .test b →
    B.unary .V h → B.unary .V v → B.unary .V w →
    B.binary .Q h v → B.binary .Q h w → B.binary .G v w →
    ¬ (B.ternary .UL b h v ∧ B.ternary .UR b h w)

def PureDelta (B : Table X) : Prop :=
  ∀ x u, B.unary u x ↔ u = .V

theorem pureDelta_legal (B : Table X) (hB : B.PureDelta) : B.Legal := by
  have hO : ∀ x, ¬ B.unary .O x := fun x h => by simpa using (hB x .O).mp h
  constructor
  · intro a h v _ h _ _ _ _
    exact (hO a h).elim
  · intro a b h v _ h _ _ _ _ _ _ _ _ _ _ _
    exact (hO a h).elim
  · intro b a h v _ h _ _ _ _ _ _
    exact (hO b h).elim
  · intro b h v w _ h _ _ _ _ _ _ _
    exact (hO b h).elim

def Domain (B : Table X) (h v : X) : Prop := B.Edge h v ∧ B.binary .Q h v

def LocalArc (B : Table X) (h v w : X) : Prop :=
  B.Domain h v ∧ B.Domain h w ∧ B.Edge v w ∧ B.binary .G v w

end Table

structure Digraph (X : Type) where
  arc : X → X → Prop
  loopless : ∀ x, ¬ arc x x

structure Hom {X Y : Type} (G : Digraph X) (H : Digraph Y) where
  toFun : X → Y
  map_arc : ∀ x y, G.arc x y → H.arc (toFun x) (toFun y)

instance {X Y : Type} {G : Digraph X} {H : Digraph Y} :
    CoeFun (Hom G H) (fun _ => X → Y) := ⟨Hom.toFun⟩

def Hom.comp {X Y Z : Type} {G : Digraph X} {H : Digraph Y} {J : Digraph Z}
    (g : Hom H J) (f : Hom G H) : Hom G J where
  toFun := g ∘ f
  map_arc x y h := g.map_arc _ _ (f.map_arc x y h)

def Table.localGraph {X : Type} (B : Table X) (h : X) : Digraph {v // B.Domain h v} where
  arc v w := B.Edge v.val w.val ∧ B.binary .G v.val w.val
  loopless _ := fun h => h.1.1 rfl

def GoodColors {X : Type} {k : ℕ} (B : Table X) (H : Digraph (Fin k))
    (c : X → X → Fin k) : Prop :=
  ∀ h v w, B.LocalArc h v w → H.arc (c h v) (c h w)

theorem goodColors_iff_local_homs {X : Type} {k : ℕ} (hk : 0 < k)
    (B : Table X) (H : Digraph (Fin k)) :
    (∃ c, GoodColors B H c) ↔ ∀ h, Nonempty (Hom (B.localGraph h) H) := by
  classical
  constructor
  · rintro ⟨c, hc⟩ h
    exact ⟨⟨fun v => c h v, fun v w ha => hc h v w ⟨v.property, w.property, ha⟩⟩⟩
  · intro hf
    let f := fun h => Classical.choice (hf h)
    let c : X → X → Fin k := fun h v =>
      if hd : B.Domain h v then f h ⟨v, hd⟩ else ⟨0, hk⟩
    refine ⟨c, ?_⟩
    intro h v w ha
    simpa [c, ha.1, ha.2.1] using
      (f h).map_arc ⟨v, ha.1⟩ ⟨w, ha.2.1⟩ ha.2.2

end CombinedRamsey.Negative
