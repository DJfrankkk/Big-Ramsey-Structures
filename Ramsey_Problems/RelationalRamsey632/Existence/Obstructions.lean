import RelationalRamsey632.Model
import Mathlib.Logic.Encodable.Basic
import Lean.Elab.Tactic.Omega

/-!
The two actual existence obstructions in the paper: independent diagonal
singleton bits in an infinite ordinary positive language, and incompatible
nullary truth values.  No type palette or generic existence is assumed.
-/

namespace RelationalRamsey632

namespace Language

abbrev PositiveSymbol (L : Language) := (r : {n : ℕ // 0 < n}) × L.Rel r.val

end Language

namespace Existence

variable (L : Language)

def ordinarySingleton (θ : L.Rel 0 → Prop) (b : L.PositiveSymbol → Prop) :
    RelStructure L Unit where
  rel {r} R _ := if hr : r = 0 then θ (hr ▸ R)
    else b ⟨⟨r, Nat.pos_of_ne_zero hr⟩, R⟩

@[simp] theorem ordinarySingleton_positive (θ : L.Rel 0 → Prop)
    (b : L.PositiveSymbol → Prop) (s : L.PositiveSymbol) (t : Fin s.1.val → Unit) :
    (ordinarySingleton L θ b).rel s.2 t ↔ b s := by
  simp [ordinarySingleton, Nat.ne_of_gt s.1.property]

@[simp] theorem ordinarySingleton_nullary (θ : L.Rel 0 → Prop)
    (b : L.PositiveSymbol → Prop) (R : L.Rel 0) (t : Fin 0 → Unit) :
    (ordinarySingleton L θ b).rel R t ↔ θ R := by
  simp [ordinarySingleton]

theorem singleton_profiles_equal_of_same_vertex {X : Type} (K : RelStructure L X)
    (θ : L.Rel 0 → Prop) (b c : L.PositiveSymbol → Prop)
    (e : RelEmbedding (ordinarySingleton L θ b) K)
    (f : RelEmbedding (ordinarySingleton L θ c) K) (h : e () = f ()) : b = c := by
  funext s
  apply propext
  let t : Fin s.1.val → Unit := fun _ => ()
  have he := e.map_rel s.2 t
  have hf := f.map_rel s.2 t
  have htuple : e ∘ t = f ∘ t := by
    funext i
    exact h
  rw [htuple] at he
  exact (ordinarySingleton_positive L θ b s t).symm.trans
    (he.trans (hf.symm.trans (ordinarySingleton_positive L θ c s t)))

def setProfile (i : ℕ ↪ L.PositiveSymbol) (S : Set ℕ) : L.PositiveSymbol → Prop :=
  fun s => ∃ n, i n = s ∧ n ∈ S

@[simp] theorem setProfile_apply (i : ℕ ↪ L.PositiveSymbol) (S : Set ℕ) (n : ℕ) :
    setProfile L i S (i n) ↔ n ∈ S := by
  constructor
  · rintro ⟨m, hm, hS⟩
    exact i.injective hm ▸ hS
  · intro hS
    exact ⟨n, rfl, hS⟩

theorem no_countable_ordinary_universal [Infinite L.PositiveSymbol]
    {X : Type} [Countable X] (K : RelStructure L X) (θ : L.Rel 0 → Prop) :
    ¬ ∀ b : L.PositiveSymbol → Prop,
      Nonempty (RelEmbedding (ordinarySingleton L θ b) K) := by
  classical
  intro hu
  let i : ℕ ↪ L.PositiveSymbol := Infinite.natEmbedding L.PositiveSymbol
  let e := fun b => Classical.choice (hu b)
  obtain ⟨k, hk⟩ := Countable.exists_injective_nat X
  let g : Set ℕ → ℕ := fun S => k (e (setProfile L i S) ())
  have hg : Function.Injective g := by
    intro S T h
    have hv : e (setProfile L i S) () = e (setProfile L i T) () := hk h
    have hb := singleton_profiles_equal_of_same_vertex L K θ
      (setProfile L i S) (setProfile L i T) (e _) (e _) hv
    ext n
    have hpn := congrFun hb (i n)
    exact (setProfile_apply L i S n).symm.trans
      ((Iff.of_eq hpn).trans (setProfile_apply L i T n))
  exact Function.cantor_injective g hg

def nullaryOnly (θ : L.Rel 0 → Prop) (X : Type) : RelStructure L X where
  rel {r} R _ := if hr : r = 0 then θ (hr ▸ R) else False

theorem nullaryOnly_injective (θ : L.Rel 0 → Prop) (X : Type) :
    (nullaryOnly L θ X).InjectiveRelations := by
  intro r R t hr ht
  simp [nullaryOnly, Nat.ne_of_gt hr] at ht

theorem nullary_preserved {X Y : Type} {A : RelStructure L X} {B : RelStructure L Y}
    (e : RelEmbedding A B) (Q : L.Rel 0) :
    A.rel Q Fin.elim0 ↔ B.rel Q Fin.elim0 := by
  have h := e.map_rel Q Fin.elim0
  have htuple : e ∘ Fin.elim0 = (Fin.elim0 : Fin 0 → Y) := by
    funext j
    exact Fin.elim0 j
  rw [htuple] at h
  exact h

theorem nullary_no_common_target (Q : L.Rel 0) {X : Type} (D : RelStructure L X) :
    ¬ (Nonempty (RelEmbedding (nullaryOnly L (fun R => R = Q) Unit) D) ∧
      Nonempty (RelEmbedding (nullaryOnly L (fun _ => False) Unit) D)) := by
  rintro ⟨⟨e⟩, ⟨f⟩⟩
  have he := nullary_preserved L e Q
  have hf := nullary_preserved L f Q
  have htrue : D.rel Q Fin.elim0 := he.mp (by simp [nullaryOnly])
  have hfalse : ¬ D.rel Q Fin.elim0 := by
    intro h
    have := hf.mpr h
    simp [nullaryOnly] at this
  exact hfalse htrue

end Existence

end RelationalRamsey632
