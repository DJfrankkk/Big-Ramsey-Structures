import CombinedRamsey.Negative.EncodingTables
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Prime.Basic

/-! Actual directed cycles, their full homomorphism order, and unbounded
finite antichains obtained from proved Euclidean infinitude of primes. -/

namespace CombinedRamsey.Negative

def directedCycle (p : ℕ) (hp : 2 ≤ p) : Digraph (Fin p) where
  arc i j := j.val = (i.val+1) % p
  loopless i := by
    intro h
    by_cases hi : i.val+1 < p
    · rw [Nat.mod_eq_of_lt hi] at h
      omega
    · have he : i.val+1 = p := by omega
      rw [he, Nat.mod_self] at h
      omega

theorem mod_successor (n p : ℕ) (hp : 2 ≤ p) :
    (n % p + 1) % p = (n+1) % p := by
  rw [Nat.add_mod n 1 p, Nat.mod_eq_of_lt (show 1 < p by omega)]

def residue (p : ℕ) (hp : 0 < p) (n : ℕ) : Fin p := ⟨n % p,Nat.mod_lt _ hp⟩

theorem cycle_hom_values {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (f : Hom (directedCycle p hp) (directedCycle q hq)) :
    ∀ n, (f (residue p (by omega) n)).val =
      ((f (residue p (by omega) 0)).val+n) % q := by
  intro n
  induction n with
  | zero => simp [Nat.mod_eq_of_lt (f (residue p (by omega) 0)).isLt]
  | succ n ih =>
    have ha : (directedCycle p hp).arc (residue p (by omega) n)
        (residue p (by omega) (n+1)) := (mod_successor n p hp).symm
    have hf := f.map_arc _ _ ha
    change (f (residue p _ (n+1))).val = ((f (residue p _ n)).val+1) % q at hf
    rw [ih, mod_successor _ q hq] at hf
    simpa [Nat.add_assoc] using hf

theorem cycle_hom_implies_dvd {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (f : Hom (directedCycle p hp) (directedCycle q hq)) : q ∣ p := by
  have h := cycle_hom_values hp hq f p
  have hz : residue p (by omega) p = residue p (by omega) 0 := Fin.ext (by simp [residue])
  rw [hz] at h
  let a := (f (residue p (by omega) 0)).val
  have hmod : Nat.ModEq q (a+p) (a+0) := by
    change (a+p) % q = (a+0) % q
    simpa [a,Nat.mod_eq_of_lt (f (residue p (by omega) 0)).isLt] using h.symm
  exact Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_left_cancel' a hmod)

def cycleHomOfDvd {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (h : q ∣ p) :
    Hom (directedCycle p hp) (directedCycle q hq) where
  toFun i := residue q (by omega) i.val
  map_arc i j ha := by
    change j.val % q = (i.val % q+1) % q
    rw [ha, Nat.mod_mod_of_dvd _ h, mod_successor _ q hq]

theorem directed_cycle_hom_iff_dvd {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    Nonempty (Hom (directedCycle p hp) (directedCycle q hq)) ↔ q ∣ p :=
  ⟨fun h => cycle_hom_implies_dvd hp hq h.some, fun h => ⟨cycleHomOfDvd hp hq h⟩⟩

noncomputable def nextPrime (n : ℕ) : ℕ := Classical.choose (Nat.exists_infinite_primes (n+1))

theorem nextPrime_prime (n : ℕ) : Nat.Prime (nextPrime n) :=
  (Classical.choose_spec (Nat.exists_infinite_primes (n+1))).2

theorem nextPrime_gt (n : ℕ) : n < nextPrime n :=
  (Classical.choose_spec (Nat.exists_infinite_primes (n+1))).1

noncomputable def primeSequence : ℕ → ℕ
  | 0 => 2
  | n+1 => nextPrime (primeSequence n)

theorem primeSequence_prime (n : ℕ) : Nat.Prime (primeSequence n) := by
  cases n with
  | zero => exact Nat.prime_two
  | succ n => exact nextPrime_prime _

theorem primeSequence_strict : StrictMono primeSequence :=
  strictMono_nat_of_lt_succ (fun n => nextPrime_gt (primeSequence n))

noncomputable def primeCycle (n : ℕ) : Digraph (Fin (primeSequence n)) :=
  directedCycle (primeSequence n) (primeSequence_prime n).two_le

theorem prime_cycles_incomparable {i j : ℕ} (hij : i ≠ j) :
    ¬ Nonempty (Hom (primeCycle i) (primeCycle j)) := by
  intro h
  have hd := (directed_cycle_hom_iff_dvd (primeSequence_prime i).two_le
    (primeSequence_prime j).two_le).mp h
  have he := (Nat.prime_dvd_prime_iff_eq (primeSequence_prime j) (primeSequence_prime i)).mp hd
  exact hij (primeSequence_strict.injective he.symm)

end CombinedRamsey.Negative
