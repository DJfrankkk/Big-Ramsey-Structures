import CombinedRamsey.Negative.EncodingTables

/-! Faithful translation to the existing full relational embedding semantics. -/

namespace CombinedRamsey.Negative

open RelationalRamsey632

instance (r : ℕ) : Finite (Symbol r) := by
  classical
  let f : Symbol r → Unary ⊕ Binary ⊕ Ternary := fun s => match s with
    | .unary u => .inl u
    | .binary b => .inr (.inl b)
    | .ternary t => .inr (.inr t)
  apply Finite.of_injective f
  intro s t h
  cases s <;> cases t <;> simp_all [f]

theorem language_positive : language.Positive := ⟨fun s => nomatch s⟩

theorem language_finite : language.FinitePerArity := by
  intro r
  change Finite (Symbol r)
  infer_instance

theorem language_maximum_arity : ∀ r, 3 < r → IsEmpty (language.Rel r) := by
  intro r hr
  exact ⟨fun s => by cases s <;> omega⟩

namespace Table

variable {X Y : Type}

@[ext] theorem ext {A B : Table X}
    (hu : ∀ u x, A.unary u x ↔ B.unary u x)
    (hb : ∀ b x y, A.binary b x y ↔ B.binary b x y)
    (ht : ∀ t x y z, A.ternary t x y z ↔ B.ternary t x y z) : A = B := by
  cases A with
  | mk au ab atr =>
    cases B with
    | mk bu bb bt =>
      congr
      · funext u x; exact propext (hu u x)
      · funext b x y; exact propext (hb b x y)
      · funext t x y z; exact propext (ht t x y z)

def ofRel (A : RelStructure language X) : Table X where
  unary u x := A.rel (.unary u) ![x]
  binary b x y := A.rel (.binary b) ![x,y]
  ternary t x y z := A.rel (.ternary t) ![x,y,z]

def Canonical (B : Table X) : Prop :=
  (∀ r x y, B.binary r x y → x ≠ y) ∧
  (∀ r x y z, B.ternary r x y z → x ≠ y ∧ x ≠ z ∧ y ≠ z)

theorem ofRel_canonical (A : RelStructure language X) (hA : A.InjectiveRelations) :
    (ofRel A).Canonical := by
  constructor
  · intro r x y h hn
    have hi := hA 2 (.binary r) ![x,y] (by omega) h
    exact (by decide : (0 : Fin 2) ≠ 1) (hi hn)
  · intro r x y z h
    have hi := hA 3 (.ternary r) ![x,y,z] (by omega) h
    exact ⟨fun hn => (by decide : (0 : Fin 3) ≠ 1) (hi hn),
      fun hn => (by decide : (0 : Fin 3) ≠ 2) (hi hn),
      fun hn => (by decide : (1 : Fin 3) ≠ 2) (hi hn)⟩

theorem ofRel_toRel (B : Table X) (hB : B.Canonical) : ofRel B.toRel = B := by
  apply ext
  · intro u x; rfl
  · intro r x y
    change (x ≠ y ∧ B.binary r x y) ↔ B.binary r x y
    exact ⟨And.right, fun h => ⟨hB.1 r x y h, h⟩⟩
  · intro r x y z
    change (x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ B.ternary r x y z) ↔ B.ternary r x y z
    exact ⟨fun h => h.2.2.2, fun h =>
      ⟨(hB.2 r x y z h).1, (hB.2 r x y z h).2.1, (hB.2 r x y z h).2.2, h⟩⟩

theorem toRel_ofRel (A : RelStructure language X) (hA : A.InjectiveRelations) :
    (ofRel A).toRel = A := by
  apply RelStructure.ext_rel
  intro r R t
  cases R with
  | unary u =>
    have he : ![t 0] = t := by funext i; fin_cases i; rfl
    change A.rel (.unary u) ![t 0] ↔ A.rel (.unary u) t
    rw [he]
  | binary b =>
    have he : ![t 0,t 1] = t := by funext i; fin_cases i <;> rfl
    change (t 0 ≠ t 1 ∧ A.rel (.binary b) ![t 0,t 1]) ↔ A.rel (.binary b) t
    rw [he]
    constructor
    · exact And.right
    · intro ht
      refine ⟨?_, ht⟩
      intro hn
      have hi := hA 2 (.binary b) t (by omega) ht hn
      exact (by decide : (0 : Fin 2) ≠ 1) hi
  | ternary b =>
    have he : ![t 0,t 1,t 2] = t := by funext i; fin_cases i <;> rfl
    change (t 0 ≠ t 1 ∧ t 0 ≠ t 2 ∧ t 1 ≠ t 2 ∧
      A.rel (.ternary b) ![t 0,t 1,t 2]) ↔ A.rel (.ternary b) t
    rw [he]
    constructor
    · exact fun ht => ht.2.2.2
    · intro ht
      have hi := hA 3 (.ternary b) t (by omega) ht
      exact ⟨fun hn => (by decide : (0 : Fin 3) ≠ 1) (hi hn),
        fun hn => (by decide : (0 : Fin 3) ≠ 2) (hi hn),
        fun hn => (by decide : (1 : Fin 3) ≠ 2) (hi hn), ht⟩

theorem unary_map {A : Table X} {B : Table Y} (f : RelEmbedding A.toRel B.toRel)
    (u : Unary) (x : X) : A.unary u x ↔ B.unary u (f x) := by
  exact f.map_rel (.unary u) ![x]

theorem binary_full_map {A : Table X} {B : Table Y} (hA : A.Canonical) (hB : B.Canonical)
    (f : RelEmbedding A.toRel B.toRel) (r : Binary) (x y : X) :
    A.binary r x y ↔ B.binary r (f x) (f y) := by
  have he := congrArg (fun C : Table X => C.binary r x y)
    (ofRel_toRel A hA)
  have he' := congrArg (fun C : Table Y => C.binary r (f x) (f y))
    (ofRel_toRel B hB)
  have ht := f.map_rel (Symbol.binary r) ![x,y]
  have hv : f ∘ ![x,y] = ![f x,f y] := by funext i; fin_cases i <;> rfl
  rw [hv] at ht
  simpa only [ofRel, ← he, ← he'] using ht

theorem ternary_full_map {A : Table X} {B : Table Y} (hA : A.Canonical) (hB : B.Canonical)
    (f : RelEmbedding A.toRel B.toRel) (r : Ternary) (x y z : X) :
    A.ternary r x y z ↔ B.ternary r (f x) (f y) (f z) := by
  have he := congrArg (fun C : Table X => C.ternary r x y z)
    (ofRel_toRel A hA)
  have he' := congrArg (fun C : Table Y => C.ternary r (f x) (f y) (f z))
    (ofRel_toRel B hB)
  have ht := f.map_rel (Symbol.ternary r) ![x,y,z]
  have hv : f ∘ ![x,y,z] = ![f x,f y,f z] := by funext i; fin_cases i <;> rfl
  rw [hv] at ht
  simpa only [ofRel, ← he, ← he'] using ht

theorem binary_map {A : Table X} {B : Table Y} (f : RelEmbedding A.toRel B.toRel)
    (r : Binary) {x y : X} (hxy : x ≠ y) :
    A.binary r x y ↔ B.binary r (f x) (f y) := by
  have he := f.map_rel (.binary r) ![x,y]
  have hmap : f x ≠ f y := fun h => hxy (f.injective h)
  simpa [toRel, hxy, hmap] using he

theorem ternary_map {A : Table X} {B : Table Y} (f : RelEmbedding A.toRel B.toRel)
    (r : Ternary) {x y z : X} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    A.ternary r x y z ↔ B.ternary r (f x) (f y) (f z) := by
  have he := f.map_rel (.ternary r) ![x,y,z]
  have hmxy : f x ≠ f y := fun h => hxy (f.injective h)
  have hmxz : f x ≠ f z := fun h => hxz (f.injective h)
  have hmyz : f y ≠ f z := fun h => hyz (f.injective h)
  simpa [toRel, hxy, hxz, hyz, hmxy, hmxz, hmyz] using he

theorem edge_map {A : Table X} {B : Table Y} (f : RelEmbedding A.toRel B.toRel)
    {x y : X} : A.Edge x y ↔ B.Edge (f x) (f y) := by
  constructor
  · rintro ⟨hn, he, hr⟩
    exact ⟨fun h => hn (f.injective h), (binary_map f .E hn).mp he,
      (binary_map f .E hn.symm).mp hr⟩
  · rintro ⟨hn, he, hr⟩
    have hxy : x ≠ y := fun h => hn (congrArg f h)
    exact ⟨hxy, (binary_map f .E hxy).mpr he, (binary_map f .E hxy.symm).mpr hr⟩

theorem complete3_map {A : Table X} {B : Table Y} (f : RelEmbedding A.toRel B.toRel)
    {a h v : X} (hc : A.Complete3 a h v) : B.Complete3 (f a) (f h) (f v) :=
  ⟨(edge_map f).mp hc.1, (edge_map f).mp hc.2.1, (edge_map f).mp hc.2.2⟩

theorem complete4_map {A : Table X} {B : Table Y} (f : RelEmbedding A.toRel B.toRel)
    {a b h v : X} (hc : A.Complete4 a b h v) :
    B.Complete4 (f a) (f b) (f h) (f v) :=
  ⟨(edge_map f).mp hc.1, (edge_map f).mp hc.2.1, (edge_map f).mp hc.2.2.1,
    (edge_map f).mp hc.2.2.2.1, (edge_map f).mp hc.2.2.2.2.1,
    (edge_map f).mp hc.2.2.2.2.2⟩

theorem legal_of_embedding {A : Table X} {B : Table Y}
    (f : RelEmbedding A.toRel B.toRel) (hB : B.Legal) : A.Legal := by
  constructor
  · intro a h v hc hO hP hV hv hQ
    have ht := hB.states (f a) (f h) (f v) (complete3_map f hc)
      ((unary_map f .O a).mp hO) ((unary_map f .path a).mp hP)
      ((unary_map f .V h).mp hV) ((unary_map f .V v).mp hv)
      ((binary_map f .Q hc.2.2.1).mp hQ)
    have hmap : ∀ t, A.ternary (.S t) a h v ↔ B.ternary (.S t) (f a) (f h) (f v) :=
      fun t => ternary_map f (.S t) hc.1.1 hc.2.1.1 hc.2.2.1
    obtain ⟨s, hs, hu⟩ := ht.1
    refine ⟨⟨s, (hmap s).mpr hs, fun t h => hu t ((hmap t).mp h)⟩, ?_, ?_⟩
    · intro hf; exact (hmap .zero).mpr (ht.2.1 ((unary_map f .first a).mp hf))
    · intro hl; exact (hmap .two).mpr (ht.2.2 ((unary_map f .last a).mp hl))
  · intro a b h v hc hO hP hbO hbP hV hv hN hQ s t hs ht
    exact hB.transition (f a) (f b) (f h) (f v) (complete4_map f hc)
      ((unary_map f .O a).mp hO) ((unary_map f .path a).mp hP)
      ((unary_map f .O b).mp hbO) ((unary_map f .path b).mp hbP)
      ((unary_map f .V h).mp hV) ((unary_map f .V v).mp hv)
      ((binary_map f .N hc.1.1).mp hN) ((binary_map f .Q hc.2.2.2.2.2.1).mp hQ)
      s t ((ternary_map f (.S s) hc.2.1.1 hc.2.2.1.1 hc.2.2.2.2.2.1).mp hs)
      ((ternary_map f (.S t) hc.2.2.2.1.1 hc.2.2.2.2.1.1 hc.2.2.2.2.2.1).mp ht)
  · intro b a h v hc hO hT haO haP hV hv hQ
    have ht := hB.bits (f b) (f a) (f h) (f v) (complete4_map f hc)
      ((unary_map f .O b).mp hO) ((unary_map f .test b).mp hT)
      ((unary_map f .O a).mp haO) ((unary_map f .path a).mp haP)
      ((unary_map f .V h).mp hV) ((unary_map f .V v).mp hv)
      ((binary_map f .Q hc.2.2.2.2.2.1).mp hQ)
    constructor
    · intro hl
      exact (ternary_map f .UL hc.2.1.1 hc.2.2.1.1 hc.2.2.2.2.2.1).trans
        ((ht.1 ((binary_map f .L hc.1.1).mp hl)).trans
          (ternary_map f (.S .one) hc.2.2.2.1.1 hc.2.2.2.2.1.1 hc.2.2.2.2.2.1).symm)
    · intro hr
      exact (ternary_map f .UR hc.2.1.1 hc.2.2.1.1 hc.2.2.2.2.2.1).trans
        ((ht.2 ((binary_map f .R hc.1.1).mp hr)).trans
          (ternary_map f (.S .one) hc.2.2.2.1.1 hc.2.2.2.2.1.1 hc.2.2.2.2.2.1).symm)
  · intro b h v w hc hO hT hV hv hw hQ hQw hG hs
    exact hB.conflict (f b) (f h) (f v) (f w) (complete4_map f hc)
      ((unary_map f .O b).mp hO) ((unary_map f .test b).mp hT)
      ((unary_map f .V h).mp hV) ((unary_map f .V v).mp hv) ((unary_map f .V w).mp hw)
      ((binary_map f .Q hc.2.2.2.1.1).mp hQ)
      ((binary_map f .Q hc.2.2.2.2.1.1).mp hQw)
      ((binary_map f .G hc.2.2.2.2.2.1).mp hG)
      ⟨(ternary_map f .UL hc.1.1 hc.2.1.1 hc.2.2.2.1.1).mp hs.1,
        (ternary_map f .UR hc.1.1 hc.2.2.1.1 hc.2.2.2.2.1.1).mp hs.2⟩

def pullbackEmbedding (B : Table Y) (f : X → Y) (hf : Function.Injective f) :
    RelEmbedding (B.pullback f).toRel B.toRel where
  toFun := f
  injective := hf
  map_rel R t := by
    cases R with
    | unary u => rfl
    | binary b =>
      have he : f (t 0) ≠ f (t 1) ↔ t 0 ≠ t 1 := hf.ne_iff
      simp only [toRel, pullback, Function.comp_apply, he]
    | ternary b =>
      have h01 : f (t 0) ≠ f (t 1) ↔ t 0 ≠ t 1 := hf.ne_iff
      have h02 : f (t 0) ≠ f (t 2) ↔ t 0 ≠ t 2 := hf.ne_iff
      have h12 : f (t 1) ≠ f (t 2) ↔ t 1 ≠ t 2 := hf.ne_iff
      simp only [toRel, pullback, Function.comp_apply, h01, h02, h12]

theorem legal_pullback (B : Table Y) (f : X → Y) (hf : Function.Injective f)
    (hB : B.Legal) : (B.pullback f).Legal :=
  legal_of_embedding (pullbackEmbedding B f hf) hB

theorem toRel_pullback (B : Table Y) (f : X → Y) (hf : Function.Injective f) :
    (B.pullback f).toRel = B.toRel.pullback f :=
  (pullbackEmbedding B f hf).pullback_eq.symm

theorem ofRel_pullback (B : RelStructure language Y) (f : X → Y) :
    ofRel (B.pullback f) = (ofRel B).pullback f := by
  apply ext
  · intro u x
    have he : f ∘ ![x] = ![f x] := by funext i; fin_cases i; rfl
    change B.rel (.unary u) (f ∘ ![x]) ↔ B.rel (.unary u) ![f x]
    rw [he]
  · intro b x y
    have he : f ∘ ![x,y] = ![f x,f y] := by funext i; fin_cases i <;> rfl
    change B.rel (.binary b) (f ∘ ![x,y]) ↔ B.rel (.binary b) ![f x,f y]
    rw [he]
  · intro b x y z
    have he : f ∘ ![x,y,z] = ![f x,f y,f z] := by funext i; fin_cases i <;> rfl
    change B.rel (.ternary b) (f ∘ ![x,y,z]) ↔ B.rel (.ternary b) ![f x,f y,f z]
    rw [he]

theorem canonical_legal_iff (B : Table X) : (ofRel B.toRel).Legal ↔ B.Legal := by
  have he := toRel_ofRel B.toRel B.toRel_injective
  constructor
  · intro hB
    let f : RelEmbedding B.toRel (ofRel B.toRel).toRel := by
      rw [he]
      exact RelationalRamsey632.RelEmbedding.refl _
    exact legal_of_embedding f hB
  · intro hB
    let f : RelEmbedding (ofRel B.toRel).toRel B.toRel := by
      rw [he]
      exact RelationalRamsey632.RelEmbedding.refl _
    exact legal_of_embedding f hB

end Table

end CombinedRamsey.Negative
