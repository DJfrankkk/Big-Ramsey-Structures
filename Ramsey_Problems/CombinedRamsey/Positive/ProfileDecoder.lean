import RelationalRamsey632.Coding.Profiles
import RelationalRamsey632.Coding.SortedSupports
import CombinedRamsey.Positive.MarkerFamily
import RelationalRamsey632.Source.RelationalModel
import RelationalRamsey632.Existence.ExtensionConsequences

/-! Actual decoding of all relation profiles on labelled nodes.  Height
ties and repeated vertices force positive-arity relations to be false. -/

namespace CombinedRamsey.Positive.Relational

open RelationalRamsey632 RelationalRamsey632.Source RelationalRamsey632.Coding

variable (L : Language) [∀ r, Fintype (L.Rel r)]


noncomputable def profileColours (r : ℕ) : ℕ := profileSize L r - 1

@[simp] theorem profileColours_add_one (r : ℕ) : profileColours L r + 1 = profileSize L r := by
  have h := profileSize_positive L r
  unfold profileColours
  omega

@[simp] theorem profileColours_add_two (r : ℕ) : profileColours L r + 2 = profileSize L r + 1 := by
  rw [← profileColours_add_one L r]

noncomputable def decodeProfile (r : ℕ) (a : Marker.Alphabet (profileColours L) r) : Profile L r :=
  if h : a.val < profileSize L r then (profileCode L r).symm ⟨a.val, h⟩
  else falseProfile L r

def embedCode (r : ℕ) (_hr : 0 < r) (a : Fin (profileSize L r)) :
    Marker.Alphabet (profileColours L) r :=
  ⟨a.val, by rw [profileColours_add_two]; exact a.isLt.trans_le (Nat.le_succ _)⟩

@[simp] theorem decodeProfile_embedCode (r : ℕ) (hr : 0 < r) (p : Profile L r) :
    decodeProfile L r (embedCode L r hr (profileCode L r p)) = p := by
  simp only [decodeProfile, embedCode, dif_pos (profileCode L r p).isLt]
  exact (profileCode L r).symm_apply_apply p

abbrev ProfileAlphabet := Marker.Alphabet (profileColours L)
abbrev DecoderVertex := UnaryProfile L × Node (ProfileAlphabet L) 0

noncomputable def relationCodes (K : RelStructure L ℕ) (v : ℕ) :
    Marker.GenuineColours (profileColours L) v := fun s =>
  ⟨(profileCode L s.val.card (profileAt L K s.val.card (supportTuple v s))).val, by
    have hp := (profileCode L s.val.card (profileAt L K s.val.card (supportTuple v s))).isLt
    simpa only [profileColours_add_one] using hp⟩

noncomputable def codingMap (K : RelStructure L ℕ) (v : ℕ) : DecoderVertex L :=
  (unaryAt L K v, Marker.family (profileColours L) (relationCodes L K) v)

@[simp] theorem codingMap_height (K : RelStructure L ℕ) (v : ℕ) :
    (codingMap L K v).2.height = Marker.originalHeight (profileColours L) v := rfl

theorem codingMap_injective (K : RelStructure L ℕ) : Function.Injective (codingMap L K) := by
  intro v w h
  exact (Marker.originalHeight_strictMono (profileColours L)).injective
    (congrArg (fun z : DecoderVertex L => z.2.height) h)

theorem codingMap_strictHeights (K : RelStructure L ℕ) {r : ℕ}
    (u : Fin r → ℕ) (hu : StrictMono u) :
    StrictMono (fun j => (codingMap L K (u j)).2.height) :=
  (Marker.originalHeight_strictMono (profileColours L)).comp hu

def decoderHeight (v : DecoderVertex L) : ℕ := v.2.height

def passingCoordinate {r : ℕ} (u : Fin (r + 1) → DecoderVertex L)
    (hu : StrictMono (decoderHeight L ∘ u)) (hr : 0 < r) :
    Coordinate (u (Fin.last r)).2.height := lowerSupport (decoderHeight L ∘ u) hu hr

theorem passingCoordinate_card {r : ℕ} (u : Fin (r + 1) → DecoderVertex L)
    (hu : StrictMono (decoderHeight L ∘ u)) (hr : 0 < r) :
    (passingCoordinate L u hu hr).val.card = r :=
  lowerSupport_card (decoderHeight L ∘ u) hu hr

noncomputable def passingValue {r : ℕ} (u : Fin (r + 1) → DecoderVertex L)
    (hu : StrictMono (decoderHeight L ∘ u)) (hr : 0 < r) : ProfileAlphabet L r :=
  cast (congrArg (ProfileAlphabet L) (by
    rw [Nat.zero_add, passingCoordinate_card]))
    ((u (Fin.last r)).2.table (passingCoordinate L u hu hr))

theorem alphabetCast_val {b : ℕ → ℕ} {i j : ℕ} (h : i = j) (x : Marker.Alphabet b i) :
    (cast (congrArg (Marker.Alphabet b) h) x).val = x.val := by
  cases h
  rfl

theorem passingValue_val {r : ℕ} (u : Fin (r + 1) → DecoderVertex L)
    (hu : StrictMono (decoderHeight L ∘ u)) (hr : 0 < r) :
    (passingValue L u hu hr).val =
      ((u (Fin.last r)).2.table (passingCoordinate L u hu hr)).val :=
  alphabetCast_val (by rw [Nat.zero_add, passingCoordinate_card]) _

noncomputable def decoder : RelStructure L (DecoderVertex L) where
  rel {k} R t := match k with
    | 0 => False
    | 1 => (t 0).1 R = true
    | r + 2 => Function.Injective t ∧
      ∃ u : Fin (r + 2) → DecoderVertex L,
      ∃ σ : Equiv.Perm (Fin (r + 2)),
      ∃ hu : StrictMono (decoderHeight L ∘ u),
        t = u ∘ σ ∧
        decodeProfile L (r + 1) (passingValue L u hu (Nat.zero_lt_succ r)) R σ = true

theorem decoder_injective : (decoder L).InjectiveRelations := by
  intro r R t hr ht
  cases r with
  | zero => omega
  | succ r =>
    cases r with
    | zero =>
      intro i j _
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      omega
    | succ r => exact ht.1

theorem passingCoordinate_coding {r : ℕ} (K : RelStructure L ℕ)
    (u : Fin (r + 1) → ℕ) (hu : StrictMono u) (hr : 0 < r) :
    passingCoordinate L (codingMap L K ∘ u) (codingMap_strictHeights L K u hu) hr =
      Marker.mapOriginal (profileColours L) (lowerSupport u hu hr) := by
  apply Subtype.ext
  change Finset.univ.image (fun j : Fin r => Marker.originalHeight (profileColours L) (u j.castSucc)) =
    (Finset.univ.image (fun j : Fin r => u j.castSucc)).image (Marker.originalHeight (profileColours L))
  rw [Finset.image_image]
  rfl

theorem passingValue_coding_val {r : ℕ} (K : RelStructure L ℕ)
    (u : Fin (r + 1) → ℕ) (hu : StrictMono u) (hr : 0 < r) :
    (passingValue L (codingMap L K ∘ u) (codingMap_strictHeights L K u hu) hr).val =
      (relationCodes L K (u (Fin.last r)) (lowerSupport u hu hr)).val := by
  rw [passingValue_val, passingCoordinate_coding]
  exact Marker.original_value (profileColours L) (relationCodes L K) (lowerSupport u hu hr)

theorem profileCode_cast_val (K : RelStructure L ℕ) {r q : ℕ} (h : q = r)
    (u : Fin (r + 1) → ℕ) :
    (profileCode L q (profileAt L K q
      (u ∘ Fin.cast (congrArg (fun k => k + 1) h)))).val =
      (profileCode L r (profileAt L K r u)).val := by
  cases h
  rfl

theorem relationCodes_sorted_val {r : ℕ} (K : RelStructure L ℕ)
    (u : Fin (r + 1) → ℕ) (hu : StrictMono u) (hr : 0 < r) :
    (relationCodes L K (u (Fin.last r)) (lowerSupport u hu hr)).val =
      (profileCode L r (profileAt L K r u)).val := by
  unfold relationCodes
  change (profileCode L (lowerSupport u hu hr).val.card
    (profileAt L K (lowerSupport u hu hr).val.card (supportTuple (u (Fin.last r)) (lowerSupport u hu hr)))).val = _
  rw [supportTuple_lowerSupport]
  exact profileCode_cast_val L K (lowerSupport_card u hu hr) u

theorem passingProfile_coding {r : ℕ} (K : RelStructure L ℕ)
    (u : Fin (r + 1) → ℕ) (hu : StrictMono u) (hr : 0 < r) :
    decodeProfile L r
      (passingValue L (codingMap L K ∘ u) (codingMap_strictHeights L K u hu) hr) =
        profileAt L K r u := by
  have hc : passingValue L (codingMap L K ∘ u) (codingMap_strictHeights L K u hu) hr =
      embedCode L r hr (profileCode L r (profileAt L K r u)) := by
    apply Fin.ext
    exact (passingValue_coding_val L K u hu hr).trans (relationCodes_sorted_val L K u hu hr)
  rw [hc, decodeProfile_embedCode]

theorem codingMap_rel [IsEmpty (L.Rel 0)] (K : RelStructure L ℕ)
    (hK : K.InjectiveRelations) {k : ℕ} (R : L.Rel k) (t : Fin k → ℕ) :
    K.rel R t ↔ (decoder L).rel R (codingMap L K ∘ t) := by
  classical
  cases k with
  | zero => exact isEmptyElim R
  | succ k =>
    cases k with
    | zero =>
      have ht : t = fun _ => t 0 := by
        funext j
        have hj : j = 0 := by
          apply Fin.ext
          omega
        rw [hj]
      change K.rel R t ↔ unaryAt L K (t 0) R = true
      rw [unaryAt_true, ht]
    | succ r =>
      constructor
      · intro h
        have ht := hK (r + 2) R t (by omega) h
        obtain ⟨u, σ, hu, htu⟩ := exists_sorted_tuple t ht
        refine ⟨(codingMap_injective L K).comp ht, codingMap L K ∘ u, σ,
          codingMap_strictHeights L K u hu, ?_, ?_⟩
        · rw [htu]
          rfl
        · rw [passingProfile_coding L K u hu (Nat.zero_lt_succ r)]
          exact (profileAt_true L K (r + 1) u R σ).mpr (htu ▸ h)
      · rintro ⟨_, w, σ, hw, ht, hd⟩
        let u := t ∘ σ.symm
        have hwu : w = codingMap L K ∘ u := by
          funext j
          have h := congrFun ht (σ.symm j)
          simpa only [Function.comp_apply, Equiv.apply_symm_apply, u] using h.symm
        have hu : StrictMono u := by
          intro i j hij
          apply (Marker.originalHeight_strictMono (profileColours L)).lt_iff_lt.mp
          have hh := hw hij
          simpa only [hwu, decoderHeight, Function.comp_apply, codingMap_height] using hh
        have hd' : decodeProfile L (r + 1)
            (passingValue L (codingMap L K ∘ u) (codingMap_strictHeights L K u hu)
              (Nat.zero_lt_succ r)) R σ = true := by
          simpa only [hwu] using hd
        rw [passingProfile_coding L K u hu (Nat.zero_lt_succ r)] at hd'
        have hh := (profileAt_true L K (r + 1) u R σ).mp hd'
        have hut : u ∘ σ = t := by
          funext j
          exact congrArg t (σ.symm_apply_apply j)
        exact hut ▸ hh

noncomputable def codingEmbedding [IsEmpty (L.Rel 0)] (K : RelStructure L ℕ)
    (hK : K.InjectiveRelations) : RelEmbedding K (decoder L) where
  toFun := codingMap L K
  injective := codingMap_injective L K
  map_rel := codingMap_rel L K hK

theorem decoderVertex_countable : Countable (DecoderVertex L) := by
  exact vertexCountable (ProfileAlphabet L) (UnaryProfile L)

noncomputable def returnEmbedding [IsEmpty (L.Rel 0)] (K : RelStructure L ℕ)
    (hEP : Existence.OnePointExtensionProperty true K) : RelEmbedding (decoder L) K := by
  haveI := decoderVertex_countable L
  exact Existence.countableEmbedding K hEP (decoder L) (fun _ => decoder_injective L)

theorem weakBiEmbedding [IsEmpty (L.Rel 0)] (K : RelStructure L ℕ)
    (hK : K.InjectiveRelations) (hEP : Existence.OnePointExtensionProperty true K) :
    Nonempty (RelEmbedding K (decoder L)) ∧ Nonempty (RelEmbedding (decoder L) K) :=
  ⟨⟨codingEmbedding L K hK⟩, ⟨returnEmbedding L K hEP⟩⟩

end CombinedRamsey.Positive.Relational


