import CombinedRamsey.Positive.MarkerRecovery

namespace CombinedRamsey.Positive.Marker

open RelationalRamsey632.Source

variable {colours : ℕ → ℕ} {c : ∀ v, GenuineColours colours v}

theorem common_coordinate_val {i : ℕ} {s t : Node (Alphabet colours) i} {n : ℕ}
    (hcommon : Node.CommonHeight s t n) (hs : n ≤ s.height) (ht : n ≤ t.height)
    (q : Coordinate n) :
    (s.table (q.inclusion hs)).val = (t.table (q.inclusion ht)).val := by
  obtain ⟨hs', ht', he⟩ := hcommon
  have htable := Node.mk_injective n he
  exact congrArg Fin.val (congrFun htable q)

theorem positive_remainder_colors_equal
    {i v w n : ℕ} {s t : Node (Alphabet colours) i}
    (S : OriginalSliceRecord colours c v s) (T : OriginalSliceRecord colours c w t)
    (hs : originalHeight colours n < s.height) (ht : originalHeight colours n < t.height)
    (hi : i ≤ n) (hcommon : Node.CommonHeight s t (originalHeight colours n))
    (R : Coordinate (n + 1)) (hn : n ∈ R.val)
    (hpositive : 0 < (c v (S.remainderProfile hs R)).val) :
    (c v (S.remainderProfile hs R)).val = (c w (T.remainderProfile ht R)).val := by
  classical
  let a := (c v (S.remainderProfile hs R)).val
  let beta := markerForSupport colours R hn hi a hpositive (S.remainder_color_le hs R)
  have he := common_coordinate_val hcommon hs.le ht.le
    (Level.singletonCoordinate (markerPosition_lt_original colours beta))
  have hS := S.recovered_marker hs hi R hn a hpositive (S.remainder_color_le hs R)
  have hT := T.recovered_marker ht hi R hn a hpositive (S.remainder_color_le hs R)
  change (s.table (Level.singletonCoordinate ((markerPosition_lt_original colours beta).trans hs))).val =
    (t.table (Level.singletonCoordinate ((markerPosition_lt_original colours beta).trans ht))).val at he
  rw [hS, hT] at he
  have haa : (c v (S.remainderProfile hs R)).val = a := rfl
  rw [if_pos haa] at he
  by_contra hab
  have hba : (c w (T.remainderProfile ht R)).val ≠ a := by simpa only [a] using Ne.symm hab
  rw [if_neg hba] at he
  omega

theorem remainder_colors_equal
    {i v w n : ℕ} {s t : Node (Alphabet colours) i}
    (S : OriginalSliceRecord colours c v s) (T : OriginalSliceRecord colours c w t)
    (hs : originalHeight colours n < s.height) (ht : originalHeight colours n < t.height)
    (hi : i ≤ n) (hcommon : Node.CommonHeight s t (originalHeight colours n))
    (R : Coordinate (n + 1)) (hn : n ∈ R.val) :
    (c v (S.remainderProfile hs R)).val = (c w (T.remainderProfile ht R)).val := by
  by_cases ha : 0 < (c v (S.remainderProfile hs R)).val
  · exact positive_remainder_colors_equal S T hs ht hi hcommon R hn ha
  · by_cases hb : 0 < (c w (T.remainderProfile ht R)).val
    · obtain ⟨hcs, hct, he⟩ := hcommon
      exact (positive_remainder_colors_equal T S ht hs hi ⟨hct, hcs, he.symm⟩ R hn hb).symm
    · omega

theorem remainder_color_zero
    {i v n m : ℕ} {s : Node (Alphabet colours) i}
    (S : OriginalSliceRecord colours c v s)
    (hs : originalHeight colours n < s.height) (hm : originalHeight colours n < m)
    (hi : i ≤ n) (hcommon : Node.CommonHeight s (Node.zero i m) (originalHeight colours n))
    (R : Coordinate (n + 1)) (hn : n ∈ R.val) :
    (c v (S.remainderProfile hs R)).val = 0 := by
  classical
  by_contra hneq
  have ha : 0 < (c v (S.remainderProfile hs R)).val := by omega
  let a := (c v (S.remainderProfile hs R)).val
  let beta := markerForSupport colours R hn hi a ha (S.remainder_color_le hs R)
  have he := common_coordinate_val hcommon hs.le hm.le
    (Level.singletonCoordinate (markerPosition_lt_original colours beta))
  have hS := S.recovered_marker hs hi R hn a ha (S.remainder_color_le hs R)
  change (s.table (Level.singletonCoordinate ((markerPosition_lt_original colours beta).trans hs))).val = 0 at he
  rw [hS, if_pos (show (c v (S.remainderProfile hs R)).val = a from rfl)] at he
  omega

end CombinedRamsey.Positive.Marker
