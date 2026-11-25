import Std

set_option autoImplicit false

namespace YoctoCore.Properties.OrderRangeRing

variable {α : Type}

/-- Physical slot for a logical index in a ring of arbitrary positive capacity. -/
def position (cap head i : Nat) : Nat :=
  if i < cap - head then head + i else i - (cap - head)

/-- Only the active slots, in chronological order. -/
def toList (buf : List α) (head len : Nat) : List α :=
  ((buf.drop head) ++ (buf.take head)).take len

theorem position_lt {cap head i : Nat} (hh : head < cap) (hi : i < cap) :
    position cap head i < cap := by
  unfold position
  split <;> omega

theorem toList_length (buf : List α) {head len : Nat} (hh : head ≤ buf.length)
    (hl : len ≤ buf.length) : (toList buf head len).length = len := by
  simp only [toList, List.length_take, List.length_append, List.length_drop]
  omega

theorem toList_get (buf : List α) {head len i : Nat} (hh : head < buf.length)
    (hl : len ≤ buf.length) (hi : i < len) :
    (toList buf head len)[i]'(by rw [toList_length buf (Nat.le_of_lt hh) hl]; exact hi) =
      buf[position buf.length head i]'(position_lt hh (by omega)) := by
  unfold toList
  rw [List.getElem_take]
  by_cases h : i < buf.length - head
  · rw [List.getElem_append_left (by simpa using h), List.getElem_drop]
    simp only [position, ite_eq_left h]
  · rw [List.getElem_append_right (by simp; omega), List.getElem_take]
    simp only [position, ite_eq_right h, List.length_drop]

/-- A resize preserves the active sequence if it maps every logical index
    to the same element in the two physical buffers. -/
theorem resize_view (old new : List α) (head next len : Nat)
    (hh : head < old.length) (hn : next < new.length)
    (hl : len ≤ old.length) (hl' : len ≤ new.length)
    (slot : ∀ j < len, new[position new.length next j]? = old[position old.length head j]?) :
    toList new next len = toList old head len := by
  apply List.ext_getElem
  · rw [toList_length _ (Nat.le_of_lt hn) hl', toList_length _ (Nat.le_of_lt hh) hl]
  · intro j hj _
    have live : j < len := by rwa [toList_length _ (Nat.le_of_lt hn) hl'] at hj
    rw [toList_get _ hn hl' live, toList_get _ hh hl live]
    have hb := position_lt hn (Nat.lt_of_lt_of_le live hl')
    have ha := position_lt hh (Nat.lt_of_lt_of_le live hl)
    simpa only [List.getElem?_eq_getElem hb, List.getElem?_eq_getElem ha, Option.some.injEq] using slot j live

theorem lookup_padded (old padded : List α) (preserved : padded.take old.length = old)
    {j : Nat} (hj : j < old.length) : padded[j]? = old[j]? := by
  have h := congrArg (fun l : List α => l[j]?) preserved
  simpa [List.getElem?_take, hj] using h

theorem grow_view_contiguous (old padded : List α) (head len : Nat)
    (hh : head < old.length) (live : len ≤ old.length - head)
    (size : old.length ≤ padded.length) (pre : padded.take old.length = old) :
    toList padded head len = toList old head len := by
  apply resize_view old padded head head len hh (by omega) (by omega) (by omega)
  intro j hj
  have ho : j < old.length-head := by omega
  have hn : j < padded.length-head := by omega
  simpa only [position, ite_eq_left ho, ite_eq_left hn] using lookup_padded old padded pre (by omega : head+j < old.length)

theorem grow_view_low (old padded moved : List α) (head len : Nat)
    (hh : head < old.length) (hl : len ≤ old.length)
    (size : old.length ≤ padded.length) (enough : len - (old.length-head) ≤ padded.length-old.length)
    (pre : padded.take old.length = old) (sameSize : moved.length = padded.length)
    (slots : ∀ j : Nat, moved[j]? = padded[if old.length ≤ j ∧
      j < old.length + (len - (old.length - head)) then j-old.length else j]?) :
    toList moved head len = toList old head len := by
  apply resize_view old moved head head len hh (by omega) hl (by omega)
  intro j hj
  rw [slots]
  have equ : (if old.length ≤ position moved.length head j ∧
      position moved.length head j < old.length + (len-(old.length-head))
      then position moved.length head j - old.length else position moved.length head j) =
      position old.length head j := by
    unfold position
    by_cases ho : j < old.length-head <;> have hn : j < moved.length-head := by omega
    all_goals simp only [ho, hn, ↓reduceIte]; split <;> omega
  rw [equ]
  exact lookup_padded old padded pre (position_lt hh (by omega))

theorem grow_view_high (old padded moved : List α) (head len added : Nat)
    (hh : head < old.length) (hl : len ≤ old.length)
    (size : old.length+added = padded.length) (pre : padded.take old.length = old)
    (sameSize : moved.length = padded.length)
    (slots : ∀ j : Nat, moved[j]? = padded[if head+added ≤ j ∧ j < old.length+added then j-added else j]?) :
    toList moved (head+added) len = toList old head len := by
  apply resize_view old moved head (head+added) len hh (by omega) hl (by omega)
  intro j hj
  rw [slots]
  have equ : (if head+added ≤ position moved.length (head+added) j ∧
      position moved.length (head+added) j < old.length+added
      then position moved.length (head+added) j - added else position moved.length (head+added) j) =
      position old.length head j := by
    have tail : moved.length-(head+added) = old.length-head := by omega
    unfold position
    rw [tail]
    by_cases ho : j < old.length-head <;> simp only [ho, ↓reduceIte] <;> split <;> omega
  rw [equ]
  exact lookup_padded old padded pre (position_lt hh (by omega))

theorem toList_initial (buf : List α) (len : Nat) :
    toList buf 0 len = buf.take len := by simp [toList]

theorem toList_mem_iff (buf : List α) {head len : Nat} (hh : head < buf.length)
    (hl : len ≤ buf.length) (r : α) :
    r ∈ toList buf head len ↔
      ∃ (i : Nat) (hi : i < len), buf[position buf.length head i]'(position_lt hh (by omega)) = r := by
  constructor
  · intro h
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp h
    have hlen : i < len := by rwa [toList_length buf (Nat.le_of_lt hh) hl] at hi
    exact ⟨i, hlen, (toList_get buf hh hl hlen).symm.trans he⟩
  · rintro ⟨i, hi, he⟩
    refine List.mem_iff_getElem.mpr ⟨i, ?_, ?_⟩
    · rw [toList_length buf (Nat.le_of_lt hh) hl]; exact hi
    · exact (toList_get buf hh hl hi).trans he

theorem position_injective {cap head i j : Nat} (hh : head < cap)
    (hi : i < cap) (hj : j < cap) (heq : position cap head i = position cap head j) : i = j := by
  unfold position at heq
  split at heq <;> split at heq <;> omega

/-- Advancing the head and then indexing gives the same physical slot as
    making both moves from the original head. -/
theorem position_advance {cap head advance i : Nat}
    (hh : head < cap) (hb : advance + i < cap) :
    position cap (position cap head advance) i = position cap head (advance + i) := by
  simp only [position]
  by_cases h : advance < cap - head <;> simp only [h, ↓reduceIte] <;> split <;> split <;> omega

/-- Moving the head backwards by the inserted width leaves the old range
    at logical index `i + added` in the new orientation. -/
theorem position_rewind {cap head added i : Nat} (hh : head < cap)
    (ha : 0 < added) (hi : i+added < cap) :
    position cap (position cap head (cap-added)) (i+added) = position cap head i := by
  unfold position
  by_cases h : cap-added < cap-head <;> simp only [h, ↓reduceIte] <;> split <;> split <;> omega

theorem lookup_view (buf : List α) {head len i : Nat} (hh : head < buf.length)
    (hl : len ≤ buf.length) (hi : i < len) :
    (toList buf head len)[i]? = buf[position buf.length head i]? := by
  have live : i < (toList buf head len).length := by rw [toList_length _ (by omega) hl]; exact hi
  rw [List.getElem?_eq_getElem live, List.getElem?_eq_getElem (position_lt hh (by omega))]
  exact congrArg some (toList_get buf hh hl hi)

/-- Two active views of different lengths share all the slots that are in
    bounds for both. -/
theorem lookup_full (buf : List α) {head len i : Nat} (hh : head < buf.length)
    (hl : len ≤ buf.length) (hi : i < len) :
    (toList buf head len)[i]? = (toList buf head buf.length)[i]? := by
  rw [lookup_view buf hh hl hi, lookup_view buf hh (Nat.le_refl _) (by omega : i < buf.length)]

theorem rewind_lookup (buf : List α) {head added i : Nat} (hh : head < buf.length)
    (ha : 0 < added) (hi : i+added < buf.length) :
    (toList buf (position buf.length head (buf.length-added)) buf.length)[i+added]? =
      (toList buf head buf.length)[i]? := by
  rw [lookup_view buf (position_lt hh (by omega)) (Nat.le_refl _) hi,
    lookup_view buf hh (Nat.le_refl _) (by omega : i < buf.length), position_rewind hh ha hi]

theorem advance_lookup (buf : List α) {head cut i : Nat} (hh : head < buf.length)
    (hi : cut+i < buf.length) :
    (toList buf (position buf.length head cut) buf.length)[i]? =
      (toList buf head buf.length)[cut+i]? := by
  rw [lookup_view buf (position_lt hh (by omega)) (Nat.le_refl _) (by omega : i < buf.length),
    lookup_view buf hh (Nat.le_refl _) hi, position_advance hh hi]

theorem drop_view (buf : List α) {head len cut : Nat}
    (hh : head < buf.length) (hl : len ≤ buf.length) (hc : cut < len) :
    toList buf (position buf.length head cut) (len - cut) = (toList buf head len).drop cut := by
  have hh' := position_lt hh (show cut < buf.length by omega)
  apply List.ext_getElem
  · rw [toList_length buf (Nat.le_of_lt hh') (by omega), List.length_drop, toList_length buf (Nat.le_of_lt hh) hl]
  · intro i hi _
    have hi' : i < len - cut := by rwa [toList_length buf (Nat.le_of_lt hh') (by omega)] at hi
    rw [List.getElem_drop, toList_get buf hh hl (by omega : cut + i < len),
      toList_get buf hh' (by omega) hi']
    congr 1
    exact position_advance hh (by omega)

/-- Updating an inactive physical slot, including a capacity hint, leaves
    every logical range unchanged. -/
theorem set_inactive (buf : List α) {head len slot : Nat}
    (hh : head < buf.length) (hl : len ≤ slot) (hs : slot < buf.length) (value : α) :
    toList (buf.set (position buf.length head slot) value) head len = toList buf head len := by
  let loc := position buf.length head slot
  let buf' := buf.set loc value
  have hlen : buf'.length = buf.length := by simp [buf']
  have hh' : head < buf'.length := by omega
  have hl' : len ≤ buf'.length := by omega
  change toList buf' head len = toList buf head len
  apply List.ext_getElem
  · rw [toList_length buf' (by omega) hl', toList_length buf (by omega) (by omega)]
  · intro i hi hi'
    have hiL : i < len := by rwa [toList_length buf' (by omega) hl'] at hi
    have hn : loc ≠ position buf.length head i := by
      intro e
      have he := position_injective hh hs (by omega : i < buf.length) e
      omega
    rw [toList_get buf' hh' hl' hiL, toList_get buf hh (by omega) hiL]
    simp [buf', List.getElem_set_ne, hn]

/-- A write to an active physical slot changes exactly its logical element. -/
theorem set_active (buf : List α) {head len slot : Nat}
    (hh : head < buf.length) (hl : len ≤ buf.length) (hs : slot < len) (value : α) :
    toList (buf.set (position buf.length head slot) value) head len =
      (toList buf head len).set slot value := by
  let loc := position buf.length head slot
  let buf' := buf.set loc value
  have hlen : buf'.length = buf.length := by simp [buf']
  have hh' : head < buf'.length := by omega
  have hl' : len ≤ buf'.length := by omega
  change toList buf' head len = (toList buf head len).set slot value
  apply List.ext_getElem
  · rw [List.length_set, toList_length buf' (Nat.le_of_lt hh') hl',
      toList_length buf (Nat.le_of_lt hh) hl]
  · intro i hi hi'
    have hiL : i < len := by rwa [toList_length buf' (by omega) hl'] at hi
    rw [toList_get buf' hh' hl' hiL]
    by_cases he : i = slot
    · subst i
      simp [buf', loc]
    · have hn : loc ≠ position buf.length head i := by
        intro e
        exact he (position_injective hh (by omega : slot < buf.length) (by omega : i < buf.length) e).symm
      rw [List.getElem_set_ne (Ne.symm he), toList_get buf hh hl hiL]
      simp [buf', List.getElem_set_ne, hn]

end YoctoCore.Properties.OrderRangeRing
