/-
The edits of the ring behind the timeline of a client
(`y_octo_core::client_blocks`): a ring that grows, a word put in between the
blocks, and a run of blocks taken away. Each is described by the word every
block of the ring holds afterwards (`PutIn`, `Closed`); the number of blocks
is the caller's to set.
-/
import Aeneas
import YoctoCore.Code.Types
import YoctoCore.Code.Funs
import YoctoCore.Properties.ListAux
import YoctoCore.Properties.Ring
import YoctoCore.Properties.RingMoves

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open YoctoCore.Code
open YoctoCore.Properties.ListAux

set_option maxHeartbeats 400000
set_option autoImplicit false

namespace YoctoCore.Properties.Ring

/-! ## Reading a ring -/

theorem length_of_capOf_lt {cb : client_blocks.ClientBlocksCore} (h : capOf cb < 4294967295) :
    cb.buf.val.length = capOf cb := by
  unfold capOf at h ⊢
  omega

theorem firstOf_lt_or (cb : client_blocks.ClientBlocksCore) :
    firstOf cb < capOf cb ∨ firstOf cb = 0 := by
  unfold firstOf
  by_cases h : cb.head.val < capOf cb
  · rw [ite_eq_left h]
    exact Or.inl h
  · rw [ite_eq_right h]
    exact Or.inr rfl

/-- The fields of a ring read as what they say when they say a ring. -/
theorem capOf_of_length {cb : client_blocks.ClientBlocksCore} {c : Nat}
    (hc : cb.buf.val.length = c) (hmax : c ≤ 4294967295) : capOf cb = c := by
  unfold capOf
  omega

theorem firstOf_of_head {cb : client_blocks.ClientBlocksCore} {c h : Nat} (hc : capOf cb = c)
    (hh : cb.head.val = h) (hhc : h < c ∨ h = 0) : firstOf cb = h := by
  unfold firstOf
  rw [hc, hh]
  by_cases hlt : h < c
  · rw [ite_eq_left hlt]
  · rw [ite_eq_right hlt]
    omega

/-- A timeline holds no more blocks than a vector has elements. -/
theorem length_blocksOf_le (cb : client_blocks.ClientBlocksCore) :
    (blocksOf cb).length ≤ Usize.max := by
  rw [length_blocksOf]
  have h1 := countOf_le cb
  have h2 := capOf_le_length cb
  have h3 := cb.buf.property
  omega

/-- The block of a timeline in its ring. -/
theorem get?_blocksOf_lt {cb : client_blocks.ClientBlocksCore} {i : Nat} (h : i < countOf cb) :
    ∃ w : Std.U128, cb.buf.val[slotOf (capOf cb) (firstOf cb) i]? = some w ∧
      (blocksOf cb)[i]? = some (blockOf w) := by
  have hs := slotOf_lt_cap (firstOf_le cb) (Nat.lt_of_lt_of_le h (countOf_le cb))
  obtain ⟨w, hw⟩ := get?_some (Nat.lt_of_lt_of_le hs (capOf_le_length cb))
  refine ⟨w, hw, ?_⟩
  rw [get?_blocksOf, ite_eq_left h, blockAt_of_get? hw]

/-! ## `grow` and `make_room` -/

theorem grow_loop_spec (v0 v : alloc.vec.Vec Std.U128) (head more «from» : Std.Usize)
    (top : Nat) (htop : top + more.val ≤ v0.val.length)
    (hinv : v.val.length = v0.val.length ∧ head.val ≤ «from».val ∧ «from».val ≤ top ∧
      ∀ p : Nat, v.val[p]? =
        if «from».val + more.val ≤ p ∧ p < top + more.val then v0.val[p - more.val]?
        else v0.val[p]?) :
    client_blocks.ClientBlocksCore.grow_loop v head more «from» ⦃ r =>
      r.val.length = v0.val.length ∧
      ∀ p : Nat, r.val[p]? =
        if head.val + more.val ≤ p ∧ p < top + more.val then v0.val[p - more.val]?
        else v0.val[p]? ⦄ := by
  unfold client_blocks.ClientBlocksCore.grow_loop
  refine loop.spec_decr_nat
    (fun ((_, k) : alloc.vec.Vec Std.U128 × Std.Usize) => k.val)
    (fun ((w, k) : alloc.vec.Vec Std.U128 × Std.Usize) =>
      w.val.length = v0.val.length ∧ head.val ≤ k.val ∧ k.val ≤ top ∧
      ∀ p : Nat, w.val[p]? =
        if k.val + more.val ≤ p ∧ p < top + more.val then v0.val[p - more.val]?
        else v0.val[p]?)
    (fun (r : alloc.vec.Vec Std.U128) => r.val.length = v0.val.length ∧
      ∀ p : Nat, r.val[p]? =
        if head.val + more.val ≤ p ∧ p < top + more.val then v0.val[p - more.val]?
        else v0.val[p]?)
    _ (v, «from») ?_ hinv
  intro ⟨w, k⟩ ⟨hwl, hhk, hkt, hw⟩
  unfold client_blocks.ClientBlocksCore.grow_loop.body
  simp only
  have hbnd := v0.property
  by_cases hgt : k > head
  · simp only [hgt, ↓reduceIte]
    have hkv : head.val < k.val := by scalar_tac
    step as ⟨k1, hk1⟩
    have hk1v : k1.val = k.val - 1 := by scalar_tac
    have hk1l : k1.val < w.val.length := by omega
    step as ⟨word, hword⟩
    have hwg : w.val[k1.val]? = some word := get?_at hk1l hword
    step as ⟨i, hi⟩
    have hiv : i.val = k1.val + more.val := by scalar_tac
    have hil : i.val < w.val.length := by omega
    step as ⟨old, back, hold, hback⟩
    have hset : (back word).val = w.val.set i.val word := by
      rw [hback]
      simp
    refine ⟨?_, by omega, by omega, ?_, by omega⟩
    · rw [hset, List.length_set]
      exact hwl
    · intro p
      rw [hset, get?_set, hk1v]
      by_cases hp : p = i.val
      · rw [ite_eq_left ⟨hp, hil⟩, ite_eq_left ⟨by omega, by omega⟩]
        have hsrc := hw k1.val
        rw [ite_eq_right (by omega), hwg] at hsrc
        rw [hsrc]
        exact get?_congr (by omega)
      · rw [ite_eq_right (fun hc => hp hc.1), hw p]
        by_cases hc : k.val + more.val ≤ p ∧ p < top + more.val
        · rw [ite_eq_left hc, ite_eq_left ⟨by omega, hc.2⟩]
        · rw [ite_eq_right hc, ite_eq_right (by omega)]
  · simp only [hgt, ↓reduceIte, spec_ok]
    have hkh : k.val = head.val := by scalar_tac
    refine ⟨hwl, ?_⟩
    intro p
    rw [hw p, hkh]

/-- `cb'` is a ring of `c1` slots, the first block in the slot `h1`, that has
room for more than `n` blocks and holds, block by block, the words of the
first `n` blocks of the ring of `cb` (`c0` slots, the first block in the slot
`h0`). -/
structure Grown (cb : client_blocks.ClientBlocksCore) (c0 h0 n c1 h1 : Nat)
    (cb' : client_blocks.ClientBlocksCore) : Prop where
  cap : capOf cb' = c1
  first : firstOf cb' = h1
  room : n < c1
  len : cb'.len = cb.len
  end_clock : cb'.end_clock = cb.end_clock
  words : ∀ i : Nat, i < n → cb'.buf.val[slotOf c1 h1 i]? = cb.buf.val[slotOf c0 h0 i]?

/-- `grow`: a ring with more slots that holds, block by block, the words the
ring held. -/
theorem grow_spec (cb : client_blocks.ClientBlocksCore) (cap head : Std.Usize)
    (hcap : cap.val = cb.buf.val.length) (hlt : cap.val < 4294967295)
    (hh : head.val < cap.val ∨ head.val = 0) :
    client_blocks.ClientBlocksCore.grow cb cap head ⦃ p cb' =>
      Grown cb cap.val head.val cap.val p.1.val p.2.val cb' ⦄ := by
  unfold client_blocks.ClientBlocksCore.grow
  have z : (0#usize : Std.Usize).val = 0 := by scalar_tac
  have z32 : (0#u32 : Std.U32).val = 0 := by scalar_tac
  by_cases h0 : head = 0#usize
  · have h0' : (head = 0#usize) = True := eq_true h0
    simp only [h0', ↓reduceIte]
    have hhv : head.val = 0 := by scalar_tac
    step as ⟨g, hg1, hg2⟩
    step as ⟨slots, hslots⟩
    have hsv : slots.val = cap.val + g.val := by scalar_tac
    step with alloc.vec.Vec.resize_spec core.clone.CloneU128 cb.buf slots 0#u128 rfl as ⟨v, hv⟩
    have hvl : v.val.length = slots.val := by
      rw [hv]
      simp
    have hc' : capOf { cb with buf := v, head := 0#u32 } = slots.val :=
      capOf_of_length hvl (by omega)
    have hf' : firstOf { cb with buf := v, head := 0#u32 } = 0 :=
      firstOf_of_head hc' z32 (Or.inr rfl)
    refine ⟨hc', hf'.trans z.symm, by omega, rfl, rfl, ?_⟩
    intro i hi
    show v.val[slotOf slots.val (0#usize : Std.Usize).val i]? =
      cb.buf.val[slotOf cap.val head.val i]?
    rw [z, hhv, slotOf_lt (by omega), slotOf_lt (by omega), hv,
      get?_resize _ _ _ _ (by omega), ite_eq_left (by omega)]
  · simp only [h0, ↓reduceIte]
    have hhv : 0 < head.val := by scalar_tac
    have hhc : head.val < cap.val := by omega
    step as ⟨i, hi⟩
    step as ⟨more, hm1, hm2⟩
    step as ⟨slots, hslots⟩
    have hsv : slots.val = cap.val + more.val := by scalar_tac
    step with alloc.vec.Vec.resize_spec core.clone.CloneU128 cb.buf slots 0#u128 rfl as ⟨v, hv⟩
    have hvl : v.val.length = slots.val := by
      rw [hv]
      simp
    have hinit : v.val.length = v.val.length ∧ head.val ≤ cap.val ∧ cap.val ≤ cap.val ∧
        ∀ p : Nat, v.val[p]? =
          if cap.val + more.val ≤ p ∧ p < cap.val + more.val then v.val[p - more.val]?
          else v.val[p]? := by
      refine ⟨rfl, by omega, Nat.le_refl _, ?_⟩
      intro p
      rw [ite_eq_right (by omega)]
    step with grow_loop_spec v v head more cap cap.val (by omega) hinit as ⟨v1, hv1l, hv1⟩
    step as ⟨head1, hhead1⟩
    have hh1v : head1.val = head.val + more.val := by scalar_tac
    step with UScalar.cast_inBounds_spec UScalarTy.U32 head1 (by scalar_tac) as ⟨i1, hi1⟩
    have hc' : capOf { cb with buf := v1, head := i1 } = slots.val :=
      capOf_of_length (by rw [hv1l, hvl]) (by omega)
    have hf' : firstOf { cb with buf := v1, head := i1 } = head1.val :=
      firstOf_of_head hc' hi1 (Or.inl (by omega))
    refine ⟨hc', hf', by omega, rfl, rfl, ?_⟩
    intro r hr
    show v1.val[slotOf slots.val head1.val r]? = cb.buf.val[slotOf cap.val head.val r]?
    rw [hsv, hh1v]
    by_cases hrt : r < cap.val - head.val
    · rw [slotOf_lt (by omega), slotOf_lt hrt, hv1, ite_eq_left ⟨by omega, by omega⟩, hv,
        get?_resize _ _ _ _ (by omega), ite_eq_left (by omega)]
      exact get?_congr (by omega)
    · rw [slotOf_ge (by omega), slotOf_ge hrt, hv1, ite_eq_right (by omega), hv,
        get?_resize _ _ _ _ (by omega), ite_eq_left (by omega)]
      exact get?_congr (by omega)

/-- `make_room`: a ring with a free slot that holds, block by block, the words
the ring held. -/
theorem make_room_spec (cb : client_blocks.ClientBlocksCore) (cap head len : Std.Usize)
    (hcap : cap.val = capOf cb) (hhead : head.val = firstOf cb) (hlen : len.val ≤ cap.val)
    (hmax : len.val < 4294967295) :
    client_blocks.ClientBlocksCore.make_room cb cap head len ⦃ p cb' =>
      Grown cb cap.val head.val len.val p.1.val p.2.val cb' ⦄ := by
  unfold client_blocks.ClientBlocksCore.make_room
  by_cases hfull : len = cap
  · have hfull' : (len = cap) = True := eq_true hfull
    simp only [hfull', ↓reduceIte]
    have hlc : len.val = cap.val := by rw [hfull]
    have hcl : cap.val = cb.buf.val.length := by
      rw [hcap]
      exact (length_of_capOf_lt (by omega)).symm
    have hfo := firstOf_lt_or cb
    refine spec_mono (grow_spec cb cap head hcl (by omega) (by omega)) ?_
    rintro ⟨p, cb'⟩ h
    have hg : Grown cb cap.val head.val cap.val p.1.val p.2.val cb' := h
    show Grown cb cap.val head.val len.val p.1.val p.2.val cb'
    have hroom := hg.room
    exact ⟨hg.cap, hg.first, by omega, hg.len, hg.end_clock, fun i hi => hg.words i (by omega)⟩
  · simp only [hfull, ↓reduceIte, spec_ok, uncurry'_pair]
    have hne : len.val ≠ cap.val := by scalar_tac
    exact ⟨hcap.symm, hhead.symm, by omega, rfl, rfl, fun _ _ => rfl⟩

/-! ## A word put in -/

/-- `cb'` is the ring of `cb` with `word` put in as its block `at`: the `n`
blocks of `cb` keep their words, the blocks from `at` on one block later. The
ring has a slot for each of the `n + 1`. -/
structure PutIn (cb : client_blocks.ClientBlocksCore) (n «at» : Nat) (word : Std.U128)
    (cb' : client_blocks.ClientBlocksCore) : Prop where
  room : n < capOf cb'
  len : cb'.len = cb.len
  end_clock : cb'.end_clock = cb.end_clock
  words : ∀ i : Nat, i < n + 1 →
    cb'.buf.val[slotOf (capOf cb') (firstOf cb') i]? =
      if i < «at» then cb.buf.val[slotOf (capOf cb) (firstOf cb) i]?
      else if i = «at» then some word
      else cb.buf.val[slotOf (capOf cb) (firstOf cb) (i - 1)]?

/-- The blocks of a ring a word was put in, once the block is counted. -/
theorem blocksOf_of_putIn {cb cb' cb'' : client_blocks.ClientBlocksCore} {n «at» : Nat}
    {word : Std.U128} (h : PutIn cb n «at» word cb') (hn : n = countOf cb) (hat : «at» ≤ n)
    (hbuf : cb''.buf = cb'.buf) (hhead : cb''.head = cb'.head) (hlen : cb''.len.val = n + 1) :
    blocksOf cb'' = insAt (blocksOf cb) «at» (blockOf word) := by
  have hc : capOf cb'' = capOf cb' := by
    unfold capOf
    rw [hbuf]
  have hf : firstOf cb'' = firstOf cb' := by
    unfold firstOf
    rw [hc, hhead]
  have hroom := h.room
  have hcnt : countOf cb'' = n + 1 := by
    unfold countOf
    rw [hc, hlen]
    omega
  have hlb : (blocksOf cb).length = n := by
    rw [length_blocksOf, hn]
  apply blocksOf_ext
  · rw [length_insAt, hlb, hcnt]
  · intro i hi
    rw [hcnt] at hi
    have hw := h.words i hi
    rw [hc, hf, hbuf]
    by_cases h1 : i < «at»
    · rw [ite_eq_left h1] at hw
      rw [get?_insAt_lt _ _ h1 (by omega), get?_blocksOf, ite_eq_left (by omega)]
      exact congrArg some (blockAt_congr hw.symm)
    · rw [ite_eq_right h1] at hw
      by_cases h2 : i = «at»
      · rw [ite_eq_left h2] at hw
        rw [h2, get?_insAt_self _ _ (by omega), blockAt_of_get? (by rw [← h2]; exact hw)]
      · rw [ite_eq_right h2] at hw
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        rw [get?_insAt_gt _ _ (by omega), get?_blocksOf, ite_eq_left (by omega)]
        exact congrArg some (blockAt_congr hw.symm)

/-- A word stored in the slot after the blocks of a ring in the order of its
slots. -/
theorem putIn_plain_set {cb : client_blocks.ClientBlocksCore} {word : Std.U128}
    {v : alloc.vec.Vec Std.U128} (hv : cb.head.val = 0) {n : Nat} (hroom : n < capOf cb)
    (hset : v.val = cb.buf.val.set n word) : PutIn cb n n word { cb with buf := v } := by
  have hfl := firstOf_le cb
  have hcb := capOf_le_length cb
  have hc' : capOf { cb with buf := v } = capOf cb := by
    unfold capOf
    show min v.val.length 4294967295 = _
    rw [hset, List.length_set]
  have hf' : firstOf { cb with buf := v } = firstOf cb := by
    unfold firstOf
    rw [hc']
  have hsl : slotOf (capOf cb) (firstOf cb) n = n := slot_plain hv hroom
  have e : v.val = cb.buf.val.set (slotOf (capOf cb) (firstOf cb) n) word := by
    rw [hsl]
    exact hset
  refine ⟨by rw [hc']; exact hroom, rfl, rfl, ?_⟩
  intro i hi
  rw [hc', hf']
  show v.val[slotOf (capOf cb) (firstOf cb) i]? = _
  rw [e, get?_set_slot _ word hfl hcb hroom (by omega)]
  by_cases h1 : i < n
  · rw [ite_eq_left h1, ite_eq_right (by omega)]
  · rw [ite_eq_right h1, ite_eq_left (by omega), ite_eq_left (by omega)]

/-- A word pushed behind the blocks of a full ring in the order of its
slots. -/
theorem putIn_plain_push {cb : client_blocks.ClientBlocksCore} {word : Std.U128}
    {v : alloc.vec.Vec Std.U128} (hv : cb.head.val = 0) {n : Nat}
    (hfull : cb.buf.val.length = n) (hmax : n < 4294967295)
    (hpush : v.val = cb.buf.val ++ [word]) : PutIn cb n n word { cb with buf := v } := by
  have hvl : v.val.length = n + 1 := by
    rw [hpush, List.length_append, hfull]
    rfl
  have hc' : capOf { cb with buf := v } = n + 1 := capOf_of_length hvl (by omega)
  have hf' : firstOf { cb with buf := v } = 0 := firstOf_of_head hc' hv (Or.inr rfl)
  have hc : capOf cb = n := capOf_of_length hfull (by omega)
  refine ⟨by rw [hc']; omega, rfl, rfl, ?_⟩
  intro i hi
  rw [hc', hf', hc, firstOf_plain hv]
  show v.val[slotOf (n + 1) 0 i]? = _
  rw [slotOf_lt (by omega), hpush, get?_append_one, hfull]
  by_cases h1 : i < n
  · rw [ite_eq_left h1, ite_eq_left (by omega), slotOf_lt (by omega)]
  · rw [ite_eq_right h1, ite_eq_right (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega)]

/-- `put_last`: the word is the block after the blocks of the ring. -/
theorem put_last_spec (cb : client_blocks.ClientBlocksCore) (cap head len : Std.Usize)
    (word : Std.U128) (hcap : cap.val = capOf cb) (hhead : head.val = firstOf cb)
    (hlen : len.val = countOf cb) (hmax : len.val < 4294967295) :
    client_blocks.ClientBlocksCore.put_last cb cap head len word ⦃ cb' =>
      PutIn cb len.val len.val word cb' ⦄ := by
  unfold client_blocks.ClientBlocksCore.put_last
  have hfl := firstOf_le cb
  have hcl := countOf_le cb
  have hcb := capOf_le_length cb
  have z32 : (0#u32 : Std.U32).val = 0 := by scalar_tac
  by_cases hlt : len < cap
  · simp only [hlt, ↓reduceIte]
    have hltv : len.val < cap.val := by scalar_tac
    step as ⟨slot, hslot, hslotlt⟩
    step as ⟨old, back, hold, hback⟩
    have hset : (back word).val = cb.buf.val.set slot.val word := by
      rw [hback]
      simp
    have hc' : capOf { cb with buf := back word } = capOf cb := by
      unfold capOf
      rw [hset, List.length_set]
    have hf' : firstOf { cb with buf := back word } = firstOf cb := by
      unfold firstOf
      rw [hc']
    refine ⟨by rw [hc']; omega, rfl, rfl, ?_⟩
    intro i hi
    rw [hc', hf']
    show (back word).val[slotOf (capOf cb) (firstOf cb) i]? = _
    rw [hset, hslot, hcap, hhead,
      get?_set_slot _ word hfl hcb (by omega) (by omega)]
    by_cases h1 : i < len.val
    · rw [ite_eq_left h1, ite_eq_right (by omega)]
    · rw [ite_eq_right h1, ite_eq_left (by omega), ite_eq_left (by omega)]
  · simp only [hlt, ↓reduceIte]
    have hlc : len.val = cap.val := by scalar_tac
    have hbl : cb.buf.val.length = cap.val := by
      rw [hcap]
      exact length_of_capOf_lt (by omega)
    by_cases h0 : head = 0#usize
    · have h0' : (head = 0#usize) = True := eq_true h0
      simp only [h0', ↓reduceIte]
      have hhv : head.val = 0 := by scalar_tac
      step as ⟨v, hv⟩
      have hvl : v.val.length = cap.val + 1 := by
        rw [hv, List.length_append, hbl]
        rfl
      have hc' : capOf { cb with buf := v, head := 0#u32 } = cap.val + 1 :=
        capOf_of_length hvl (by omega)
      have hf' : firstOf { cb with buf := v, head := 0#u32 } = 0 :=
        firstOf_of_head hc' z32 (Or.inr rfl)
      refine ⟨by rw [hc']; omega, rfl, rfl, ?_⟩
      intro i hi
      rw [hc', hf', ← hhead, ← hcap, hhv]
      show v.val[slotOf (cap.val + 1) 0 i]? = _
      rw [slotOf_lt (by omega), hv, get?_append_one, hbl]
      by_cases h1 : i < len.val
      · rw [ite_eq_left h1, ite_eq_left (by omega), slotOf_lt (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega), ite_eq_left (by omega),
          ite_eq_left (by omega)]
    · simp only [h0, ↓reduceIte]
      have hhv : 0 < head.val := by scalar_tac
      have hfo := firstOf_lt_or cb
      step with grow_spec cb cap head hbl.symm (by omega) (by omega) as ⟨cap1, head1, cb1, hgrown⟩
      have hg : Grown cb cap.val head.val cap.val cap1.val head1.val cb1 := hgrown
      have hc1 := hg.cap
      have hf1 := hg.first
      have hgt := hg.room
      have hw1 := hg.words
      have hfl1 := firstOf_le cb1
      have hcb1 := capOf_le_length cb1
      step as ⟨slot, hslot, hslotlt⟩
      step as ⟨old, back, hold, hback⟩
      have hset : (back word).val = cb1.buf.val.set slot.val word := by
        rw [hback]
        simp
      have hc' : capOf { cb1 with buf := back word } = capOf cb1 := by
        unfold capOf
        rw [hset, List.length_set]
      have hf' : firstOf { cb1 with buf := back word } = firstOf cb1 := by
        unfold firstOf
        rw [hc']
      refine ⟨by rw [hc', hc1]; omega, hg.len, hg.end_clock, ?_⟩
      intro i hi
      rw [hc', hf']
      show (back word).val[slotOf (capOf cb1) (firstOf cb1) i]? = _
      rw [hset, hslot, ← hc1, ← hf1,
        get?_set_slot _ word hfl1 hcb1 (by omega) (by omega)]
      by_cases h1 : i < len.val
      · rw [ite_eq_left h1, ite_eq_right (by omega), hc1, hf1, hw1 i (by omega), hcap, hhead]
      · rw [ite_eq_right h1, ite_eq_left (by omega), ite_eq_left (by omega)]

/-- `put_moving_up`: the word is the block `at`, and the blocks from `at` on
are one block later. -/
theorem put_moving_up_spec (cb : client_blocks.ClientBlocksCore)
    (cap head len «at» : Std.Usize) (word : Std.U128) (hcap : cap.val = capOf cb)
    (hhead : head.val = firstOf cb) (hlen : len.val = countOf cb)
    (hmax : len.val < 4294967295) (hat : «at».val ≤ len.val) :
    client_blocks.ClientBlocksCore.put_moving_up cb cap head len «at» word ⦃ cb' =>
      PutIn cb len.val «at».val word cb' ⦄ := by
  unfold client_blocks.ClientBlocksCore.put_moving_up
  have hcl := countOf_le cb
  step with make_room_spec cb cap head len hcap hhead (by omega) hmax as ⟨cap1, head1, cb1, hgrown⟩
  have hg : Grown cb cap.val head.val len.val cap1.val head1.val cb1 := hgrown
  have hc1 := hg.cap
  have hf1 := hg.first
  have hgt := hg.room
  have hl1 := hg.len
  have he1 := hg.end_clock
  have hw1 := hg.words
  have hfl1 := firstOf_le cb1
  have hcb1 := capOf_le_length cb1
  step with move_up_spec cb1 cap1 head1 «at» len (by omega) (by omega) hat hgt
    as ⟨cb2, hh2, hl2, he2, hbl2, hw2⟩
  step as ⟨slot, hslot, hslotlt⟩
  step as ⟨old, back, hold, hback⟩
  have hset : (back word).val = cb2.buf.val.set slot.val word := by
    rw [hback]
    simp
  have hc' : capOf { cb2 with buf := back word } = capOf cb1 := by
    unfold capOf
    rw [hset, List.length_set, hbl2]
  have hf' : firstOf { cb2 with buf := back word } = firstOf cb1 := by
    unfold firstOf
    rw [hc']
    show (if cb2.head.val < capOf cb1 then cb2.head.val else 0) = _
    rw [hh2]
  refine ⟨by rw [hc', hc1]; omega, hl2.trans hl1, he2.trans he1, ?_⟩
  intro i hi
  rw [hc', hf']
  show (back word).val[slotOf (capOf cb1) (firstOf cb1) i]? = _
  rw [hset, hslot, ← hc1, ← hf1,
    get?_set_slot _ word (by omega) (by omega) (by omega) (by omega)]
  by_cases h2 : i = «at».val
  · rw [ite_eq_left h2, ite_eq_right (by omega), ite_eq_left h2]
  · rw [ite_eq_right h2, hc1, hf1, hw2 i (by omega)]
    by_cases h1 : i < «at».val
    · rw [ite_eq_left h1, ite_eq_right (by omega), hw1 i (by omega), hcap, hhead]
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left ⟨by omega, by omega⟩,
        hw1 (i - 1) (by omega), hcap, hhead]

/-- `put_moving_down`: the word is the block `at`, the ring starts a slot
earlier, and the blocks before `at` are where they were on the timeline. -/
theorem put_moving_down_spec (cb : client_blocks.ClientBlocksCore)
    (cap head len «at» : Std.Usize) (word : Std.U128) (hcap : cap.val = capOf cb)
    (hhead : head.val = firstOf cb) (hlen : len.val = countOf cb)
    (hmax : len.val < 4294967295) (hat : «at».val ≤ len.val) :
    client_blocks.ClientBlocksCore.put_moving_down cb cap head len «at» word ⦃ cb' =>
      PutIn cb len.val «at».val word cb' ⦄ := by
  unfold client_blocks.ClientBlocksCore.put_moving_down
  have hcl := countOf_le cb
  step with make_room_spec cb cap head len hcap hhead (by omega) hmax as ⟨cap1, head1, cb1, hgrown⟩
  have hg : Grown cb cap.val head.val len.val cap1.val head1.val cb1 := hgrown
  have hc1 := hg.cap
  have hf1 := hg.first
  have hgt := hg.room
  have hl1 := hg.len
  have he1 := hg.end_clock
  have hw1 := hg.words
  have hfo1 := firstOf_lt_or cb1
  have hcb1 := capOf_le_length cb1
  have hh1 : head1.val < cap1.val := by omega
  have hmx1 := capOf_le_max cb1
  step as ⟨head2, hhead2, hhead2lt⟩
  have hh2m : head2.val ≤ 4294967295 := by omega
  step with UScalar.cast_inBounds_spec UScalarTy.U32 head2 (by scalar_tac) as ⟨i, hi⟩
  step with move_down_spec { cb1 with head := i } cap1 head2 0#usize «at» (by omega)
    (by show cap1.val ≤ cb1.buf.val.length; omega) (by scalar_tac) (by omega)
    as ⟨cb2, hh2, hl2, he2, hbl2, hw2⟩
  step as ⟨slot, hslot, hslotlt⟩
  step as ⟨old, back, hold, hback⟩
  have hset : (back word).val = cb2.buf.val.set slot.val word := by
    rw [hback]
    simp
  have hc' : capOf { cb2 with buf := back word } = cap1.val := by
    unfold capOf
    rw [hset, List.length_set, hbl2]
    exact hc1
  have hf' : firstOf { cb2 with buf := back word } = head2.val :=
    firstOf_of_head hc' (by show cb2.head.val = head2.val; rw [hh2]; exact hi)
      (Or.inl hhead2lt)
  refine ⟨by rw [hc']; omega, hl2.trans hl1, he2.trans he1, ?_⟩
  intro r hr
  rw [hc', hf']
  show (back word).val[slotOf cap1.val head2.val r]? = _
  rw [hset, hslot, get?_set_slot _ word (by omega) (by omega) (by omega) (by omega)]
  by_cases h2 : r = «at».val
  · rw [ite_eq_left h2, ite_eq_right (by omega), ite_eq_left h2]
  · rw [ite_eq_right h2, hw2 r (by omega)]
    by_cases h1 : r < «at».val
    · rw [ite_eq_left h1, ite_eq_left ⟨by scalar_tac, h1⟩, hhead2,
        slotOf_before hh1 (by omega)]
      exact (hw1 r (by omega)).trans (by rw [hcap, hhead])
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (by omega)]
      obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
      have e : j + 1 - 1 = j := by omega
      rw [hhead2, slotOf_before hh1 (by omega), e]
      exact (hw1 j (by omega)).trans (by rw [hcap, hhead])

/-- `put`: the word is the block `at` of the ring. -/
theorem put_spec (cb : client_blocks.ClientBlocksCore) (cap head len «at» : Std.Usize)
    (word : Std.U128) (hcap : cap.val = capOf cb) (hhead : head.val = firstOf cb)
    (hlen : len.val = countOf cb) (hmax : len.val < 4294967295) (hat : «at».val ≤ len.val) :
    client_blocks.ClientBlocksCore.put cb cap head len «at» word ⦃ cb' =>
      PutIn cb len.val «at».val word cb' ⦄ := by
  unfold client_blocks.ClientBlocksCore.put
  have hcl := countOf_le cb
  have z32 : (0#u32 : Std.U32).val = 0 := by scalar_tac
  step as ⟨after, hafter⟩
  have hav : after.val = len.val - «at».val := by scalar_tac
  by_cases h1 : after > «at»
  · simp only [h1, ↓reduceIte]
    exact put_moving_down_spec cb cap head len «at» word hcap hhead hlen hmax hat
  · simp only [h1, ↓reduceIte]
    by_cases h2 : len < cap
    · simp only [h2, ↓reduceIte]
      exact put_moving_up_spec cb cap head len «at» word hcap hhead hlen hmax hat
    · simp only [h2, ↓reduceIte]
      have hlc : len.val = cap.val := by scalar_tac
      by_cases h0 : head = 0#usize
      · have h0' : (head = 0#usize) = True := eq_true h0
        simp only [h0', ↓reduceIte]
        have hhv : head.val = 0 := by scalar_tac
        have hbl : cb.buf.val.length = cap.val := by
          rw [hcap]
          exact length_of_capOf_lt (by omega)
        by_cases h3 : after = 0#usize
        · have h3' : (after = 0#usize) = True := eq_true h3
          simp only [h3', ↓reduceIte]
          have hal : «at».val = len.val := by scalar_tac
          step as ⟨v, hv⟩
          have hvl : v.val.length = cap.val + 1 := by
            rw [hv, List.length_append, hbl]
            rfl
          have hc' : capOf { cb with buf := v, head := 0#u32 } = cap.val + 1 :=
            capOf_of_length hvl (by omega)
          have hf' : firstOf { cb with buf := v, head := 0#u32 } = 0 :=
            firstOf_of_head hc' z32 (Or.inr rfl)
          refine ⟨by rw [hc']; omega, rfl, rfl, ?_⟩
          intro i hi
          rw [hc', hf', ← hhead, ← hcap, hhv]
          show v.val[slotOf (cap.val + 1) 0 i]? = _
          rw [slotOf_lt (by omega), hv, get?_append_one, hbl]
          by_cases hia : i < «at».val
          · rw [ite_eq_left hia, ite_eq_left (by omega), slotOf_lt (by omega)]
          · rw [ite_eq_right hia, ite_eq_right (by omega), ite_eq_left (by omega),
              ite_eq_left (by omega)]
        · simp only [h3, ↓reduceIte]
          have hal : «at».val < len.val := by scalar_tac
          step as ⟨v, hv⟩
          have hins : v.val = insAt cb.buf.val «at».val word := by
            rw [hv, insertIdx_eq_insAt _ _ _ (by omega)]
          have hvl : v.val.length = cap.val + 1 := by
            rw [hins, length_insAt, hbl]
          have hc' : capOf { cb with buf := v, head := 0#u32 } = cap.val + 1 :=
            capOf_of_length hvl (by omega)
          have hf' : firstOf { cb with buf := v, head := 0#u32 } = 0 :=
            firstOf_of_head hc' z32 (Or.inr rfl)
          refine ⟨by rw [hc']; omega, rfl, rfl, ?_⟩
          intro i hi
          rw [hc', hf', ← hhead, ← hcap, hhv]
          show v.val[slotOf (cap.val + 1) 0 i]? = _
          rw [slotOf_lt (by omega), hins]
          have e0 : 0 + i = i := by omega
          rw [e0]
          by_cases hia : i < «at».val
          · rw [ite_eq_left hia, slotOf_lt (by omega), e0, get?_insAt_lt _ _ hia (by omega)]
          · rw [ite_eq_right hia]
            by_cases hie : i = «at».val
            · rw [ite_eq_left hie, hie, get?_insAt_self _ _ (by omega)]
            · rw [ite_eq_right hie, slotOf_lt (by omega)]
              obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
              have e1 : 0 + (j + 1 - 1) = j := by omega
              rw [e1, get?_insAt_gt _ _ (by omega)]
      · simp only [h0, ↓reduceIte]
        exact put_moving_up_spec cb cap head len «at» word hcap hhead hlen hmax hat

/-! ## A run of blocks taken away -/

/-- `cb'` is the ring of `cb` without its blocks `first + 1..=first + gap`:
the blocks up to `first` keep their words, and the blocks after them hold the
words of the blocks `gap` blocks later. -/
structure Closed (cb : client_blocks.ClientBlocksCore) (n first gap : Nat)
    (cb' : client_blocks.ClientBlocksCore) : Prop where
  cap : capOf cb' = capOf cb
  len : cb'.len = cb.len
  end_clock : cb'.end_clock = cb.end_clock
  words : ∀ i : Nat, i + gap < n →
    cb'.buf.val[slotOf (capOf cb') (firstOf cb') i]? =
      if i ≤ first then cb.buf.val[slotOf (capOf cb) (firstOf cb) i]?
      else cb.buf.val[slotOf (capOf cb) (firstOf cb) (i + gap)]?

/-- The blocks of a ring a run of blocks was taken away from, once they are
no longer counted. -/
theorem blocksOf_of_closed {cb cb' cb'' : client_blocks.ClientBlocksCore} {n first gap : Nat}
    (h : Closed cb n first gap cb') (hn : n = countOf cb) (hfg : first + gap < n)
    (hbuf : cb''.buf = cb'.buf) (hhead : cb''.head = cb'.head)
    (hlen : cb''.len.val = n - gap) :
    blocksOf cb'' = (blocksOf cb).take (first + 1) ++ (blocksOf cb).drop (first + gap + 1) := by
  have hc : capOf cb'' = capOf cb' := by
    unfold capOf
    rw [hbuf]
  have hf : firstOf cb'' = firstOf cb' := by
    unfold firstOf
    rw [hc, hhead]
  have hcl := countOf_le cb
  have hcnt : countOf cb'' = n - gap := by
    unfold countOf
    rw [hc, hlen, h.cap]
    omega
  have hlb : (blocksOf cb).length = n := by
    rw [length_blocksOf, hn]
  have key : ∀ j : Nat, ((blocksOf cb).take (first + 1) ++
      (blocksOf cb).drop (first + gap + 1))[j]? =
        if j < first + 1 then (blocksOf cb)[j]? else (blocksOf cb)[j + gap]? := by
    intro j
    have hlen : ((blocksOf cb).take (first + 1)).length = first + 1 := by
      rw [List.length_take]
      omega
    by_cases hj : j < first + 1
    · rw [ite_eq_left hj, get?_append_left (by rw [hlen]; exact hj)]
      simp [hj]
    · obtain ⟨k, rfl⟩ : ∃ k, j = first + 1 + k := ⟨j - (first + 1), by omega⟩
      rw [ite_eq_right hj]
      have ha := get?_append_right ((blocksOf cb).take (first + 1))
        ((blocksOf cb).drop (first + gap + 1)) k
      rw [hlen] at ha
      rw [ha, List.getElem?_drop]
      exact get?_congr (by omega)
  apply blocksOf_ext
  · rw [hcnt, List.length_append, List.length_take, List.length_drop, hlb]
    omega
  · intro i hi
    rw [hcnt] at hi
    have hw := h.words i (by omega)
    rw [key, hc, hf, hbuf]
    by_cases h1 : i < first + 1
    · rw [ite_eq_left h1, get?_blocksOf, ite_eq_left (by omega)]
      rw [ite_eq_left (by omega)] at hw
      exact congrArg some (blockAt_congr hw.symm)
    · rw [ite_eq_right h1, get?_blocksOf, ite_eq_left (by omega)]
      rw [ite_eq_right (by omega)] at hw
      exact congrArg some (blockAt_congr hw.symm)

theorem pull_down_loop_spec (cb0 cb : client_blocks.ClientBlocksCore)
    (cap head len gap i : Std.Usize) («from» : Nat) (hh : head.val ≤ cap.val)
    (hc : cap.val ≤ cb0.buf.val.length) (hlc : len.val ≤ cap.val) (hg : 0 < gap.val)
    (hgf : gap.val ≤ «from»)
    (hinv : cb.head = cb0.head ∧ cb.len = cb0.len ∧ cb.end_clock = cb0.end_clock ∧
      cb.buf.val.length = cb0.buf.val.length ∧ «from» ≤ i.val ∧ i.val ≤ len.val ∧
      ∀ r : Nat, r < cap.val → cb.buf.val[slotOf cap.val head.val r]? =
        if «from» - gap.val ≤ r ∧ r + gap.val < i.val then
          cb0.buf.val[slotOf cap.val head.val (r + gap.val)]?
        else cb0.buf.val[slotOf cap.val head.val r]?) :
    client_blocks.ClientBlocksCore.pull_down_loop cb cap head len gap i ⦃ cb' =>
      cb'.head = cb0.head ∧ cb'.len = cb0.len ∧ cb'.end_clock = cb0.end_clock ∧
      cb'.buf.val.length = cb0.buf.val.length ∧
      ∀ r : Nat, r < cap.val → cb'.buf.val[slotOf cap.val head.val r]? =
        if «from» - gap.val ≤ r ∧ r + gap.val < len.val then
          cb0.buf.val[slotOf cap.val head.val (r + gap.val)]?
        else cb0.buf.val[slotOf cap.val head.val r]? ⦄ := by
  unfold client_blocks.ClientBlocksCore.pull_down_loop
  refine loop.spec_decr_nat
    (fun ((_, k) : client_blocks.ClientBlocksCore × Std.Usize) => len.val - k.val)
    (fun ((c, k) : client_blocks.ClientBlocksCore × Std.Usize) =>
      c.head = cb0.head ∧ c.len = cb0.len ∧ c.end_clock = cb0.end_clock ∧
      c.buf.val.length = cb0.buf.val.length ∧ «from» ≤ k.val ∧ k.val ≤ len.val ∧
      ∀ r : Nat, r < cap.val → c.buf.val[slotOf cap.val head.val r]? =
        if «from» - gap.val ≤ r ∧ r + gap.val < k.val then
          cb0.buf.val[slotOf cap.val head.val (r + gap.val)]?
        else cb0.buf.val[slotOf cap.val head.val r]?)
    (fun (c : client_blocks.ClientBlocksCore) =>
      c.head = cb0.head ∧ c.len = cb0.len ∧ c.end_clock = cb0.end_clock ∧
      c.buf.val.length = cb0.buf.val.length ∧
      ∀ r : Nat, r < cap.val → c.buf.val[slotOf cap.val head.val r]? =
        if «from» - gap.val ≤ r ∧ r + gap.val < len.val then
          cb0.buf.val[slotOf cap.val head.val (r + gap.val)]?
        else cb0.buf.val[slotOf cap.val head.val r]?)
    _ (cb, i) ?_ hinv
  intro ⟨c, k⟩ ⟨hch, hcl, hce, hcbl, hfk, hkl, hw⟩
  unfold client_blocks.ClientBlocksCore.pull_down_loop.body
  simp only
  by_cases hlt : k < len
  · simp only [hlt, ↓reduceIte]
    have hkv : k.val < len.val := by scalar_tac
    step as ⟨s1, hs1, hs1lt⟩
    step as ⟨word, hword⟩
    have hwg : c.buf.val[s1.val]? = some word := get?_at (by omega) hword
    step as ⟨k2, hk2⟩
    have hk2v : k2.val = k.val - gap.val := by scalar_tac
    step as ⟨slot, hslot, hslotlt⟩
    step as ⟨old, back, hold, hback⟩
    step as ⟨k3, hk3⟩
    have hk3v : k3.val = k.val + 1 := by scalar_tac
    have hset : (back word).val = c.buf.val.set slot.val word := by
      rw [hback]
      simp
    refine ⟨hch, hcl, hce, ?_, by omega, by omega, ?_, by omega⟩
    · show (back word).val.length = cb0.buf.val.length
      rw [hset, List.length_set]
      exact hcbl
    · intro r hr
      show (back word).val[slotOf cap.val head.val r]? = _
      rw [hset, hslot, hk2v, get?_set_slot _ word hh (by omega) (by omega) hr, hk3v]
      by_cases hrk : r = k.val - gap.val
      · rw [ite_eq_left hrk, ite_eq_left ⟨by omega, by omega⟩]
        have hsrc := hw k.val (by omega)
        rw [ite_eq_right (by omega), ← hs1, hwg] at hsrc
        have e : r + gap.val = k.val := by omega
        rw [hsrc, e, hs1]
      · rw [ite_eq_right hrk, hw r hr]
        by_cases hcnd : «from» - gap.val ≤ r ∧ r + gap.val < k.val
        · rw [ite_eq_left hcnd, ite_eq_left ⟨hcnd.1, by omega⟩]
        · rw [ite_eq_right hcnd, ite_eq_right (by omega)]
  · simp only [hlt, ↓reduceIte, spec_ok]
    have hke : k.val = len.val := by scalar_tac
    refine ⟨hch, hcl, hce, hcbl, ?_⟩
    intro r hr
    rw [hw r hr, hke]

theorem push_up_loop_spec (cb0 cb : client_blocks.ClientBlocksCore)
    (cap head gap i : Std.Usize) (count : Nat) (hh : head.val ≤ cap.val)
    (hc : cap.val ≤ cb0.buf.val.length) (hcg : count + gap.val ≤ cap.val) (hg : 0 < gap.val)
    (hinv : cb.head = cb0.head ∧ cb.len = cb0.len ∧ cb.end_clock = cb0.end_clock ∧
      cb.buf.val.length = cb0.buf.val.length ∧ i.val ≤ count ∧
      ∀ r : Nat, r < cap.val → cb.buf.val[slotOf cap.val head.val r]? =
        if i.val + gap.val ≤ r ∧ r < count + gap.val then
          cb0.buf.val[slotOf cap.val head.val (r - gap.val)]?
        else cb0.buf.val[slotOf cap.val head.val r]?) :
    client_blocks.ClientBlocksCore.push_up_loop cb cap head gap i ⦃ cb' =>
      cb'.head = cb0.head ∧ cb'.len = cb0.len ∧ cb'.end_clock = cb0.end_clock ∧
      cb'.buf.val.length = cb0.buf.val.length ∧
      ∀ r : Nat, r < cap.val → cb'.buf.val[slotOf cap.val head.val r]? =
        if gap.val ≤ r ∧ r < count + gap.val then
          cb0.buf.val[slotOf cap.val head.val (r - gap.val)]?
        else cb0.buf.val[slotOf cap.val head.val r]? ⦄ := by
  unfold client_blocks.ClientBlocksCore.push_up_loop
  refine loop.spec_decr_nat
    (fun ((_, k) : client_blocks.ClientBlocksCore × Std.Usize) => k.val)
    (fun ((c, k) : client_blocks.ClientBlocksCore × Std.Usize) =>
      c.head = cb0.head ∧ c.len = cb0.len ∧ c.end_clock = cb0.end_clock ∧
      c.buf.val.length = cb0.buf.val.length ∧ k.val ≤ count ∧
      ∀ r : Nat, r < cap.val → c.buf.val[slotOf cap.val head.val r]? =
        if k.val + gap.val ≤ r ∧ r < count + gap.val then
          cb0.buf.val[slotOf cap.val head.val (r - gap.val)]?
        else cb0.buf.val[slotOf cap.val head.val r]?)
    (fun (c : client_blocks.ClientBlocksCore) =>
      c.head = cb0.head ∧ c.len = cb0.len ∧ c.end_clock = cb0.end_clock ∧
      c.buf.val.length = cb0.buf.val.length ∧
      ∀ r : Nat, r < cap.val → c.buf.val[slotOf cap.val head.val r]? =
        if gap.val ≤ r ∧ r < count + gap.val then
          cb0.buf.val[slotOf cap.val head.val (r - gap.val)]?
        else cb0.buf.val[slotOf cap.val head.val r]?)
    _ (cb, i) ?_ hinv
  intro ⟨c, k⟩ ⟨hch, hcl, hce, hcbl, hkc, hw⟩
  unfold client_blocks.ClientBlocksCore.push_up_loop.body
  simp only
  by_cases hgt : k > 0#usize
  · simp only [hgt, ↓reduceIte]
    have hkv : 0 < k.val := by scalar_tac
    step as ⟨k1, hk1⟩
    have hk1v : k1.val = k.val - 1 := by scalar_tac
    step as ⟨s1, hs1, hs1lt⟩
    step as ⟨word, hword⟩
    have hwg : c.buf.val[s1.val]? = some word := get?_at (by omega) hword
    step as ⟨k3, hk3⟩
    have hk3v : k3.val = k1.val + gap.val := by scalar_tac
    step as ⟨slot, hslot, hslotlt⟩
    step as ⟨old, back, hold, hback⟩
    have hset : (back word).val = c.buf.val.set slot.val word := by
      rw [hback]
      simp
    refine ⟨hch, hcl, hce, ?_, by omega, ?_, by omega⟩
    · show (back word).val.length = cb0.buf.val.length
      rw [hset, List.length_set]
      exact hcbl
    · intro r hr
      show (back word).val[slotOf cap.val head.val r]? = _
      rw [hset, hslot, hk3v, get?_set_slot _ word hh (by omega) (by omega) hr, hk1v]
      by_cases hrk : r = k.val - 1 + gap.val
      · rw [ite_eq_left hrk, ite_eq_left ⟨by omega, by omega⟩]
        have hsrc := hw k1.val (by omega)
        rw [ite_eq_right (by omega), ← hs1, hwg] at hsrc
        have e : r - gap.val = k1.val := by omega
        rw [hsrc, e, hs1]
      · rw [ite_eq_right hrk, hw r hr]
        by_cases hcnd : k.val + gap.val ≤ r ∧ r < count + gap.val
        · rw [ite_eq_left hcnd, ite_eq_left ⟨by omega, hcnd.2⟩]
        · rw [ite_eq_right hcnd, ite_eq_right (by omega)]
  · simp only [hgt, ↓reduceIte, spec_ok]
    have hk0 : k.val = 0 := by scalar_tac
    refine ⟨hch, hcl, hce, hcbl, ?_⟩
    intro r hr
    rw [hw r hr, hk0, Nat.zero_add]

theorem push_up_few_loop_spec (cb0 cb : client_blocks.ClientBlocksCore)
    (cap head count gap pass : Std.Usize) (hh : head.val ≤ cap.val)
    (hc : cap.val ≤ cb0.buf.val.length) (hcg : count.val + gap.val ≤ cap.val)
    (hinv : cb.head = cb0.head ∧ cb.len = cb0.len ∧ cb.end_clock = cb0.end_clock ∧
      cb.buf.val.length = cb0.buf.val.length ∧ pass.val ≤ gap.val ∧
      ∀ r : Nat, r < cap.val →
        (pass.val ≤ r ∧ r < count.val + pass.val →
          cb.buf.val[slotOf cap.val head.val r]? =
            cb0.buf.val[slotOf cap.val head.val (r - pass.val)]?) ∧
        (count.val + pass.val ≤ r →
          cb.buf.val[slotOf cap.val head.val r]? = cb0.buf.val[slotOf cap.val head.val r]?)) :
    client_blocks.ClientBlocksCore.push_up_few_loop cb cap head count gap pass ⦃ cb' =>
      cb'.head = cb0.head ∧ cb'.len = cb0.len ∧ cb'.end_clock = cb0.end_clock ∧
      cb'.buf.val.length = cb0.buf.val.length ∧
      ∀ r : Nat, r < cap.val →
        (gap.val ≤ r ∧ r < count.val + gap.val →
          cb'.buf.val[slotOf cap.val head.val r]? =
            cb0.buf.val[slotOf cap.val head.val (r - gap.val)]?) ∧
        (count.val + gap.val ≤ r →
          cb'.buf.val[slotOf cap.val head.val r]? =
            cb0.buf.val[slotOf cap.val head.val r]?) ⦄ := by
  unfold client_blocks.ClientBlocksCore.push_up_few_loop
  refine loop.spec_decr_nat
    (fun ((_, k) : client_blocks.ClientBlocksCore × Std.Usize) => gap.val - k.val)
    (fun ((c, k) : client_blocks.ClientBlocksCore × Std.Usize) =>
      c.head = cb0.head ∧ c.len = cb0.len ∧ c.end_clock = cb0.end_clock ∧
      c.buf.val.length = cb0.buf.val.length ∧ k.val ≤ gap.val ∧
      ∀ r : Nat, r < cap.val →
        (k.val ≤ r ∧ r < count.val + k.val →
          c.buf.val[slotOf cap.val head.val r]? =
            cb0.buf.val[slotOf cap.val head.val (r - k.val)]?) ∧
        (count.val + k.val ≤ r →
          c.buf.val[slotOf cap.val head.val r]? = cb0.buf.val[slotOf cap.val head.val r]?))
    (fun (c : client_blocks.ClientBlocksCore) =>
      c.head = cb0.head ∧ c.len = cb0.len ∧ c.end_clock = cb0.end_clock ∧
      c.buf.val.length = cb0.buf.val.length ∧
      ∀ r : Nat, r < cap.val →
        (gap.val ≤ r ∧ r < count.val + gap.val →
          c.buf.val[slotOf cap.val head.val r]? =
            cb0.buf.val[slotOf cap.val head.val (r - gap.val)]?) ∧
        (count.val + gap.val ≤ r →
          c.buf.val[slotOf cap.val head.val r]? = cb0.buf.val[slotOf cap.val head.val r]?))
    _ (cb, pass) ?_ hinv
  intro ⟨c, k⟩ ⟨hch, hcl, hce, hcbl, hkg, hw⟩
  unfold client_blocks.ClientBlocksCore.push_up_few_loop.body
  simp only
  by_cases hlt : k < gap
  · simp only [hlt, ↓reduceIte]
    have hkv : k.val < gap.val := by scalar_tac
    step as ⟨i, hi⟩
    have hiv : i.val = count.val + k.val := by scalar_tac
    step with move_up_spec c cap head k i hh (by omega) (by omega) (by omega)
      as ⟨c1, hh1, hl1, he1, hbl1, hw1⟩
    step as ⟨k1, hk1⟩
    have hk1v : k1.val = k.val + 1 := by scalar_tac
    refine ⟨hh1.trans hch, hl1.trans hcl, he1.trans hce, hbl1.trans hcbl, by omega, ?_, by omega⟩
    intro r hr
    have hm : c1.buf.val[slotOf cap.val head.val r]? =
        if k.val < r ∧ r ≤ count.val + k.val then c.buf.val[slotOf cap.val head.val (r - 1)]?
        else c.buf.val[slotOf cap.val head.val r]? := by
      rw [← hiv]
      exact hw1 r hr
    constructor
    · intro hc1 hc1'
      have h1 : k.val + 1 ≤ r := by
        rw [← hk1v]
        exact hc1
      have h2 : r < count.val + (k.val + 1) := by
        rw [← hk1v]
        exact hc1'
      have hprev : c.buf.val[slotOf cap.val head.val (r - 1)]? =
          cb0.buf.val[slotOf cap.val head.val (r - 1 - k.val)]? :=
        (hw (r - 1) (by omega)).1 ⟨by omega, by omega⟩
      show c1.buf.val[slotOf cap.val head.val r]? =
        cb0.buf.val[slotOf cap.val head.val (r - k1.val)]?
      rw [hm, ite_eq_left ⟨by omega, by omega⟩, hprev]
      exact get?_congr (congrArg (slotOf cap.val head.val) (by omega))
    · intro hc2
      have h3 : count.val + (k.val + 1) ≤ r := by
        rw [← hk1v]
        exact hc2
      show c1.buf.val[slotOf cap.val head.val r]? = cb0.buf.val[slotOf cap.val head.val r]?
      rw [hm, ite_eq_right (by omega), (hw r hr).2 (by omega)]
  · simp only [hlt, ↓reduceIte, spec_ok]
    have hke : k.val = gap.val := by scalar_tac
    refine ⟨hch, hcl, hce, hcbl, ?_⟩
    intro r hr
    have h := hw r hr
    rw [hke] at h
    exact h

/-- `close`: the blocks `first + 1..=last` are taken away. -/
theorem close_spec (cb : client_blocks.ClientBlocksCore) (cap head len first last : Std.Usize)
    (hcap : cap.val = capOf cb) (hhead : head.val = firstOf cb) (hlen : len.val = countOf cb)
    (hfl : first.val < last.val) (hll : last.val < len.val) :
    client_blocks.ClientBlocksCore.close cb cap head len first last ⦃ cb' =>
      Closed cb len.val first.val (last.val - first.val) cb' ⦄ := by
  unfold client_blocks.ClientBlocksCore.close
  have hfle := firstOf_le cb
  have hcl := countOf_le cb
  have hcb := capOf_le_length cb
  have hmx := capOf_le_max cb
  have z : (0#usize : Std.Usize).val = 0 := by scalar_tac
  step as ⟨i, hi⟩
  step as ⟨after, hafter⟩
  by_cases hae : after <= first
  · simp only [hae, ↓reduceIte]
    step as ⟨i1, hi1⟩
    step as ⟨gap, hgap⟩
    have hi1v : i1.val = last.val + 1 := by scalar_tac
    have hgv : gap.val = last.val - first.val := by scalar_tac
    unfold client_blocks.ClientBlocksCore.close_from_end
    by_cases hfl : i1 = len
    · have hfl' : (i1 = len) = True := eq_true hfl
      simp only [hfl', ↓reduceIte, spec_ok]
      have hflv : i1.val = len.val := by rw [hfl]
      show Closed cb len.val first.val (last.val - first.val) cb
      refine ⟨rfl, rfl, rfl, ?_⟩
      intro r hr
      by_cases hrf : r ≤ first.val
      · rw [ite_eq_left hrf]
      · exfalso
        omega
    · simp only [hfl, ↓reduceIte]
      by_cases hg1 : gap = 1#usize
      · have hg1' : (gap = 1#usize) = True := eq_true hg1
        simp only [hg1', ↓reduceIte]
        have hg1v : gap.val = 1 := by scalar_tac
        step as ⟨a, ha⟩
        step as ⟨b, hb⟩
        refine spec_mono (move_down_spec cb cap head a b (by omega) (by omega) (by scalar_tac)
          (by scalar_tac)) ?_
        rintro cb' ⟨hh', hl', he', hbl', hw'⟩
        have hc' : capOf cb' = capOf cb := by
          unfold capOf
          rw [hbl']
        have hf' : firstOf cb' = firstOf cb := by
          unfold firstOf
          rw [hc', hh']
        show Closed cb len.val first.val (last.val - first.val) cb'
        refine ⟨hc', hl', he', ?_⟩
        intro r hr
        rw [hc', hf', ← hcap, ← hhead, hw' r (by omega)]
        by_cases hrf : r ≤ first.val
        · rw [ite_eq_left hrf, ite_eq_right (by scalar_tac)]
        · rw [ite_eq_right hrf, ite_eq_left ⟨by scalar_tac, by scalar_tac⟩]
          exact get?_congr (by rw [← hgv, hg1v])
      · simp only [hg1, ↓reduceIte]
        unfold client_blocks.ClientBlocksCore.pull_down
        have hinit : cb.head = cb.head ∧ cb.len = cb.len ∧ cb.end_clock = cb.end_clock ∧
            cb.buf.val.length = cb.buf.val.length ∧ last.val + 1 ≤ i1.val ∧ i1.val ≤ len.val ∧
            ∀ r : Nat, r < cap.val → cb.buf.val[slotOf cap.val head.val r]? =
              if last.val + 1 - gap.val ≤ r ∧ r + gap.val < i1.val then
                cb.buf.val[slotOf cap.val head.val (r + gap.val)]?
              else cb.buf.val[slotOf cap.val head.val r]? := by
          refine ⟨rfl, rfl, rfl, rfl, by omega, by omega, ?_⟩
          intro r hr
          rw [ite_eq_right (by omega)]
        refine spec_mono (pull_down_loop_spec cb cb cap head len gap i1 (last.val + 1) (by omega)
          (by omega) (by omega) (by omega) (by omega) hinit) ?_
        rintro cb' ⟨hh', hl', he', hbl', hw'⟩
        have hc' : capOf cb' = capOf cb := by
          unfold capOf
          rw [hbl']
        have hf' : firstOf cb' = firstOf cb := by
          unfold firstOf
          rw [hc', hh']
        show Closed cb len.val first.val (last.val - first.val) cb'
        refine ⟨hc', hl', he', ?_⟩
        intro r hr
        rw [hc', hf', ← hcap, ← hhead, hw' r (by omega), hgv]
        by_cases hrf : r ≤ first.val
        · rw [ite_eq_left hrf, ite_eq_right (by omega)]
        · rw [ite_eq_right hrf, ite_eq_left ⟨by omega, by omega⟩]
  · simp only [hae, ↓reduceIte]
    step as ⟨count, hcount⟩
    step as ⟨gap, hgap⟩
    have hcv : count.val = first.val + 1 := by scalar_tac
    have hgv : gap.val = last.val - first.val := by scalar_tac
    unfold client_blocks.ClientBlocksCore.close_from_start
    have hmoved : ∀ cb1 : client_blocks.ClientBlocksCore,
        (cb1.head = cb.head ∧ cb1.len = cb.len ∧ cb1.end_clock = cb.end_clock ∧
          cb1.buf.val.length = cb.buf.val.length ∧
          ∀ r : Nat, r < cap.val →
            (gap.val ≤ r ∧ r < count.val + gap.val →
              cb1.buf.val[slotOf cap.val head.val r]? =
                cb.buf.val[slotOf cap.val head.val (r - gap.val)]?) ∧
            (count.val + gap.val ≤ r →
              cb1.buf.val[slotOf cap.val head.val r]? =
                cb.buf.val[slotOf cap.val head.val r]?)) →
        (do
          let head1 ← client_blocks.slot_of cap head gap
          let i2 ← lift (UScalar.cast .U32 head1)
          ok { cb1 with head := i2 }) ⦃ cb' =>
            Closed cb len.val first.val (last.val - first.val) cb' ⦄ := by
      rintro cb1 ⟨hh1, hl1, he1, hbl1, hw1⟩
      step as ⟨head1, hhead1, hhead1lt⟩
      step with UScalar.cast_inBounds_spec UScalarTy.U32 head1 (by scalar_tac) as ⟨i2, hi2⟩
      have hc' : capOf { cb1 with head := i2 } = capOf cb := by
        unfold capOf
        show min cb1.buf.val.length 4294967295 = _
        rw [hbl1]
      have hf' : firstOf { cb1 with head := i2 } = head1.val :=
        firstOf_of_head hc' hi2 (Or.inl (by omega))
      refine ⟨hc', hl1, he1, ?_⟩
      intro r hr
      rw [hc', hf', ← hcap, hhead1, slotOf_shift (by omega) (by omega) (by omega), ← hhead]
      show cb1.buf.val[slotOf cap.val head.val (r + gap.val)]? = _
      rw [← hgv]
      by_cases hrf : r ≤ first.val
      · rw [ite_eq_left hrf, (hw1 (r + gap.val) (by omega)).1 ⟨by omega, by omega⟩]
        exact get?_congr (by congr 1; omega)
      · rw [ite_eq_right hrf, (hw1 (r + gap.val) (by omega)).2 (by omega)]
    by_cases hfew : gap <= client_blocks.FEW_PASSES
    · simp only [hfew, ↓reduceIte]
      unfold client_blocks.ClientBlocksCore.push_up_few
      have hinit : cb.head = cb.head ∧ cb.len = cb.len ∧ cb.end_clock = cb.end_clock ∧
          cb.buf.val.length = cb.buf.val.length ∧ (0#usize : Std.Usize).val ≤ gap.val ∧
          ∀ r : Nat, r < cap.val →
            ((0#usize : Std.Usize).val ≤ r ∧ r < count.val + (0#usize : Std.Usize).val →
              cb.buf.val[slotOf cap.val head.val r]? =
                cb.buf.val[slotOf cap.val head.val (r - (0#usize : Std.Usize).val)]?) ∧
            (count.val + (0#usize : Std.Usize).val ≤ r →
              cb.buf.val[slotOf cap.val head.val r]? =
                cb.buf.val[slotOf cap.val head.val r]?) := by
        refine ⟨rfl, rfl, rfl, rfl, by rw [z]; omega, ?_⟩
        intro r hr
        exact ⟨fun _ => get?_congr (by rw [z, Nat.sub_zero]), fun _ => rfl⟩
      refine spec_bind (push_up_few_loop_spec cb cb cap head count gap 0#usize (by omega)
        (by omega) (by omega) hinit) ?_
      intro cb1 h1
      exact hmoved cb1 h1
    · simp only [hfew, ↓reduceIte]
      unfold client_blocks.ClientBlocksCore.push_up
      have hinit : cb.head = cb.head ∧ cb.len = cb.len ∧ cb.end_clock = cb.end_clock ∧
          cb.buf.val.length = cb.buf.val.length ∧ count.val ≤ count.val ∧
          ∀ r : Nat, r < cap.val → cb.buf.val[slotOf cap.val head.val r]? =
            if count.val + gap.val ≤ r ∧ r < count.val + gap.val then
              cb.buf.val[slotOf cap.val head.val (r - gap.val)]?
            else cb.buf.val[slotOf cap.val head.val r]? := by
        refine ⟨rfl, rfl, rfl, rfl, Nat.le_refl _, ?_⟩
        intro r hr
        rw [ite_eq_right (by omega)]
      refine spec_bind (push_up_loop_spec cb cb cap head gap count count.val (by omega)
        (by omega) (by omega) (by omega) hinit) ?_
      rintro cb1 ⟨hh1, hl1, he1, hbl1, hw1⟩
      exact hmoved cb1 ⟨hh1, hl1, he1, hbl1, fun r hr =>
        ⟨fun hc1 => by rw [hw1 r hr, ite_eq_left hc1],
          fun hc2 => by rw [hw1 r hr, ite_eq_right (by omega)]⟩⟩

end YoctoCore.Properties.Ring
