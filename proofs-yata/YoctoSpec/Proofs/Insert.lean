/-
Integration preserves the invariant: `legal_integrate`.
-/
import YoctoSpec.Proofs.Scan

namespace YoctoSpec

theorem not_some_of_fresh {s : List Item} {o : Option Id} {x : Id} (hp : Present s o)
    (hf : ∀ a, a ∈ s → a.id ≠ x) : o ≠ some x := by
  intro e
  obtain ⟨a, ha, e'⟩ := ix_le_length_iff.mp (hp x e)
  exact hf a ha e'

theorem length_ins (p q : List Item) (i : Item) :
    (p ++ i :: q).length = (p ++ q).length + 1 := by
  simp only [List.length_append, List.length_cons]
  omega

theorem present_ins {p q : List Item} {i : Item} {o : Option Id} (h : Present (p ++ q) o)
    (hf : ∀ a, a ∈ p ++ q → a.id ≠ i.id) : Present (p ++ i :: q) o := by
  intro y hy
  have hne : i.id ≠ y := by
    intro e
    exact not_some_of_fresh h hf (by rw [hy, e])
  rw [ix_ins hne, length_ins]
  have := h y hy
  have := sh_spec p.length (ix (p ++ q) y)
  omega

def rankO (rank : Id → Nat) : Option Id → Nat
  | none => 0
  | some x => rank x

/-- Inserting `i` at a position the scan accepts keeps the sequence legal. -/
theorem Legal.insert {p q : List Item} {i : Item} (hs : Legal (p ++ q))
    (hi : CanIntegrate (p ++ q) i) (hp : ScanPost (p ++ q) i p.length) :
    Legal (p ++ i :: q) := by
  have hid : ∀ a, a ∈ p ++ q → i.id ≠ a.id := fun a ha e => hi.fresh a ha e.symm
  have oix : ∀ a, a ∈ p ++ q → ix (p ++ i :: q) a.id = sh p.length (ix (p ++ q) a.id) :=
    fun a ha => ix_ins (hid a ha)
  have oL : ∀ a, a ∈ p ++ q →
      ixL (p ++ i :: q) a.left = sh p.length (ixL (p ++ q) a.left) :=
    fun a ha => ixL_ins (not_some_of_fresh (hs.left_present ha) hi.fresh)
  have oR : ∀ a, a ∈ p ++ q →
      ixR (p ++ i :: q) a.right = sh p.length (ixR (p ++ q) a.right) :=
    fun a ha => ixR_ins (not_some_of_fresh (hs.right_mem a ha) hi.fresh)
  have nix : ix (p ++ i :: q) i.id = p.length + 1 :=
    ix_append_cons_self i q (fun a ha => hi.fresh a (List.mem_append_left _ ha))
  have nL : ixL (p ++ i :: q) i.left = sh p.length (ixL (p ++ q) i.left) :=
    ixL_ins (not_some_of_fresh hi.left_mem hi.fresh)
  have nR : ixR (p ++ i :: q) i.right = sh p.length (ixR (p ++ q) i.right) :=
    ixR_ins (not_some_of_fresh hi.right_mem hi.fresh)
  have hlo := hp.lo
  have hhi := hp.hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- nodup
    have hn := hs.nodup
    unfold NodupIds at hn ⊢
    rw [List.pairwise_append] at hn ⊢
    refine ⟨hn.1, ?_, ?_⟩
    · rw [List.pairwise_cons]
      refine ⟨?_, hn.2.1⟩
      intro b hb
      exact fun e => hi.fresh b (List.mem_append_right _ hb) e.symm
    · intro a ha b hb
      rcases List.mem_cons.mp hb with e | hb
      · rw [e]
        exact hi.fresh a (List.mem_append_left _ ha)
      · exact hn.2.2 a ha b hb
  · -- left_lt
    intro a ha
    rcases mem_ins.mp ha with e | ha
    · rw [e, nix, nL]
      have := sh_spec p.length (ixL (p ++ q) i.left)
      omega
    · rw [oix a ha, oL a ha]
      have := hs.left_lt a ha
      have := sh_spec p.length (ixL (p ++ q) a.left)
      have := sh_spec p.length (ix (p ++ q) a.id)
      omega
  · -- lt_right
    intro a ha
    rcases mem_ins.mp ha with e | ha
    · rw [e, nix, nR]
      have := sh_spec p.length (ixR (p ++ q) i.right)
      omega
    · rw [oix a ha, oR a ha]
      have := hs.lt_right a ha
      have := sh_spec p.length (ixR (p ++ q) a.right)
      have := sh_spec p.length (ix (p ++ q) a.id)
      omega
  · -- right_mem
    intro a ha
    rcases mem_ins.mp ha with e | ha
    · rw [e]
      exact present_ins hi.right_mem hi.fresh
    · exact present_ins (hs.right_mem a ha) hi.fresh
  · -- rule
    intro a ha b hb hlt
    unfold Rule
    rcases mem_ins.mp ha with ea | ha
    · rcases mem_ins.mp hb with eb | hb
      · rw [ea, eb] at hlt
        omega
      · rw [ea, nix, oix b hb] at hlt
        rw [ea, nix, nL, nR, oix b hb, oL b hb]
        have s1 := sh_spec p.length (ix (p ++ q) b.id)
        have s2 := sh_spec p.length (ixL (p ++ q) b.left)
        have s3 := sh_spec p.length (ixL (p ++ q) i.left)
        have s4 := sh_spec p.length (ixR (p ++ q) i.right)
        rcases hp.goodB b hb (by omega) with g | g | g | g
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (Or.inl (by omega)))
        · exact Or.inr (Or.inr (Or.inr g))
    · rcases mem_ins.mp hb with eb | hb
      · rw [eb, nix, oix a ha] at hlt
        rw [eb, nix, nL, oix a ha, oL a ha, oR a ha]
        have s1 := sh_spec p.length (ix (p ++ q) a.id)
        have s2 := sh_spec p.length (ixL (p ++ q) a.left)
        have s3 := sh_spec p.length (ixL (p ++ q) i.left)
        have s4 := sh_spec p.length (ixR (p ++ q) a.right)
        rcases hp.goodA a ha (by omega) with g | g | g | g
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (Or.inl (by omega)))
        · exact Or.inr (Or.inr (Or.inr g))
      · rw [oix a ha, oix b hb] at hlt
        rw [oix a ha, oix b hb, oL a ha, oL b hb, oR a ha]
        have s1 := sh_spec p.length (ix (p ++ q) a.id)
        have s2 := sh_spec p.length (ix (p ++ q) b.id)
        have s3 := sh_spec p.length (ixL (p ++ q) a.left)
        have s4 := sh_spec p.length (ixL (p ++ q) b.left)
        have s5 := sh_spec p.length (ixR (p ++ q) a.right)
        rcases hs.rule a ha b hb (by omega) with g | g | g | g
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (Or.inl (by omega)))
        · exact Or.inr (Or.inr (Or.inr g))
  · -- rightLeft
    intro a ha y hy hr
    have hyo : y ∈ p ++ q := by
      rcases mem_ins.mp hy with e | hy
      · exfalso
        rcases mem_ins.mp ha with ea | ha
        · exact not_some_of_fresh hi.right_mem hi.fresh (by rw [ea, e] at hr; exact hr)
        · exact not_some_of_fresh (hs.right_mem a ha) hi.fresh (by rw [e] at hr; exact hr)
      · exact hy
    rcases mem_ins.mp ha with ea | ha
    · rw [ea, nL, oL y hyo]
      have := hi.rightLeft y hyo (by rw [ea] at hr; exact hr)
      have := sh_spec p.length (ixL (p ++ q) y.left)
      have := sh_spec p.length (ixL (p ++ q) i.left)
      omega
    · rw [oL a ha, oL y hyo]
      have := hs.rightLeft a ha y hyo hr
      have := sh_spec p.length (ixL (p ++ q) y.left)
      have := sh_spec p.length (ixL (p ++ q) a.left)
      omega
  · -- acyclic
    obtain ⟨rank, hrank⟩ := hs.acyclic
    refine ⟨fun x => if x = i.id then rankO rank i.left + rankO rank i.right + 1 else rank x, ?_⟩
    intro a ha x hx
    show (if x = i.id then rankO rank i.left + rankO rank i.right + 1 else rank x) <
      (if a.id = i.id then rankO rank i.left + rankO rank i.right + 1 else rank a.id)
    rcases mem_ins.mp ha with ea | ha
    · rw [ea] at hx
      have hxne : x ≠ i.id := by
        intro e
        rw [e] at hx
        rcases hx with hx | hx
        · exact not_some_of_fresh hi.left_mem hi.fresh hx
        · exact not_some_of_fresh hi.right_mem hi.fresh hx
      rw [ea, ite_eq_right hxne, ite_eq_left rfl]
      rcases hx with hx | hx
      · rw [hx]
        simp only [rankO]
        omega
      · rw [hx]
        simp only [rankO]
        omega
    · have hxne : x ≠ i.id := by
        intro e
        rw [e] at hx
        rcases hx with hx | hx
        · exact not_some_of_fresh (hs.left_present ha) hi.fresh hx
        · exact not_some_of_fresh (hs.right_mem a ha) hi.fresh hx
      rw [ite_eq_right hxne, ite_eq_right (hi.fresh a ha)]
      exact hrank a ha x hx

/-- `integrate` inserts the item after the position the scan returns. -/
theorem integrate_eq (s : List Item) (i : Item) :
    integrate s i =
      s.take (ixL s (findConflictLeft i i.right (owner s) (after i.left s) i.left [] [])) ++
        i :: s.drop (ixL s (findConflictLeft i i.right (owner s) (after i.left s) i.left [] [])) := by
  unfold integrate
  rw [insertAfter_eq]

theorem mem_integrate {s : List Item} {i a : Item} : a ∈ integrate s i ↔ a = i ∨ a ∈ s := by
  rw [integrate_eq, mem_ins, List.take_append_drop]

/-- Integration preserves the invariant. -/
theorem legal_integrate {s : List Item} {i : Item} (hs : Legal s) (hi : CanIntegrate s i) :
    Legal (integrate s i) := by
  have hp := scan_integrate hs hi
  rw [integrate_eq]
  generalize ixL s (findConflictLeft i i.right (owner s) (after i.left s) i.left [] []) = k at hp ⊢
  have hk : k ≤ s.length := by
    have := hp.hi
    have := ixR_le s i.right
    omega
  have hlen : (s.take k).length = k := by
    rw [List.length_take]
    omega
  have e : s.take k ++ s.drop k = s := List.take_append_drop k s
  apply Legal.insert
  · rw [e]; exact hs
  · rw [e]; exact hi
  · rw [e, hlen]; exact hp

end YoctoSpec
