-- PDP is short for "prime board prime"
import GoldbachTm.Tm31.TuringMachine31
import GoldbachTm.Tm31.Search0
import GoldbachTm.Tm31.Prime
import Mathlib.Data.Nat.Prime.Defs

namespace Tm31

-- l1 : count of 1 on the left
-- r1 : count of 1 on the right
theorem lemma_26 (i l1 r1: ℕ)
(hp : ¬ Nat.Prime (l1+1) \/ ¬ Nat.Prime (r1+1))
(g :
nth_cfg i = some ⟨⟨26, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate (l1+1) Γ.one), Turing.ListBlank.mk (List.replicate (r1+1) Γ.one)⟩⟩
):
∃ j, nth_cfg (i+j) = some ⟨⟨28, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate l1 Γ.one), Turing.ListBlank.mk (List.replicate (r1+2) Γ.one)⟩⟩ := by
forward g g i
by_cases hr1 : Nat.Prime (r1+1)
. refine (?_ ∘ (lemma_23 (1+i) r1 (Γ.one :: List.replicate l1 Γ.one) [])) ?_
  . intros g
    specialize g hr1
    obtain ⟨j, g⟩ := g
    forward g g (1+i+j)
    refine (?_ ∘ (lemma_23_to_27 (2+i+j) l1 [] (Γ.zero :: Γ.one :: (List.replicate r1 Γ.one ++ [Γ.zero])))) ?_
    . intros g
      obtain ⟨k, g⟩ := g
      forward g g (k+(2+i+j))
      have h : ¬ Nat.Prime (l1+1) := by tauto
      apply lemma_not_prime at h
      pick_goal 5
      . rw [g]
        simp
        repeat any_goals apply And.intro
        all_goals rfl
      obtain ⟨m, h⟩ := h
      forward h h (3+k+i+j+m)
      forward h h (4+k+i+j+m)
      forward h h (5+k+i+j+m)
      apply rec30 at h
      forward h h (6+k+i+j+m+l1+1)
      use (8+k+j+m+l1)
      ring_nf at *
      simp [h]
      repeat any_goals apply And.intro
      all_goals simp! [Turing.ListBlank.mk]
      all_goals rw [Quotient.eq'']
      all_goals right
      . use 2
        tauto
      . use 1
        simp
        rw [← List.cons_append]
        rw [← List.cons_append]
        rw [← List.replicate_succ]
        rw [← List.replicate_succ]
        ring_nf
        tauto
    . simp! [g, Turing.ListBlank.mk]
      rw [Quotient.eq'']
      left
      use 1
      tauto
  . simp! [g, Turing.ListBlank.mk]
    rw [Quotient.eq'']
    left
    use 1
    tauto
. apply lemma_not_prime at hr1
  pick_goal 5
  . rw [g]
    simp
    repeat any_goals apply And.intro
    . rfl
    . simp! [Turing.ListBlank.mk]
      rw [Quotient.eq'']
      left
      use 1
      tauto
  obtain ⟨j, g⟩ := hr1
  forward g g (1+i+j)
  forward g g (2+i+j)
  forward g g (3+i+j)
  use (4+j)
  ring_nf at *
  simp! [g]
  simp! [Turing.ListBlank.mk]
  rw [Quotient.eq'']
  right
  use 1
  rw [← List.cons_append]
  rw [← List.replicate_succ]
  rw [← List.cons_append]
  rw [← List.replicate_succ]
  ring_nf
  tauto


-- +2
theorem both_prime (i l1 r1: ℕ)
(hpl : Nat.Prime (l1+1))
(hpr : Nat.Prime (r1+1))
(g :
nth_cfg i = some ⟨⟨26, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate (l1+1) Γ.one), Turing.ListBlank.mk (List.replicate (r1+1) Γ.one)⟩⟩
) :
∃ j, nth_cfg (i+j) = some ⟨⟨25, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (l1+r1+4) Γ.one), Turing.ListBlank.mk []⟩⟩ := by
forward g g i
apply lemma_23 at hpr
pick_goal 5
. rw [g]
  simp
  constructor
  . rfl
  . simp! [Turing.ListBlank.mk]
    rw [Quotient.eq'']
    left
    use 1
    tauto
obtain ⟨j, g⟩ := hpr
forward g g (1+i+j)
refine (?_ ∘ (lemma_23_to_27 (2+i+j) l1 [] (Γ.zero :: Γ.one :: (List.replicate r1 Γ.one ++ [Γ.zero])))) ?_
. intros g
  obtain ⟨k, g⟩ := g
  forward g g (k+(2+i+j))
  apply lemma_23 at hpl
  pick_goal 5
  . rw [g]
    simp
    constructor <;> rfl
  obtain ⟨m, g⟩ := hpl
  forward g g (3+k+i+j+m)
  forward g g (4+k+i+j+m)
  forward g g (5+k+i+j+m)
  apply rec24 at g
  forward g g (6+k+i+j+m+l1+1)
  apply rec25 at g
  use (9 + k + j + m + l1 + r1)
  ring_nf at *
  rename_i h
  simp [h]
  simp! [Turing.ListBlank.mk]
  rw [Quotient.eq'']
  right
  use 1
  rw [← List.cons_append]
  rw [← List.replicate_succ]
  rw [← List.cons_append]
  rw [← List.replicate_succ]
  rw [← List.append_assoc]
  rw [← List.replicate_add]
  rw [List.append_cons]
  rw [← List.replicate_succ']
  ring_nf
  tauto
. rw [g]
  simp! [Turing.ListBlank.mk]
  rw [Quotient.eq'']
  left
  use 1
  tauto


theorem leap_26 (l1 : ℕ) : ∀ (i r1: ℕ),
l1 + r1 ≥ 2 →
nth_cfg i = some ⟨⟨26, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate (l1+1) Γ.one), Turing.ListBlank.mk (List.replicate (r1+1) Γ.one)⟩⟩ →
(∃ x y, x + y = l1 + r1 + 2 /\ Nat.Prime x /\ Nat.Prime y /\ (r1+1) ≤ x /\ x ≤ y) →
∃ j, nth_cfg (i+j) = some ⟨⟨25, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (l1+r1+4) Γ.one), Turing.ListBlank.mk []⟩⟩
:= by
induction l1 with
| zero => omega
| succ l1 =>
  rename_i induction_step
  intros i r1 h g hpp
  by_cases hp : ¬ Nat.Prime (l1+2) \/ ¬ Nat.Prime (r1+1)
  . -- induction step
    apply lemma_26 at g
    any_goals tauto
    obtain ⟨j, g⟩ := g
    forward g g (i+j)
    forward g g (1+i+j)
    repeat rw [← List.replicate_succ] at g
    apply induction_step at g
    any_goals omega
    refine (?_ ∘ g) ?_
    . intros g
      obtain ⟨m, g₂⟩ := g
      use (2+j+m)
      ring_nf at *
      simp [g₂]
    . obtain ⟨x, y, _, _, _, _⟩ := hpp
      use! x, y
      repeat any_goals apply And.intro
      any_goals assumption
      any_goals omega
      by_cases x = r1+1
      any_goals omega
      subst x
      exfalso
      cases hp with
      | inl hp => apply hp
                  have : y = l1+2 := by omega
                  subst y
                  assumption
      | inr hp => apply hp
                  assumption
  . -- both prime
    apply both_prime at g
    all_goals tauto

theorem leap_26_halt (l1 : ℕ) : ∀ (i r1: ℕ),
l1 + r1 ≥ 2 →
nth_cfg i = some ⟨⟨26, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate (l1+1) Γ.one), Turing.ListBlank.mk (List.replicate (r1+1) Γ.one)⟩⟩ →
(∀ x y, x + y = l1 + r1 + 2 /\ Nat.Prime x /\ Nat.Prime y → False) →
∃ j, nth_cfg j = none
:= by
induction l1 with
| zero =>
  intros i r1 h g hpp
  have hr1 : ∃ r2, r2 + 2 = r1 := by use (r1-2); omega
  obtain ⟨r2, _⟩ := hr1
  subst r1
  forward g g i
  rw [← List.replicate_succ] at g
  rw [← List.replicate_succ] at g
  by_cases hp : Nat.Prime (r2+3)
  . apply lemma_23 at hp
    pick_goal 5
    . rw [g]
      simp
      constructor
      . rfl
      . simp! [Turing.ListBlank.mk]
        rw [Quotient.eq'']
        left
        use 1
        tauto
    obtain ⟨j, h⟩ := hp
    forward h h (1+i+j)
    forward h h (2+i+j)
    forward h h (3+i+j)
    forward h h (4+i+j)
    forward h h (5+i+j)
    forward h h (6+i+j)
    forward h h (7+i+j)
    forward h h (8+i+j)
    forward h h (9+i+j)
    forward h h (10+i+j)
    forward h h (11+i+j)
    forward h h (12+i+j)
    forward h h (13+i+j)
    use (14+i+j)
  . apply lemma_not_prime at hp
    pick_goal 5
    . rw [g]
      simp
      constructor
      . rfl
      . simp! [Turing.ListBlank.mk]
        rw [Quotient.eq'']
        left
        use 1
        tauto
    obtain ⟨j, h⟩ := hp
    forward h h (1+i+j)
    forward h h (2+i+j)
    forward h h (3+i+j)
    forward h h (4+i+j)
    forward h h (5+i+j)
    use (6+i+j)
| succ l1 =>
    intros i r1 h g hpp
    apply lemma_26 at g
    . obtain ⟨j, g⟩ := g
      forward g g (i+j)
      forward g g (1+i+j)
      rename_i induction_step
      repeat rw [← List.replicate_succ] at g
      apply induction_step at g
      any_goals omega
      apply g
      ring_nf at hpp
      ring_nf
      assumption
    . specialize hpp (l1+2) (r1+1)
      ring_nf at hpp
      simp at hpp
      ring_nf
      by_cases Nat.Prime (2+l1) <;> tauto

end Tm31
