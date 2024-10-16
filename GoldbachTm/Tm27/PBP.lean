-- PDP is short for "prime board prime"
import GoldbachTm.Tm27.TuringMachine27
import GoldbachTm.Tm27.Search0
import GoldbachTm.Tm27.Prime
import Mathlib.Data.Nat.Prime.Defs

namespace Tm27

-- l1 : count of 1 on the left
-- r1 : count of 1 on the right
theorem lemma_18 (i l1 r1: ℕ)
(hp : ¬ Nat.Prime (l1+1) \/ ¬ Nat.Prime (r1+1))
(g :
nth_cfg i = some ⟨⟨18, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate (l1+1) Γ.one), Turing.ListBlank.mk (List.replicate (r1+1) Γ.one)⟩⟩
):
∃ j>i, nth_cfg j = some ⟨⟨18, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate l1 Γ.one), Turing.ListBlank.mk (List.replicate (r1+2) Γ.one)⟩⟩ := by
forward g g i
forward g g (1+i)
forward g g (2+i)
by_cases hr1 : Nat.Prime (r1+1)
. refine (?_ ∘ (prime_21 (3+i) r1 (Γ.one :: List.replicate l1 Γ.one) [])) ?_
  . intros g
    specialize g hr1
    obtain ⟨j, _, g⟩ := g
    forward g g j
    refine (?_ ∘ (lemma_22_to_24 (1+j) l1 [] (Γ.zero :: Γ.one :: (List.replicate r1 Γ.one ++ [Γ.zero])))) ?_
    . intros g
      obtain ⟨k, g⟩ := g
      forward g g (k+(1+j))
      have h : ¬ Nat.Prime (l1+1) := by tauto
      apply n_prime_17 at h
      pick_goal 5
      . rw [g]
        simp
        repeat any_goals apply And.intro
        all_goals rfl
      obtain ⟨m, _, h⟩ := h
      forward h h m
      forward h h (1+m)
      forward h h (2+m)
      apply rec26 at h
      forward h h (3+m+l1+1)
      use (5+m+l1)
      constructor
      . omega
      . simp [h]
        repeat any_goals apply And.intro
        all_goals simp! [Turing.ListBlank.mk]
        all_goals rw [Quotient.eq'']
        all_goals right
        . use 2
          tauto
        . use 1
          simp
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
. apply n_prime_17 at hr1
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
  obtain ⟨j, _, g⟩ := hr1
  forward g g j
  use (1+j)
  constructor
  . omega
  . simp! [g]
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
(even_sum : Even (l1+r1))
(g :
nth_cfg i = some ⟨⟨18, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate (l1+1) Γ.one), Turing.ListBlank.mk (List.replicate (r1+1) Γ.one)⟩⟩
) :
∃ j>i, nth_cfg j = some ⟨⟨26, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (l1+r1+4) Γ.one), Turing.ListBlank.mk []⟩⟩ := by
forward g g i
forward g g (1+i)
forward g g (2+i)
apply prime_21 at hpr
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
clear g
obtain ⟨j, _, g⟩ := hpr
forward g g j
refine (?_ ∘ (lemma_22_to_24 (1+j) l1 []  (Γ.zero :: Γ.one :: (List.replicate r1 Γ.one ++ [Γ.zero])))) ?_
. intros h
  obtain ⟨k, h⟩ := h
  forward h h (k+(1+j))
  apply prime_21 at hpl
  pick_goal 5
  . rw [h]
    simp
    constructor <;> rfl
  obtain ⟨m, _, g⟩ := hpl
  forward g g m
  forward g g (1+m)
  forward g g (2+m)
  apply rec23 at g
  forward g g (3+m+l1+1)
  rw [← List.cons_append] at g
  rw [← List.replicate_succ] at g
  rw [← List.cons_append] at g
  rw [← List.replicate_succ] at g
  rw [List.append_cons] at g
  rw [← List.replicate_succ'] at g
  apply rec24 at g
  forward g g (5+m+l1+(l1+1)+1)
  rw [← List.cons_append] at g
  rw [← List.replicate_succ] at g
  rw [← List.cons_append] at g
  rw [← List.replicate_succ] at g
  rw [List.append_cons] at g
  rw [← List.replicate_succ'] at g
  rw [← List.append_assoc] at g
  rw [← List.replicate_add] at g
  apply n_prime_17 at g
  refine (?_ ∘ g) ?_
  . clear g
    intros g
    obtain ⟨n, _, g⟩ := g
    forward g g n
    forward g g (1+n)
    forward g g (2+n)
    rw [← List.cons_append] at g
    rw [← List.replicate_succ] at g
    apply rec26 at g
    use (3 + n + (2 + l1 + r1 + 1) + 1)
    constructor
    . omega
    . rw [g]
      simp [Turing.ListBlank.mk]
      rw [Quotient.eq'']
      right
      use 2
      ring_nf
      tauto
  . apply (@Nat.not_prime_of_dvd_of_lt 2)
    any_goals omega
    ring_nf
    rw [add_assoc]
    apply Nat.dvd_add
    . omega
    . apply Even.two_dvd
      assumption
. rw [g]
  simp! [Turing.ListBlank.mk]
  rw [Quotient.eq'']
  left
  use 1
  tauto


theorem leap_18 (l1 : ℕ) : ∀ (i r1: ℕ),
l1 + r1 ≥ 2 →
Even (l1+r1) →
nth_cfg i = some ⟨⟨18, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate (l1+1) Γ.one), Turing.ListBlank.mk (List.replicate (r1+1) Γ.one)⟩⟩ →
(∃ x y, x + y = l1 + r1 + 2 /\ Nat.Prime x /\ Nat.Prime y /\ (r1+1) ≤ x /\ x ≤ y) →
∃ j>i, nth_cfg j = some ⟨⟨26, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (l1+r1+4) Γ.one), Turing.ListBlank.mk []⟩⟩
:= by
induction l1 with
| zero => omega
| succ l1 =>
  rename_i induction_step
  intros i r1 h _ g hpp
  by_cases hp : ¬ Nat.Prime (l1+2) \/ ¬ Nat.Prime (r1+1)
  . -- induction step
    apply lemma_18 at g
    any_goals tauto
    obtain ⟨j, _, g⟩ := g
    apply induction_step at g
    all_goals ring_nf at *
    any_goals assumption
    refine (?_ ∘ g) ?_
    . intros g
      obtain ⟨m, g₂⟩ := g
      use m
      ring_nf at *
      simp [g₂]
      omega
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
                  ring_nf at *
                  assumption
      | inr hp => apply hp
                  ring_nf at *
                  assumption
  . -- both prime
    apply both_prime at g
    all_goals tauto


theorem leap_18_halt (l1 : ℕ) : ∀ (i r1: ℕ),
l1 + r1 ≥ 2 →
nth_cfg i = some ⟨⟨18, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate (l1+1) Γ.one), Turing.ListBlank.mk (List.replicate (r1+1) Γ.one)⟩⟩ →
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
  forward g g (1+i)
  forward g g (2+i)
  rw [← List.replicate_succ] at g
  rw [← List.replicate_succ] at g
  by_cases hp : Nat.Prime (r2+3)
  . apply prime_21 at hp
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
    obtain ⟨j, _, h⟩ := hp
    forward h h j
    forward h h (1+j)
    forward h h (2+j)
    forward h h (3+j)
    forward h h (4+j)
    forward h h (5+j)
    forward h h (6+j)
    forward h h (7+j)
    forward h h (8+j)
    forward h h (9+j)
    forward h h (10+j)
    forward h h (11+j)
    forward h h (12+j)
    use (13+j)
  . apply n_prime_17 at hp
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
    obtain ⟨j, _, h⟩ := hp
    forward h h j
    forward h h (1+j)
    forward h h (2+j)
    use (3+j)
| succ l1 =>
    intros i r1 h g hpp
    apply lemma_18 at g
    . rename_i induction_step
      obtain ⟨j, _, g⟩ := g
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
      tauto

end Tm27
