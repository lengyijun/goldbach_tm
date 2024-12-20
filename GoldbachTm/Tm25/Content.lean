import GoldbachTm.Tm25.TuringMachine25
import GoldbachTm.Tm25.Search0
import GoldbachTm.Tm25.PBP
import Mathlib.Data.Nat.Prime.Defs

namespace Tm25

theorem lemma_21 (n : ℕ) (i : ℕ)
(even_n : Even (n+2))
(g :
nth_cfg i = some ⟨⟨21, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (n+4) Γ.one), Turing.ListBlank.mk []⟩⟩ )
( hpp : Goldbach (n+4)) :
∃ j>i, nth_cfg j = some ⟨⟨21, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (n+4+2) Γ.one), Turing.ListBlank.mk []⟩⟩
:= by
forward g
repeat rw [← List.replicate_succ] at g
apply (leap_17 _ _ 0) at g
any_goals omega
any_goals assumption
refine (?_ ∘ g) ?_
. intros g
  obtain ⟨k, _, h⟩ := g
  use k
  constructor
  . omega
  . simp [h]
. obtain ⟨x, y, _, hx, hy⟩ := hpp
  by_cases x ≤ y
  . use! x, y
    repeat any_goals apply And.intro
    any_goals assumption
    apply Nat.Prime.two_le at hx
    omega
  . use! y, x
    repeat any_goals apply And.intro
    any_goals assumption
    any_goals omega
    apply Nat.Prime.two_le at hy
    omega

lemma never_halt_step (n : ℕ) :
(∀ i < n, Goldbach (2*i+4)) ->
∃ j, nth_cfg j = some ⟨⟨21, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (2*n+4) Γ.one), Turing.ListBlank.mk []⟩⟩
 := by
induction n with
| zero =>
intros _
use 45
simp [cfg45]
tauto
| succ n induction_step =>
intros h
refine (?_ ∘ induction_step) ?_
. intros g
  obtain ⟨j, g⟩ := g
  specialize h n (by omega)
  apply lemma_21 at g
  . specialize g h
    obtain ⟨k, g⟩ := g
    use k
    simp [g]
    ring_nf
  . use (n+1)
    ring_nf
. intros i hi
  apply h i (by omega)

theorem never_halt (never_none : ∀ i, nth_cfg i ≠ none) (n : ℕ):
Goldbach (2*n + 4)
:= by
induction' n using Nat.strongRecOn with n IH
apply never_halt_step at IH
obtain ⟨j, g⟩ := IH
forward g
repeat rw [← List.replicate_succ] at g
apply (leap_17_halt _ _ 0) at g
any_goals omega
by_contra! h
refine (?_ ∘ g) ?_
. intros h
  obtain ⟨k, h⟩ := h
  apply never_none _ h
. intros x y _
  apply h ⟨x, y, ?_⟩
  ring_nf at *
  tauto


theorem halt_lemma_rev' (h : ∀ n, Goldbach (2*n+4)) :
∀ i, nth_cfg i ≠ none := by
apply propagating_induction (fun i => nth_cfg i ≠ none) (fun i n => nth_cfg i = some ⟨⟨21, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (2*n+4) Γ.one), Turing.ListBlank.mk []⟩⟩) 45
. simp [cfg45]; tauto
. intros i n g
  apply (lemma_21 (2*n)) at g
  . specialize g (h _)
    obtain ⟨j, g⟩ := g
    use j
    simp! [g]
  . use (n+1)
    ring_nf
. intros i n g j hij _
  have h₂ : ∀ k, nth_cfg (j+k) = none := by
    intro k
    induction k with
    | zero => tauto
    | succ k => simp! [← add_assoc, *]
  specialize h₂ (i-j)
  have h₃ : j + (i-j) = i := by omega
  rw [h₃] at h₂
  rw [h₂] at g
  tauto

theorem halt_lemma':
(∃ n, ¬ Goldbach (2*n+4)) → (∃ i, nth_cfg i = none)
:= by
intros h
obtain ⟨j, hj⟩ := never_halt_step (Nat.find h) (λ i g =>
by rw [← Mathlib.Tactic.PushNeg.not_not_eq (Goldbach (2*i+4))]
   apply Nat.find_min h g
)
forward hj
repeat rw [← List.replicate_succ] at hj
apply (leap_17_halt _ _ 0) at hj
any_goals omega
apply hj
intros x y _
apply Nat.find_spec h
use! x, y

theorem halt_lemma_rev :
(∃ i, nth_cfg i = none) → (∃ n, ¬ Goldbach (2*n+4))
:= by
intros h
by_contra! g
apply halt_lemma_rev' at g
tauto

end Tm25
