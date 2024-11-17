import GoldbachTm.Tm31.TuringMachine31
import GoldbachTm.Tm31.PBP
import Mathlib.Data.Nat.Prime.Defs

namespace Tm31

theorem lemma_25 (n : ℕ) (i : ℕ)
(g :
nth_cfg i = some ⟨⟨25, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (n+4) Γ.one), Turing.ListBlank.mk []⟩⟩ )
( hpp : Goldbach (n+4)) :
∃ j>0, nth_cfg (i+j) = some ⟨⟨25, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (n+4+2) Γ.one), Turing.ListBlank.mk []⟩⟩
:= by
forward g g i
repeat rw [← List.replicate_succ] at g
apply (leap_26 _ _ 0) at g
any_goals omega
refine (?_ ∘ g) ?_
. intros g
  obtain ⟨k, h⟩ := g
  use (1+k)
  ring_nf at *
  simp [h]
  omega
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
∃ j, nth_cfg j = some ⟨⟨25, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (2*n+4) Γ.one), Turing.ListBlank.mk []⟩⟩
 := by
induction n with
| zero =>
intros _
use 6
simp [cfg6]
tauto
| succ n induction_step =>
intros h
refine (?_ ∘ induction_step) ?_
. intros g
  obtain ⟨j, g⟩ := g
  specialize h n (by omega)
  apply lemma_25 at g
  specialize g h
  obtain ⟨k, g⟩ := g
  use (j+k)
  simp [g]
  ring_nf
. intros i hi
  apply h i (by omega)

theorem never_halt (never_none : ∀ i, nth_cfg i ≠ none) (n : ℕ):
Goldbach (2*n + 4)
:= by
induction' n using Nat.strongRecOn with n IH
apply never_halt_step at IH
obtain ⟨j, g⟩ := IH
by_contra! h
forward g g j
repeat rw [← List.replicate_succ] at g
apply (leap_26_halt _ _ 0) at g
any_goals omega
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
apply propagating_induction (fun i => nth_cfg i ≠ none) (fun i n => nth_cfg i = some ⟨⟨25, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (2*n+4) Γ.one), Turing.ListBlank.mk []⟩⟩) 6
. simp [cfg6]; tauto
. intros i n g
  apply (lemma_25 (2*n)) at g
  specialize g (h _)
  obtain ⟨j, g⟩ := g
  use (i+j)
  simp! [g]
. intros i n g j hij _
  have h₂ : ∀ k, nth_cfg (j+k) = none := by
    intro k
    induction k with
    | zero => tauto
    | succ k h₁ =>  forward h₁ h₁ (j+k)
                    rw [← h₁]
                    ring_nf
  specialize h₂ (i-j)
  have h₃ : j + (i-j) = i := by omega
  rw [h₃] at h₂
  rw [h₂] at g
  tauto

theorem halt_lemma_rev :
(∃ i, nth_cfg i = none) → (∃ n, ¬ Goldbach (2*n+4))
:= by
intros h
by_contra! g
apply halt_lemma_rev' at g
tauto

end Tm31
