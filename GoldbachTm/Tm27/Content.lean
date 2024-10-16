import GoldbachTm.Tm27.TuringMachine27
import GoldbachTm.Tm27.Search0
import GoldbachTm.Tm27.PBP
import Mathlib.Data.Nat.Prime.Defs

namespace Tm27

theorem lemma_26 (n : ℕ) (i : ℕ)
(even_n : Even (n+2))
(g :
nth_cfg i = some ⟨⟨26, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (n+4) Γ.one), Turing.ListBlank.mk []⟩⟩ )
( hpp : goldbach (n+4)) :
∃ j>i, nth_cfg j = some ⟨⟨26, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (n+4+2) Γ.one), Turing.ListBlank.mk []⟩⟩
:= by
forward g g i
repeat rw [← List.replicate_succ] at g
apply (leap_18 _ _ 0) at g
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
(∀ i < n, goldbach (2*i+4)) ->
∃ j, nth_cfg j = some ⟨⟨26, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (2*n+4) Γ.one), Turing.ListBlank.mk []⟩⟩
 := by
induction n with
| zero =>
intros _
use 45
simp [cfg45]
tauto
| succ n =>
rename_i induction_step
intros h
refine (?_ ∘ induction_step) ?_
. intros g
  obtain ⟨j, g⟩ := g
  specialize h n (by omega)
  apply lemma_26 at g
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
goldbach (2*n + 4)
:= by
induction' n using Nat.strongRecOn with n IH
apply never_halt_step at IH
obtain ⟨j, g⟩ := IH
by_contra! h
forward g g j
repeat rw [← List.replicate_succ] at g
apply (leap_18_halt _ _ 0) at g
any_goals omega
refine (?_ ∘ g) ?_
. intros h
  obtain ⟨k, h⟩ := h
  apply never_none _ h
. intros x y _
  apply h ⟨x, y, ?_⟩
  ring_nf at *
  tauto


theorem halt_lemma_rev' (h : ∀ n, goldbach (2*n+4)) :
∀ i, nth_cfg i ≠ none := by
apply propagating_induction (fun i => nth_cfg i ≠ none) (fun i n => nth_cfg i = some ⟨⟨26, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (2*n+4) Γ.one), Turing.ListBlank.mk []⟩⟩) 45
. simp [cfg45]; tauto
. intros i n g
  apply (lemma_26 (2*n)) at g
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
    | succ k => rename_i h₁
                forward h₁ h₁ (j+k)
                rw [← h₁]
                ring_nf
  specialize h₂ (i-j)
  have h₃ : j + (i-j) = i := by omega
  rw [h₃] at h₂
  rw [h₂] at g
  tauto

theorem halt_lemma':
(∃ n, ¬ goldbach (2*n+4)) → (∃ i, nth_cfg i = none)
:= by
intros h
obtain ⟨j, hj⟩ := never_halt_step (Nat.find h) (λ i g =>
by rw [← Mathlib.Tactic.PushNeg.not_not_eq (goldbach (2*i+4))]
   apply Nat.find_min h g
)
forward hj
repeat rw [← List.replicate_succ] at hj
apply (leap_18_halt _ _ 0) at hj
any_goals omega
apply hj
intros x y _
apply Nat.find_spec h
use! x, y

theorem halt_lemma_rev :
(∃ i, nth_cfg i = none) → (∃ n, ¬ goldbach (2*n+4))
:= by
intros h
by_contra! g
apply halt_lemma_rev' at g
tauto

end Tm27
