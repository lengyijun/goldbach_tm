import GoldbachTm.Tm31.TuringMachine31
import Mathlib.Data.Nat.Prime.Defs

theorem lemma_25 (k : ℕ): ∀ (i : ℕ),
nth_cfg i = some ⟨⟨25, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate k Γ.one), Turing.ListBlank.mk []⟩⟩ →
(¬ (∃ x y, x + y = k /\ Nat.Prime x /\ Nat.Prime y)) →
∃ j, nth_cfg (i+j) = some ⟨⟨25, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (k+2) Γ.one), Turing.ListBlank.mk []⟩⟩
:= by
sorry

theorem halt_lemma :
(∃ (n x y: ℕ), Even n /\ n > 2 /\ x + y = n /\ Nat.Prime x /\ Nat.Prime y) →
∃ i, nth_cfg i = none
:= by
sorry

theorem halt_lemma_rev :
∃ i, nth_cfg i = none →
(∃ (n x y: ℕ), Even n /\ n > 2 /\ x + y = n /\ Nat.Prime x /\ Nat.Prime y)
:= by
sorry
