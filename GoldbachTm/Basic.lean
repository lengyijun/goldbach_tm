import Mathlib.Computability.TuringMachine
import Mathlib.Data.Nat.Prime.Defs

inductive Γ
  | zero
  | one
   deriving DecidableEq

instance : Inhabited Γ := ⟨ Γ.zero ⟩

instance : ToString Γ where
  toString
    | Γ.zero => "0"
    | Γ.one => "1"

structure Stmt where
  move : Turing.Dir
  write : Γ

def Goldbach (n : ℕ) := ∃ (x y: ℕ), x + y = n /\ Nat.Prime x /\ Nat.Prime y

def goldbach_search_aux (n : ℕ) : ℕ → Option ℕ
| k =>
  if h : k ≥ n then none
  else if (Nat.decidablePrime k).decide /\ (Nat.decidablePrime (n-k)).decide then
    some k
  else
    goldbach_search_aux n (k+1)
termination_by k => n - k
decreasing_by omega

def goldbach_search (n : ℕ) : Option ℕ := goldbach_search_aux n 2

theorem goldbach_search_aux_exists (n : ℕ) (k : ℕ) (x : ℕ) : x ≥ k → Nat.Prime x → Nat.Prime (n-x) → goldbach_search_aux n k ≠ none := by
have hi : ∃ i , i = n - k := by use (n-k)
obtain ⟨i, hi⟩ := hi
revert k
induction i with intros k _ _ _ hp2
| zero => have h : n - x = 0 := by omega
          rw [h] at hp2
          apply Nat.Prime.ne_zero at hp2
          omega
| succ i induction_step =>
            unfold goldbach_search_aux
            simp
            constructor
            . omega
            . split
              . tauto
              . apply induction_step (k+1) (by omega)
                any_goals assumption
                by_cases x = k
                . subst x
                  tauto
                . omega

theorem goldbach_search_aux_correct (n : ℕ) (k : ℕ) (p : ℕ) : goldbach_search_aux n k = some p →
p < n ∧ Nat.Prime p ∧ Nat.Prime (n - p) := by
have hi : ∃ i , i = n - k := by use (n-k)
obtain ⟨i, hi⟩ := hi
revert k
induction i with intros k _ h
| zero =>
  unfold goldbach_search_aux at h
  simp at h
  omega
| succ i induction_step =>
  unfold goldbach_search_aux at h
  simp at h
  obtain ⟨_, h⟩ := h
  split at h
  . simp at h
    subst p
    tauto
  . apply induction_step (k+1) (by omega) h


theorem goldbach_def_search (n : ℕ) : Goldbach n ↔ goldbach_search n ≠ none :=
⟨by intros h
    obtain ⟨x, y, _, h, _⟩ := h
    apply goldbach_search_aux_exists _ _ x
    any_goals assumption
    . apply Nat.Prime.two_le at h
      omega
    . have : y = n - x := by omega
      subst y
      assumption
,
by intros h
   cases h : (goldbach_search n) with
   | some p => use! p, n-p
               apply goldbach_search_aux_correct at h
               repeat any_goals apply And.intro
               any_goals tauto
               all_goals omega
   | none => tauto
⟩


instance decidableGoldbach (n : ℕ) : Decidable (Goldbach n) :=
decidable_of_iff' _ (goldbach_def_search n)

instance : DecidablePred Goldbach := decidableGoldbach

theorem unlimitedQ (Q : ℕ → Prop)
               (base : ℕ) (hbase : Q base)
               (hq : ∀ x, Q x → ∃ y > x, Q y) :
               ∀ n, ∃ m > n, Q m := by
intros n
induction n with
| zero => cases base with
          | zero => apply hq at hbase
                    tauto
          | succ base => use (base+1)
                         constructor
                         . omega
                         . tauto
| succ n induction_step =>
            obtain ⟨m, _, _⟩ := induction_step
            by_cases hm: m = n + 1
            . subst m
              apply hq
              tauto
            . use m
              constructor
              . omega
              . assumption


/-
P i => nth_cfg i ≠ none
Q i n => nth_cfg i = some ⟨⟨24, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (2*n+4) Γ.one), Turing.ListBlank.mk []⟩⟩
-/
theorem propagating_induction (P : ℕ → Prop) (Q : ℕ → ℕ → Prop)
               (base : ℕ) (hbase : Q base 0)
               (hq : ∀ i n, Q i n → ∃ j > i, Q j (n+1))
               (pq : ∀ i n, Q i n → ∀ j ≤ i, P j)
: ∀ j, P j := by
intro j
have h := unlimitedQ (fun i => ∃ n, Q i n) base ⟨0, hbase⟩
simp at h
refine (?_ ∘ h) ?_
. intros g
  obtain ⟨i, hi, n, hqin⟩ := g j
  apply pq i n hqin
  omega
. intros i m hqim
  obtain ⟨j, _, _⟩ := hq i m hqim
  use j
  constructor
  . omega
  . use (m+1)
