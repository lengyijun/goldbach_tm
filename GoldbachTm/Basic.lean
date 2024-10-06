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

def goldbach (n : ℕ) := ∃ (x y: ℕ), x + y = n /\ Nat.Prime x /\ Nat.Prime y
