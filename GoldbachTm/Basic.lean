import Mathlib.Computability.TuringMachine

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
