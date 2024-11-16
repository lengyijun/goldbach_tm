import GoldbachTm.Tm26.TuringMachine26
import GoldbachTm.Basic

open Tm26

unsafe def foo (cfg : Cfg) : IO Unit :=
match (step machine cfg) with
| some cfg => do
                IO.println s!"{cfg}"
                foo cfg
| none => IO.println s!"halt"


unsafe def main : List String → IO Unit
| _ => foo (init [])
