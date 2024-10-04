import GoldbachTm.TuringMachine31
import GoldbachTm.Basic

open Tm31

unsafe def foo (cfg : Cfg) : IO Unit :=
match (step machine cfg) with
| some cfg => do
                IO.println s!"{cfg}"
                foo cfg
| none => IO.println s!"halt"


unsafe def main : List String → IO Unit
| _ => foo (init [])
