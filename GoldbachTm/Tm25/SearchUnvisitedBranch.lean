import GoldbachTm.Tm25.TuringMachine25
import GoldbachTm.Basic
import Init.Data.List.Basic

set_option maxHeartbeats 0

open Tm25

unsafe def foo (cfg : Cfg) (unvisited : List (Fin 25 × Γ)): IO Unit :=
do
  let unvisited <- pure (List.removeAll unvisited [⟨cfg.q, cfg.Tape.head⟩])
  IO.println s!"{unvisited}"
  match (step machine cfg) with
  | some cfg => IO.println s!"{cfg}"
                foo cfg unvisited
  | none => IO.println s!"halt"


unsafe def main : List String → IO Unit
| _ => foo (init []) ([
  ⟨00, by omega⟩,
  ⟨01, by omega⟩,
  ⟨02, by omega⟩,
  ⟨03, by omega⟩,
  ⟨04, by omega⟩,
  ⟨05, by omega⟩,
  ⟨06, by omega⟩,
  ⟨07, by omega⟩,
  ⟨08, by omega⟩,
  ⟨09, by omega⟩,
  ⟨10, by omega⟩,
  ⟨11, by omega⟩,
  ⟨12, by omega⟩,
  ⟨13, by omega⟩,
  ⟨14, by omega⟩,
  ⟨15, by omega⟩,
  ⟨16, by omega⟩,
  ⟨17, by omega⟩,
  ⟨18, by omega⟩,
  ⟨19, by omega⟩,
  ⟨20, by omega⟩,
  ⟨21, by omega⟩,
  ⟨22, by omega⟩,
  ⟨23, by omega⟩,
  ⟨24, by omega⟩].map (fun q => [⟨q, Γ.zero⟩, ⟨q, Γ.one⟩])).flatten
