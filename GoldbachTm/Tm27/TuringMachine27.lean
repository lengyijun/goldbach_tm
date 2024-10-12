-- inspired by https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Computability/TuringMachine.lean
import Mathlib.Computability.TuringMachine
import GoldbachTm.Basic
import GoldbachTm.Format
import GoldbachTm.ListBlank

namespace Tm27

def Machine := Fin 27 → Γ → Option (Fin 27 × Stmt)

structure Cfg where
  /-- The current machine state. -/
  q : Fin 27
  /-- The current state of the tape: current symbol, left and right parts. -/
  Tape : Turing.Tape Γ


instance : ToString Cfg where
  toString := fun ⟨q, ⟨head, l, r⟩⟩ ↦
    let l : String := join ((to_list_rev l).map ToString.toString)
    let r : String := join ((to_list r).map ToString.toString)
    let s : String := if l == "" then s!"[{head}]{r}"
                                 else s!" {l}[{head}]{r}"
    if q < 10 then
      s!" {q}   {s}"
    else
      s!"{q}   {s}"

/-- The initial configuration. -/
def init (l : List Γ) : Cfg := ⟨⟨0, by omega⟩, Turing.Tape.mk₁ l⟩

/-- Execution semantics of the Turing machine. -/
def step (M : Machine) : Cfg → Option Cfg :=
  fun ⟨q, T⟩ ↦ (M q T.1).map fun ⟨q', a⟩ ↦ ⟨q', (T.write a.write).move a.move⟩


def machine : Machine
| ⟨ 0, _⟩, Γ.zero => some ⟨⟨23, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨ 0, _⟩, Γ.one  => some ⟨⟨01, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨ 1, _⟩, Γ.zero => some ⟨⟨17, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 1, _⟩, Γ.one  => some ⟨⟨02, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨ 2, _⟩, Γ.zero => some ⟨⟨21, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 2, _⟩, Γ.one  => some ⟨⟨03, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨ 3, _⟩, Γ.zero => some ⟨⟨21, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 3, _⟩, Γ.one  => some ⟨⟨04, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 4, _⟩, Γ.zero => some ⟨⟨09, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨ 4, _⟩, Γ.one  => some ⟨⟨05, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨ 5, _⟩, Γ.zero => some ⟨⟨04, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨ 5, _⟩, Γ.one  => some ⟨⟨05, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 6, _⟩, Γ.zero => some ⟨⟨08, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 6, _⟩, Γ.one  => some ⟨⟨07, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 7, _⟩, Γ.zero => some ⟨⟨09, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨ 7, _⟩, Γ.one  => some ⟨⟨07, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 8, _⟩, Γ.zero => some ⟨⟨09, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨ 8, _⟩, Γ.one  => some ⟨⟨08, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 9, _⟩, Γ.zero => some ⟨⟨10, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨ 9, _⟩, Γ.one  => some ⟨⟨26, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨10, _⟩, Γ.zero => some ⟨⟨10, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨10, _⟩, Γ.one  => some ⟨⟨11, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨11, _⟩, Γ.zero => some ⟨⟨12, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨11, _⟩, Γ.one  => some ⟨⟨11, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨12, _⟩, Γ.zero => some ⟨⟨14, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨12, _⟩, Γ.one  => some ⟨⟨13, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨13, _⟩, Γ.zero => some ⟨⟨06, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨13, _⟩, Γ.one  => some ⟨⟨13, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨14, _⟩, Γ.zero => some ⟨⟨15, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨14, _⟩, Γ.one  => some ⟨⟨14, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨15, _⟩, Γ.zero => some ⟨⟨16, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨15, _⟩, Γ.one  => some ⟨⟨19, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨16, _⟩, Γ.zero => some ⟨⟨17, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨16, _⟩, Γ.one  => none -- unreachable
| ⟨17, _⟩, Γ.zero => some ⟨⟨18, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨17, _⟩, Γ.one  => some ⟨⟨17, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨18, _⟩, Γ.zero => some ⟨⟨09, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨18, _⟩, Γ.one  => some ⟨⟨25, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨19, _⟩, Γ.zero => some ⟨⟨20, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨19, _⟩, Γ.one  => some ⟨⟨19, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨20, _⟩, Γ.zero => some ⟨⟨02, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨20, _⟩, Γ.one  => some ⟨⟨20, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨21, _⟩, Γ.zero => some ⟨⟨22, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨21, _⟩, Γ.one  => some ⟨⟨21, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨22, _⟩, Γ.zero => some ⟨⟨00, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨22, _⟩, Γ.one  => some ⟨⟨24, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨23, _⟩, Γ.zero => some ⟨⟨24, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨23, _⟩, Γ.one  => some ⟨⟨23, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨24, _⟩, Γ.zero => some ⟨⟨00, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨24, _⟩, Γ.one  => some ⟨⟨24, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨25, _⟩, Γ.zero => none
| ⟨25, _⟩, Γ.one  => some ⟨⟨24, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨26, _⟩, Γ.zero => some ⟨⟨18, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨26, _⟩, Γ.one  => some ⟨⟨26, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨_+27, _⟩, _ => by omega -- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Pattern.20matching.20on.20Fin.20isn't.20exhaustive.20for.20large.20matches/near/428048252

end Tm27