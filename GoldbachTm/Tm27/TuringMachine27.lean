-- inspired by https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Computability/TuringMachine.lean
import Mathlib.Computability.TuringMachine
import Mathlib.Data.Real.Sqrt
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

def nth_cfg : (n : Nat) -> Option Cfg
| 0 => init []
| Nat.succ n => match (nth_cfg n) with
                | none => none
                | some cfg =>  step machine cfg


-- g1 = g2
macro "forward" g1:ident g2:Lean.binderIdent i:term: tactic => `(tactic| (
have h : nth_cfg ($i + 1) = nth_cfg ($i + 1) := rfl
nth_rewrite 2 [nth_cfg] at h
simp [*, step, Option.map, machine, Turing.Tape.write, Turing.Tape.move] at h
try simp! [*, -nth_cfg] at h
try ring_nf at h
clear $g1
rename_i $g2
))

theorem cfg45 : nth_cfg 45 = some ⟨26,
        { head := default, left := Turing.ListBlank.mk (List.replicate 4 Γ.one), right := Turing.ListBlank.mk [] } ⟩ := by
have h : nth_cfg 0 = init [] := by simp!
simp [init, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk'] at h
forward h h 0
forward h h 1
forward h h 2
forward h h 3
forward h h 4
forward h h 5
forward h h 6
forward h h 7
forward h h 8
forward h h 9
forward h h 10
forward h h 11
forward h h 12
forward h h 13
forward h h 14
forward h h 15
forward h h 16
forward h h 17
forward h h 18
forward h h 19
forward h h 20
forward h h 21
forward h h 22
forward h h 23
forward h h 24
forward h h 25
forward h h 26
forward h h 27
forward h h 28
forward h h 29
forward h h 30
forward h h 31
forward h h 32
forward h h 33
forward h h 34
forward h h 35
forward h h 36
forward h h 37
forward h h 38
forward h h 39
forward h h 40
forward h h 41
forward h h 42
forward h h 43
forward h h 44
simp [h]
constructor
. tauto
. simp! [Turing.ListBlank.mk]
  rw [Quotient.eq'']
  right
  use 2
  tauto


end Tm27
