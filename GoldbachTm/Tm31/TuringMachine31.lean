-- inspired by https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Computability/TuringMachine.lean
import Mathlib.Computability.TuringMachine
import Mathlib.Tactic.Ring.RingNF
import GoldbachTm.Basic
import GoldbachTm.Format
import GoldbachTm.ListBlank

namespace Tm31

def Machine := Fin 31 → Γ → Option (Fin 31 × Stmt)

structure Cfg where
  /-- The current machine state. -/
  q : Fin 31
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
  fun ⟨q, T⟩ ↦ (M q T.head).map fun ⟨q', a⟩ ↦ ⟨q', (T.write a.write).move a.move⟩


def machine : Machine
| ⟨000, _⟩, Γ.zero => some ⟨⟨006, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨000, _⟩, Γ.one  => some ⟨⟨001, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨001, _⟩, Γ.zero => some ⟨⟨018, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨001, _⟩, Γ.one  => some ⟨⟨002, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨002, _⟩, Γ.zero => some ⟨⟨022, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨002, _⟩, Γ.one  => some ⟨⟨003, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨003, _⟩, Γ.zero => some ⟨⟨022, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨003, _⟩, Γ.one  => some ⟨⟨004, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨004, _⟩, Γ.zero => some ⟨⟨018, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨004, _⟩, Γ.one  => some ⟨⟨005, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨005, _⟩, Γ.zero => some ⟨⟨006, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨005, _⟩, Γ.one  => some ⟨⟨005, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨006, _⟩, Γ.zero => some ⟨⟨011, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨006, _⟩, Γ.one  => some ⟨⟨007, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨007, _⟩, Γ.zero => some ⟨⟨008, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨007, _⟩, Γ.one  => some ⟨⟨007, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨008, _⟩, Γ.zero => some ⟨⟨010, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨008, _⟩, Γ.one  => some ⟨⟨009, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨009, _⟩, Γ.zero => some ⟨⟨011, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨009, _⟩, Γ.one  => some ⟨⟨009, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨010, _⟩, Γ.zero => some ⟨⟨011, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨010, _⟩, Γ.one  => some ⟨⟨010, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨011, _⟩, Γ.zero => some ⟨⟨024, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨011, _⟩, Γ.one  => some ⟨⟨012, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨012, _⟩, Γ.zero => some ⟨⟨013, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨012, _⟩, Γ.one  => some ⟨⟨012, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨013, _⟩, Γ.zero => some ⟨⟨014, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨013, _⟩, Γ.one  => some ⟨⟨013, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨014, _⟩, Γ.zero => some ⟨⟨016, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨014, _⟩, Γ.one  => some ⟨⟨015, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨015, _⟩, Γ.zero => some ⟨⟨008, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨015, _⟩, Γ.one  => some ⟨⟨015, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨016, _⟩, Γ.zero => some ⟨⟨017, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨016, _⟩, Γ.one  => some ⟨⟨016, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨017, _⟩, Γ.zero => some ⟨⟨004, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨017, _⟩, Γ.one  => some ⟨⟨020, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨018, _⟩, Γ.zero => some ⟨⟨019, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨018, _⟩, Γ.one  => some ⟨⟨018, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨019, _⟩, Γ.zero => some ⟨⟨028, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨019, _⟩, Γ.one  => some ⟨⟨026, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨020, _⟩, Γ.zero => some ⟨⟨021, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨020, _⟩, Γ.one  => some ⟨⟨020, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨021, _⟩, Γ.zero => some ⟨⟨002, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨021, _⟩, Γ.one  => some ⟨⟨021, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨022, _⟩, Γ.zero => some ⟨⟨023, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨022, _⟩, Γ.one  => some ⟨⟨022, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨023, _⟩, Γ.zero => some ⟨⟨011, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨023, _⟩, Γ.one  => some ⟨⟨027, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨024, _⟩, Γ.zero => some ⟨⟨025, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨024, _⟩, Γ.one  => some ⟨⟨024, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨025, _⟩, Γ.zero => some ⟨⟨026, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨025, _⟩, Γ.one  => some ⟨⟨025, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨026, _⟩, Γ.zero => some ⟨⟨028, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨026, _⟩, Γ.one  => some ⟨⟨000, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨027, _⟩, Γ.zero => some ⟨⟨000, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨027, _⟩, Γ.one  => some ⟨⟨027, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨028, _⟩, Γ.zero => some ⟨⟨030, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨028, _⟩, Γ.one  => some ⟨⟨029, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨029, _⟩, Γ.zero => none
| ⟨029, _⟩, Γ.one  => some ⟨⟨026, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨030, _⟩, Γ.zero => some ⟨⟨028, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨030, _⟩, Γ.one  => some ⟨⟨030, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨_+31, _⟩, _ => by omega -- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Pattern.20matching.20on.20Fin.20isn't.20exhaustive.20for.20large.20matches/near/428048252

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

theorem cfg6 : nth_cfg 6 = some ⟨25,
        { head := default, left := Turing.ListBlank.mk (List.replicate 4 Γ.one), right := Turing.ListBlank.mk [] } ⟩ := by
have h : nth_cfg 0 = init [] := by simp!
simp [init, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk'] at h
forward h h 0
forward h h 1
forward h h 2
forward h h 3
forward h h 4
forward h h 5
assumption

end Tm31
