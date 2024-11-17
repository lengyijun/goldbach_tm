-- inspired by https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Computability/TuringMachine.lean
import Mathlib.Computability.TuringMachine
import Mathlib.Tactic.Ring.RingNF
import GoldbachTm.Basic
import GoldbachTm.Format
import GoldbachTm.ListBlank

namespace Tm25

open Lean Meta Elab Tactic Std Term

def Machine := Fin 25 → Γ → Option (Fin 25 × Stmt)

structure Cfg where
  /-- The current machine state. -/
  q : Fin 25
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
| ⟨ 0, _⟩, Γ.zero => some ⟨⟨22, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨ 0, _⟩, Γ.one  => some ⟨⟨ 1, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨ 1, _⟩, Γ.zero => some ⟨⟨16, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 1, _⟩, Γ.one  => some ⟨⟨ 2, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨ 2, _⟩, Γ.zero => some ⟨⟨20, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 2, _⟩, Γ.one  => some ⟨⟨ 3, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨ 3, _⟩, Γ.zero => some ⟨⟨20, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 3, _⟩, Γ.one  => some ⟨⟨ 4, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 4, _⟩, Γ.zero => some ⟨⟨16, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨ 4, _⟩, Γ.one  => some ⟨⟨ 5, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨ 5, _⟩, Γ.zero => some ⟨⟨ 7, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨ 5, _⟩, Γ.one  => some ⟨⟨ 5, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 6, _⟩, Γ.zero => some ⟨⟨ 8, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 6, _⟩, Γ.one  => some ⟨⟨ 7, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 7, _⟩, Γ.zero => some ⟨⟨ 9, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨ 7, _⟩, Γ.one  => some ⟨⟨ 7, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 8, _⟩, Γ.zero => some ⟨⟨ 9, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨ 8, _⟩, Γ.one  => some ⟨⟨ 8, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨ 9, _⟩, Γ.zero => some ⟨⟨10, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨ 9, _⟩, Γ.one  => some ⟨⟨21, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨10, _⟩, Γ.zero => some ⟨⟨10, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨10, _⟩, Γ.one  => some ⟨⟨11, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨11, _⟩, Γ.zero => some ⟨⟨12, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨11, _⟩, Γ.one  => some ⟨⟨11, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨12, _⟩, Γ.zero => some ⟨⟨14, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨12, _⟩, Γ.one  => some ⟨⟨13, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨13, _⟩, Γ.zero => some ⟨⟨ 6, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨13, _⟩, Γ.one  => some ⟨⟨13, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨14, _⟩, Γ.zero => some ⟨⟨15, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨14, _⟩, Γ.one  => some ⟨⟨14, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨15, _⟩, Γ.zero => some ⟨⟨ 4, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨15, _⟩, Γ.one  => some ⟨⟨18, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨16, _⟩, Γ.zero => some ⟨⟨17, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨16, _⟩, Γ.one  => some ⟨⟨16, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨17, _⟩, Γ.zero => some ⟨⟨ 9, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨17, _⟩, Γ.one  => some ⟨⟨24, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨18, _⟩, Γ.zero => some ⟨⟨19, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨18, _⟩, Γ.one  => some ⟨⟨18, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨19, _⟩, Γ.zero => some ⟨⟨ 2, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨19, _⟩, Γ.one  => some ⟨⟨19, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨20, _⟩, Γ.zero => some ⟨⟨23, by omega⟩, ⟨Turing.Dir.left, Γ.zero⟩⟩
| ⟨20, _⟩, Γ.one  => some ⟨⟨20, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨21, _⟩, Γ.zero => some ⟨⟨17, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨21, _⟩, Γ.one  => some ⟨⟨21, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨22, _⟩, Γ.zero => some ⟨⟨23, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨22, _⟩, Γ.one  => some ⟨⟨22, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨23, _⟩, Γ.zero => some ⟨⟨ 0, by omega⟩, ⟨Turing.Dir.right, Γ.zero⟩⟩
| ⟨23, _⟩, Γ.one  => some ⟨⟨23, by omega⟩, ⟨Turing.Dir.left, Γ.one⟩⟩
| ⟨24, _⟩, Γ.zero => none
| ⟨24, _⟩, Γ.one  => some ⟨⟨23, by omega⟩, ⟨Turing.Dir.right, Γ.one⟩⟩
| ⟨_+25, _⟩, _ => by omega -- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Pattern.20matching.20on.20Fin.20isn't.20exhaustive.20for.20large.20matches/near/428048252

def nth_cfg : (n : Nat) -> Option Cfg
| 0 => init []
| Nat.succ n => match (nth_cfg n) with
                | none => none
                | some cfg =>  step machine cfg


-- https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/binderIdent.20vs.20Ident/near/402516388
def toBinderIdent (i : Ident) : TSyntax ``binderIdent := Unhygienic.run <|
  withRef i `(binderIdent| $i:ident)

elab "forward" g:ident : tactic => withSynthesize <| withMainContext do
  let some ldecl := (← getLCtx).findFromUserName? g.getId
    | throwErrorAt g m!"Identifier {g} not found"
  match ldecl with
  | LocalDecl.cdecl _ _ _ (Expr.app (Expr.app _ (Expr.app _ arg)) _) _ _ =>
      let argType ← inferType arg
      if ← isDefEq argType (mkConst ``Nat) then
        let arg ← Elab.Term.exprToSyntax arg
        evalTactic (← `(tactic| (
            have h : nth_cfg ($arg + 1) = nth_cfg ($arg + 1) := rfl
            nth_rewrite 2 [nth_cfg] at h
            simp [*, step, Option.map, machine, Turing.Tape.write, Turing.Tape.move] at h
            try simp! [*, -nth_cfg] at h
            try ring_nf at h
            clear $g
            rename_i $(toBinderIdent g)
        )))
      else
        throwError "The first argument of {g} is not a Nat"
  | _ => logInfo m!"please forward on nth_cfg i = some ⟨...⟩"


theorem cfg45 : nth_cfg 45 = some ⟨21,
        { head := default, left := Turing.ListBlank.mk (List.replicate 4 Γ.one), right := Turing.ListBlank.mk [] } ⟩ := by
have h : nth_cfg 0 = init [] := by simp!
simp [init, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk'] at h
iterate 45 forward h
simp [h]
constructor
. tauto
. simp! [Turing.ListBlank.mk]
  rw [Quotient.eq'']
  right
  use 2
  tauto


end Tm25
