-- some helper of ListBlank
import Mathlib.Computability.TuringMachine
import GoldbachTm.Basic

def to_list_rev (l : Turing.ListBlank Γ) : List Γ := by
  apply l.liftOn (fun l ↦ l.reverse.dropWhile (fun c ↦ c == Γ.zero))
  rintro a _ ⟨i, rfl⟩
  cases a <;> simp
  . tauto
  . induction i
    . tauto
    . simp [*]
      tauto

def to_list (l : Turing.ListBlank Γ) : List Γ := l |> to_list_rev |> List.reverse

theorem to_list_rev_rfl (l : List Γ) : to_list_rev (Turing.ListBlank.mk l) = l.reverse.dropWhile (fun c ↦ c == Γ.zero) := rfl

theorem to_list_rev_one (l : Turing.ListBlank Γ) : to_list_rev (l.cons Γ.one) = (to_list_rev l) ++ [Γ.one] := by
  refine l.inductionOn fun l ↦ ?_
  suffices to_list_rev ((Turing.ListBlank.mk l).cons Γ.one) = (to_list_rev (Turing.ListBlank.mk l)) ++ [Γ.one] by exact this
  rw [Turing.ListBlank.cons_mk, to_list_rev_rfl, to_list_rev_rfl]
  simp
  rw [List.dropWhile_append]
  simp

def count1 (l : Turing.ListBlank Γ) : Nat :=
match head_h : l.head with
| Γ.zero => 0
| Γ.one =>
  let h : to_list_rev l = (to_list_rev l.tail) ++ [Γ.one] := by
    rw [← Turing.ListBlank.cons_head_tail l, ← to_list_rev_one, head_h]
    simp
  let _termination_proof : (l |> to_list_rev |> List.length) > (l.tail |> to_list_rev |> List.length):= by rw [h]; simp
  1 + count1 l.tail
termination_by (l |> to_list_rev |> List.length)
