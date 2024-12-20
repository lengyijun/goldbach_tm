-- theorem of recursive states
-- all these states' usage is to search 0
import GoldbachTm.Tm31.TuringMachine31

namespace Tm31

-- left
theorem rec5 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨5, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨5, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) l (List.cons Γ.one r)
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

theorem rec9 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨9, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨9, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) l (List.cons Γ.one r)
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

theorem rec10 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨10, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨10, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) l (List.cons Γ.one r)
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

theorem rec15 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨15, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨15, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) l (List.cons Γ.one r)
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

theorem rec16 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨16, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨16, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) l (List.cons Γ.one r)
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

theorem rec18 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨18, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨18, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) l (List.cons Γ.one r)
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

theorem rec20 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨20, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨20, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) l (List.cons Γ.one r)
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

theorem rec22 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨22, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨22, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) l (List.cons Γ.one r)
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

theorem rec27 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨27, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨27, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) l (List.cons Γ.one r)
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]


-- right
theorem rec7 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨7, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero r) ⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨7, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ l), Turing.ListBlank.mk r⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) (List.cons Γ.one l) r
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

theorem rec12 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨12, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero r) ⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨12, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ l), Turing.ListBlank.mk r⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) (List.cons Γ.one l) r
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

theorem rec13 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨13, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero r) ⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨13, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ l), Turing.ListBlank.mk r⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) (List.cons Γ.one l) r
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

theorem rec21 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨21, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero r) ⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨21, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ l), Turing.ListBlank.mk r⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) (List.cons Γ.one l) r
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

theorem rec24 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨24, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero r) ⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨24, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ l), Turing.ListBlank.mk r⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) (List.cons Γ.one l) r
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

theorem rec25 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨25, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero r) ⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨25, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ l), Turing.ListBlank.mk r⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) (List.cons Γ.one l) r
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

theorem rec30 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨30, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero r) ⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨30, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ l), Turing.ListBlank.mk r⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) (List.cons Γ.one l) r
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

end Tm31
