-- theorem of recursive states
-- all these states' usage is to search 0
import GoldbachTm.Tm25.TuringMachine25

namespace Tm25

-- left
theorem rec13 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨13, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨13, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) l (List.cons Γ.one r)
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

theorem rec14 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨14, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨14, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
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

theorem rec23 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨23, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨23, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) l (List.cons Γ.one r)
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

--right
theorem rec11 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨11, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero r) ⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨11, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ l), Turing.ListBlank.mk r⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) (List.cons Γ.one l) r
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

theorem rec19 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨19, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero r) ⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨19, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ l), Turing.ListBlank.mk r⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) (List.cons Γ.one l) r
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

theorem rec22 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨22, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero r) ⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨22, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ l), Turing.ListBlank.mk r⟩⟩ := by
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

end Tm25
