-- some lemmas tm31 doesn't contain

import GoldbachTm.Tm27.TuringMachine27
import GoldbachTm.Tm27.Transition

namespace Tm27

theorem lemma7 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨7, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨7, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (k+1) Γ.zero ++ r)⟩⟩ := by
induction k with (intros i l r h; simp_all)
| zero => forward h h i
          rw [← h]
          ring_nf
| succ k => forward h h i
            rename_i induction_step
            apply induction_step at h
            ring_nf at *
            simp! [h]
            rw [List.append_cons]
            rw [← List.replicate_succ']
            ring_nf

theorem lemma8 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨8, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 2) = some ⟨⟨9, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (Γ.zero :: l), Turing.ListBlank.mk (List.replicate k Γ.zero ++ r)⟩⟩ := by
induction k with (intros i l r h; simp_all)
| zero => forward h h i
          forward h h (1+i)
          rw [← h]
          ring_nf
| succ k => forward h h i
            rename_i induction_step
            apply induction_step at h
            ring_nf at *
            simp! [h]
            rw [List.append_cons]
            rw [← List.replicate_succ']
            ring_nf

theorem lemma5 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨5, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 2) = some ⟨⟨4, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (Γ.zero :: l), Turing.ListBlank.mk (List.replicate k Γ.zero ++ r)⟩⟩ := by
induction k with (intros i l r h; simp_all)
| zero => forward h h i
          forward h h (1+i)
          rw [← h]
          ring_nf
| succ k => forward h h i
            rename_i induction_step
            apply induction_step at h
            ring_nf at *
            simp! [h]
            rw [List.append_cons]
            rw [← List.replicate_succ']
            ring_nf

theorem lemma10 (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨10, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate k Γ.zero ++ List.cons Γ.one r) ⟩⟩ →
nth_cfg (i + k + 1) = some ⟨⟨10, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ l), Turing.ListBlank.mk r⟩⟩ := by
induction k with (intros i l r h; simp_all)
| zero => forward h h i
          rw [← h]
          ring_nf
| succ k => rename_i induction_step
            specialize induction_step (i+1) (List.cons Γ.one l) r
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ' (k+1)]
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

theorem lemma_6_to_7 (i : ℕ) (l1: ℕ) (l r : List Γ)
(h :
nth_cfg i = some ⟨⟨6, by omega⟩, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate l1 Γ.one ++ List.cons Γ.zero l),
  Turing.ListBlank.mk r,
  ⟩⟩) :
∃ j>i, nth_cfg j = some ⟨⟨7, by omega⟩, ⟨Γ.zero,
    Turing.ListBlank.mk l,
    Turing.ListBlank.mk (List.replicate (l1+1) Γ.zero ++ r),
    ⟩⟩
:= by
forward h h i
cases l1 with
| zero => use (1+i)
          simp [h]
| succ l1 => simp! at h
             apply lemma7 at h
             use (1+i+l1 + 1)
             simp [h]
             constructor
             . omega
             . rw [List.append_cons, ← List.replicate_succ']

theorem lemma_9_to_10 (i : ℕ) (r1: ℕ) (l r : List Γ)
(h :
nth_cfg i = some ⟨⟨9, by omega⟩, ⟨Γ.zero,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate r1 Γ.zero ++ List.cons Γ.one r),
  ⟩⟩) :
∃ j>i, nth_cfg j = some ⟨⟨10, by omega⟩, ⟨Γ.one,
    Turing.ListBlank.mk (List.replicate r1 Γ.one ++ Γ.zero :: l),
    Turing.ListBlank.mk r,
    ⟩⟩
:= by
forward h h i
cases r1 with simp_all
| zero => use (1+i)
          simp [h]
| succ l1 => simp! at h
             apply lemma10 at h
             use (1+i+l1 + 1)
             simp [h]
             omega

end Tm27
