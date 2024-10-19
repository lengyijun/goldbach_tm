import GoldbachTm.Tm27.TuringMachine27
import GoldbachTm.Tm27.Search0

namespace Tm27

theorem lemma_10_to_11 (i : ℕ) (r1: ℕ) (l r : List Γ)
(h :
nth_cfg i = some ⟨⟨10, by omega⟩, ⟨Γ.one,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate r1 Γ.one ++ List.cons Γ.zero r)⟩⟩) :

∃ j, nth_cfg (j + i) = some ⟨⟨11, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate r1 Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩
:= by
forward h
cases r1 with
| zero => use 1
          simp [h]
| succ r1 => apply rec11 at h
             use (r1 + 2)
             rw [← h]
             ring_nf

theorem lemma_15_to_19 (i : ℕ) (l1: ℕ) (l r : List Γ)
(h :
nth_cfg i = some ⟨⟨15, by omega⟩, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate l1 Γ.one ++ List.cons Γ.zero l),
  Turing.ListBlank.mk r,
  ⟩⟩) :
∃ j, nth_cfg (j + i) = some ⟨⟨19, by omega⟩, ⟨Γ.zero,
    Turing.ListBlank.mk l,
    Turing.ListBlank.mk (List.replicate (l1+1) Γ.one ++ r),
    ⟩⟩
:= by
forward h
cases l1 with simp! [*, -nth_cfg] at h
| zero => use 1
          simp [h]
| succ r1 =>  apply rec19 at h
              use (r1+2)
              ring_nf at *
              simp [h]
              rw [List.append_cons, ← List.replicate_succ']
              ring_nf

theorem lemma_22_to_24 (i : ℕ) (l1: ℕ) (l r : List Γ)
(h :
nth_cfg i = some ⟨⟨22, by omega⟩, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate l1 Γ.one ++ List.cons Γ.zero l),
  Turing.ListBlank.mk r,
  ⟩⟩) :

∃ j, nth_cfg (j + i) = some ⟨⟨24, by omega⟩, ⟨Γ.zero,
    Turing.ListBlank.mk l,
    Turing.ListBlank.mk (List.replicate (l1+1) Γ.one ++ r),
    ⟩⟩
:= by
forward h
cases l1 with
| zero => use 1
          simp [h]
| succ l1 => apply rec24 at h
             use (l1 + 2)
             ring_nf at *
             simp [h]
             rw [List.append_cons, ← List.replicate_succ']
             ring_nf

end Tm27
