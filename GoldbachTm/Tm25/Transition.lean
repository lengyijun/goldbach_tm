import GoldbachTm.Tm25.TuringMachine25
import GoldbachTm.Tm25.Search0

namespace Tm25

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

theorem lemma_15_to_18 (i : ℕ) (l1: ℕ) (l r : List Γ)
(h :
nth_cfg i = some ⟨⟨15, by omega⟩, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate l1 Γ.one ++ List.cons Γ.zero l),
  Turing.ListBlank.mk r,
  ⟩⟩) :
∃ j, nth_cfg (j + i) = some ⟨⟨18, by omega⟩, ⟨Γ.zero,
    Turing.ListBlank.mk l,
    Turing.ListBlank.mk (List.replicate (l1+1) Γ.one ++ r),
    ⟩⟩
:= by
forward h
cases l1 with simp! [*, -nth_cfg] at h
| zero => use 1
          simp [h]
| succ r1 =>  apply rec18 at h
              use (r1+2)
              ring_nf at *
              simp [h]
              rw [List.append_cons, ← List.replicate_succ']
              ring_nf

end Tm25
