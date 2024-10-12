import GoldbachTm.Tm31.TuringMachine31
import GoldbachTm.Tm31.Search0

theorem lemma_12_to_13 (i : ℕ) (r1: ℕ) (l r : List Γ)
(h :
nth_cfg i = some ⟨⟨12, by omega⟩, ⟨Γ.zero,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate r1 Γ.one ++ List.cons Γ.zero r)⟩⟩) :

∃ j, nth_cfg (j + i) = some ⟨⟨13, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate r1 Γ.one ++ List.cons Γ.zero l), Turing.ListBlank.mk r⟩⟩
:= by
forward h h i

cases r1 with
| zero => use 1
          simp [h]
| succ r1 => apply rec13 at h
             use (r1 + 2)
             have g : r1 + 2+i = 1 + i + r1 + 1 := by omega
             rw [g, h]

theorem lemma_8_to_9 (i : ℕ) (l1: ℕ) (l r : List Γ)
(h :
nth_cfg i = some ⟨⟨8, by omega⟩, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate l1 Γ.one ++ List.cons Γ.zero l),
  Turing.ListBlank.mk r,
  ⟩⟩) :

∃ j, nth_cfg (j + i) = some ⟨⟨9, by omega⟩, ⟨Γ.zero,
    Turing.ListBlank.mk l,
    Turing.ListBlank.mk (List.replicate (l1+1) Γ.one ++ r),
    ⟩⟩
:= by
forward h h i
cases l1 with
| zero => use 1
          simp [h]
| succ l1 => apply rec9 at h
             use (l1 + 2)
             have g : l1 + 2+i = 1+i +l1 + 1 := by omega
             simp [g, h]
             rw [List.append_cons, ← List.replicate_succ']

theorem lemma_11_to_12 (i : ℕ) (r1: ℕ) (l r : List Γ)
(h :
nth_cfg i = some ⟨⟨11, by omega⟩, ⟨Γ.one,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate r1 Γ.one ++ List.cons Γ.zero r),
  ⟩⟩) :
∃ j, nth_cfg (j + i) = some ⟨⟨12, by omega⟩, ⟨Γ.zero,
    Turing.ListBlank.mk (List.replicate r1 Γ.one ++ List.cons Γ.zero l),
    Turing.ListBlank.mk r,
    ⟩⟩
:= by
forward h h i
cases r1 with
| zero => use 1
          simp [h]
| succ r1 =>  simp! [*, -nth_cfg] at h
              apply rec12 at h
              use (r1+2)
              have g : r1 + 2+i = 1+i +r1 + 1 := by omega
              simp [g, h]

theorem lemma_17_to_20 (i : ℕ) (l1: ℕ) (l r : List Γ)
(h :
nth_cfg i = some ⟨⟨17, by omega⟩, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate l1 Γ.one ++ List.cons Γ.zero l),
  Turing.ListBlank.mk r,
  ⟩⟩) :
∃ j, nth_cfg (j + i) = some ⟨⟨20, by omega⟩, ⟨Γ.zero,
    Turing.ListBlank.mk l,
    Turing.ListBlank.mk (List.replicate (l1+1) Γ.one ++ r),
    ⟩⟩
:= by
forward h h i
cases l1 with simp! [*, -nth_cfg] at h
| zero => use 1
          simp [h]
| succ r1 =>  apply rec20 at h
              use (r1+2)
              have g : r1 + 2+i = 1+i +r1 + 1 := by omega
              simp [g, h, List.replicate_succ' (r1+1)]
