-- theorem of subroutine: judge prime

import GoldbachTm.Tm31.TuringMachine31
import GoldbachTm.Tm31.Transition
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.ModEq

-- c1++, c2++
--    l 0 [la 11] 0  [lb 11] 0 [ra 11111] 0  [(rb+1) 1] 0 r
--                c1         ^            c2
--
--    l 0 [la' 1] 0  [lb' 1] 0 [(ra+1) 1] 0  [rb 11111] 0 r
--                c1         ^            c2
private lemma step_12_pointer (i la lb ra rb: ℕ) (l r : List Γ) :
nth_cfg i = some ⟨⟨12, by omega⟩, ⟨Γ.zero,
  Turing.ListBlank.mk (List.replicate lb Γ.one ++ List.cons Γ.zero (List.replicate la Γ.one ++ List.cons Γ.zero l)),
  Turing.ListBlank.mk (List.replicate ra Γ.one ++ List.cons Γ.zero (List.replicate (rb+1) Γ.one ++ List.cons Γ.zero r))⟩⟩ →
  (ra + 2) ≡ (la + 1) [MOD (la + lb + 1)] →
∃ j la' lb', nth_cfg (i+j) = some ⟨⟨12, by omega⟩, ⟨Γ.zero,
  Turing.ListBlank.mk (List.replicate lb' Γ.one ++ List.cons Γ.zero (List.replicate la' Γ.one ++ List.cons Γ.zero l)),
  Turing.ListBlank.mk (List.replicate (ra+1) Γ.one ++ List.cons Γ.zero (List.replicate rb Γ.one ++ List.cons Γ.zero r))⟩⟩
  /\ (ra + 3) ≡ (la' + 1) [MOD (la + lb + 1)]
  /\ la + lb = la' + lb'
:= by
intros g hm

apply lemma_12_to_13 at g
obtain ⟨j, g⟩ := g
forward g g (j+i)
forward g g (1+j+i)
apply rec15 at g

forward g g (2+j+i+ra+1)

cases lb with simp_all
| zero => forward g g (4+j+i+ra)
          cases la with
          | zero => forward g g (5+j+i+ra)
                    forward g g (6+j+i+ra)
                    use! (j+ra+7), 0, 0
                    simp
                    constructor
                    . have h: i+(j+ra+7) = 7+j +i + ra := by omega
                      rw [h, g]
                      constructor
                    . apply Nat.modEq_one
          | succ la =>  simp! [*, -nth_cfg] at g
                        apply rec10 at g
                        forward g g (5+j+i+ra+la+1)
                        forward g g (7+j+i+ra+la)
                        rw [List.append_cons, ← List.replicate_succ'] at g
                        simp! [*, -nth_cfg] at g
                        apply rec12 at g
                        use! (9+j+ra+la+la), 0, (la+1)
                        simp
                        constructor
                        . have h : i + (9+j + ra + la + la) =8+ j + i + ra + la + la + 1 := by omega
                          rw [h, g]
                          constructor
                        . apply Nat.ModEq.add_right 1
                          apply Nat.ModEq.trans hm
                          rw [Nat.modEq_zero_iff_dvd]
| succ lb =>  simp! [*, -nth_cfg] at g
              apply lemma_8_to_9 at g
              obtain ⟨k, g⟩ := g
              forward g g (k+ (4+j+i+ra))
              apply lemma_11_to_12 at g
              obtain ⟨m, g⟩ := g
              use! (j+ra+k+m+5), (la+1), lb
              have h : i+(j+ra+k+m+5) =m + (5 + k + j + i + ra) := by omega
              rw [h, g]
              repeat any_goals constructor
              any_goals omega
              apply Nat.ModEq.add_right 1 hm

-- c1++, c2++
--    l 0 [la 11] 0  [lb 11] 0 [ra 11111111] 0  [rb 1] 0 r
--                c1         ^               c2
--
--    l 0 [la' 1] 0  [lb' 1] 0 [(ra+rb) 111] 0         0 r
--                c1         ^               c2
theorem lemma_12  (rb : ℕ): ∀ (i la lb ra : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨12, by omega⟩, ⟨Γ.zero,
  Turing.ListBlank.mk (List.replicate lb Γ.one ++ List.cons Γ.zero (List.replicate la Γ.one ++ List.cons Γ.zero l)),
  Turing.ListBlank.mk (List.replicate ra Γ.one ++ List.cons Γ.zero (List.replicate rb Γ.one ++ List.cons Γ.zero r))⟩⟩ →
  (ra + 2) ≡ (la + 1) [MOD (la + lb + 1)] →
∃ j la' lb', nth_cfg (i+j) = some ⟨⟨12, by omega⟩, ⟨Γ.zero,
  Turing.ListBlank.mk (List.replicate lb' Γ.one ++ List.cons Γ.zero (List.replicate la' Γ.one ++ List.cons Γ.zero l)),
  Turing.ListBlank.mk (List.replicate (ra+rb) Γ.one ++ List.cons Γ.zero (List.cons Γ.zero r))⟩⟩
  /\ (ra + rb + 2) ≡ (la' + 1) [MOD (la + lb + 1)]
  /\ la + lb = la' + lb'
:= by
induction rb with intros i la lb ra l r g hm
| zero => use! 0, la, lb
          simp [g, hm]
| succ rb =>  rename_i induction_step
              apply step_12_pointer at g
              specialize g hm
              obtain ⟨j, la', lb', g, h₁, h₂⟩ := g
              apply induction_step at g
              rw [← h₂] at g
              have h : ra + 1 + 2 = ra + 3 := by omega
              rw [h] at g
              specialize g h₁
              obtain ⟨k, la'', lb'', g, h₃, h₄⟩ := g
              use! (j+k), la'', lb''
              repeat any_goals constructor
              any_goals tauto
              . rw [← Nat.add_assoc i, g]
                apply congr <;> try rfl
                apply congr <;> try rfl
                apply congr <;> try rfl
                apply congr <;> try rfl
                apply congr <;> try rfl
                apply congr <;> try rfl
                apply congr <;> try rfl
                apply congr <;> try rfl
                omega
              . have h : ra + (rb + 1) +2 = ra + 1 + rb + 2:= by omega
                rw [h]
                assumption

--    l 0 1 0  [lb 11]    0  0  [(rb+1) 1] 0 r
--          c1            ^  c2
--
--    l 0 1 0  [(lb+1) 1] 0  0  [rb 11111] 0 r
--          c1            ^  c2
theorem step_12_n_dvd (i lb rb: ℕ) (l r : List Γ) :
nth_cfg i = some ⟨⟨12, by omega⟩, ⟨Γ.zero,
  Turing.ListBlank.mk (List.replicate lb Γ.one ++ Γ.zero :: Γ.one :: Γ.zero :: l),
  Turing.ListBlank.mk (List.cons Γ.zero (List.replicate (rb+1) Γ.one ++ List.cons Γ.zero r))⟩⟩ →
  ¬ (lb + 2) ∣ (rb + 3) →
∃ j, nth_cfg (i+j) = some ⟨⟨12, by omega⟩, ⟨Γ.zero,
  Turing.ListBlank.mk (List.replicate (lb+1) Γ.one ++ Γ.zero :: Γ.one :: Γ.zero :: l),
  Turing.ListBlank.mk (List.cons Γ.zero (List.replicate rb Γ.one ++ List.cons Γ.zero r))⟩⟩
:= by
intros g ne_dvd
have h := lemma_12 (rb+1) i 1 lb 0 l r
simp at h
specialize h g rfl
clear g
obtain ⟨j, la', lb', g, h₁, h₂⟩ := h
apply lemma_12_to_13 at g
obtain ⟨k, g⟩ := g
forward g g (k+(i+j))
forward g g (1+k+i+j)
rw [← List.cons_append, ← List.replicate.eq_2] at g
apply rec16 at g
forward g g (2 + k + i + j + rb.succ + 1)
cases lb' with (simp! [*, -nth_cfg] at g; simp_all)
| zero => subst la'
          exfalso
          apply ne_dvd
          rw [← Nat.modEq_zero_iff_dvd]
          ring_nf at *
          apply Nat.ModEq.trans h₁
          rw [Nat.modEq_zero_iff_dvd]
| succ lb' => apply lemma_17_to_20 at g
              obtain ⟨m, g⟩ := g
              forward g g (m + (5 + k + i + j + rb))
              apply rec21 at g
              forward g g (6 + m + k + i + j + rb + lb' + 1)
              forward g g (8 + m + k + i + j + rb + lb')
              forward g g (9 + m + k + i + j + rb + lb')
              forward g g (10 + m + k + i + j + rb + lb')
              rw [← List.cons_append] at g
              rw [← List.replicate.eq_2] at g
              rw [ List.append_cons ] at g
              rw [← List.replicate_succ'] at g
              rw [← List.append_assoc] at g
              rw [← List.replicate_add] at g
              apply rec5 at g
              forward g g (11 + m + k + i + j + rb + lb' + (lb'.succ + 1 + la') + 1)
              forward g g (15 + m + k + i + j + rb + lb' * 2 + la')
              rw [List.replicate_add] at g
              rw [List.replicate_add] at g
              simp! [*, -nth_cfg] at g
              apply rec7 at g
              have h : 2+lb'+la'-1=1+lb'+la' := by omega
              rw [h] at g
              forward g g (16 + m + k + i + j + rb + lb' * 2 + la'+ (1 + lb' + la') + 1)
              forward g g (19 + m + k + i + j + rb + lb' * 3 + la'*2)
              rw [List.replicate_add] at g
              rw [List.replicate_add] at g
              simp! [*, -nth_cfg] at g
              apply rec9 at g
              forward g g (20 + m + k + i + j + rb + lb' * 3 + la' * 2 + (1 + lb' + la' - 1) + 1)
              rw [ List.append_cons ] at g
              rw [← List.replicate_succ'] at g
              apply lemma_11_to_12 at g
              obtain ⟨n, g⟩ := g
              use (n + (22 + m + k + j + rb + lb' * 3 + la' * 2 + (1 + lb' + la' - 1)))
              ring_nf at *
              rw [g]
              any_goals apply congr
              any_goals rfl
              any_goals apply congr
              any_goals rfl
              any_goals apply congr
              any_goals rfl
              any_goals apply congr
              any_goals rfl
              any_goals apply congr
              any_goals rfl
              any_goals apply congr
              any_goals rfl
              any_goals apply congr
              any_goals rfl
              any_goals apply congr
              any_goals rfl
              any_goals apply congr
              any_goals rfl
              omega

--    l 0 1 0  [lb 11]    0  0  [rb 1] 0 r
--          c1            ^  c2
--                        12
--
--    l 0 1 1  [lb 11]    1  1  [rb 1] 0 r
--      ^
--      18
theorem step_12_dvd (i lb rb: ℕ) (l r : List Γ) :
nth_cfg i = some ⟨⟨12, by omega⟩, ⟨Γ.zero,
  Turing.ListBlank.mk (List.replicate lb Γ.one ++ Γ.zero :: Γ.one :: Γ.zero :: l),
  Turing.ListBlank.mk (List.cons Γ.zero (List.replicate rb Γ.one ++ List.cons Γ.zero r))⟩⟩ →
  (lb + 2) ∣ (rb + 2) →
∃ j, nth_cfg (i+j) = some ⟨⟨18, by omega⟩, ⟨Γ.zero,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate (lb+rb+4) Γ.one ++ List.cons Γ.zero r)⟩⟩
:= by
intros g dvd
have h := lemma_12 rb i 1 lb 0 l r
simp at h
specialize h g rfl
clear g
obtain ⟨j, la', lb', g, h₁, h₂⟩ := h
apply lemma_12_to_13 at g
obtain ⟨k, g⟩ := g
forward g g (k+(i+j))
forward g g (1+k+i+j)
rw [← List.cons_append] at g
apply rec16 at g
forward g g (2 + k + i + j + rb + 1)
cases lb' with (simp! [*, -nth_cfg] at g; simp_all)
| zero => subst la'
          forward g g (4+k+i+j+rb)
          forward g g (5+k+i+j+rb)
          apply rec18 at g
          use (8 + k + j + rb + lb)
          ring_nf at *
          simp [g]
          rw [List.append_cons, ← List.replicate_succ']
          rw [List.append_cons, ← List.replicate_succ']
          rw [← List.append_assoc, ← List.replicate_add]
          ring_nf
| succ lb' => have : lb = la'+ lb' := by omega
              subst lb
              clear h₂
              ring_nf at *
              rw [Nat.ModEq.comm] at h₁
              rw [← Nat.modEq_zero_iff_dvd] at dvd
              have h := Nat.ModEq.trans h₁ dvd
              rw [Nat.modEq_zero_iff_dvd] at h
              apply Nat.le_of_dvd at h <;> omega

--    l 0 1 0  [lb 11]     0  0  [rb 1] 0 r
--          c1             ^  c2
--
--    l 0 1 0  [(lb+rb) 1] 0  0         0 r
--          c1             ^  c2
theorem leap_12_prime (rb : ℕ) : ∀ (i lb: ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨12, by omega⟩, ⟨Γ.zero,
  Turing.ListBlank.mk (List.replicate lb Γ.one ++ Γ.zero :: Γ.one :: Γ.zero :: l),
  Turing.ListBlank.mk (List.cons Γ.zero (List.replicate rb Γ.one ++ List.cons Γ.zero r))⟩⟩ →
Nat.Prime (lb+rb+4) →
∃ j, nth_cfg (i+j) = some ⟨⟨12, by omega⟩, ⟨Γ.zero,
  Turing.ListBlank.mk (List.replicate (lb+rb) Γ.one ++ Γ.zero :: Γ.one :: Γ.zero :: l),
  Turing.ListBlank.mk (Γ.zero :: Γ.zero :: r)⟩⟩
:= by
induction rb with intros i lb l r g p
| zero => use 0
          simp! [g]
| succ rb => apply step_12_n_dvd at g
             by_cases (lb + 2 ∣ rb + 3) <;> rename_i h
             . have g : (lb + 2 ∣ lb + 2) := Nat.dvd_refl _
               have g := Nat.dvd_add g h
               ring_nf at p g
               rw [Nat.Prime.dvd_iff_eq] at g
               any_goals omega
               all_goals assumption
             . specialize g h
               rename_i induction_step
               obtain ⟨j, g⟩ := g
               apply induction_step at g
               ring_nf at g p
               specialize g p
               obtain ⟨k, g⟩ := g
               use (j+k)
               ring_nf at *
               rw [g]

-- r1 : count of 1 on the right
theorem lemma_23 (i r1: ℕ) (l r : List Γ)
(g :
nth_cfg i = some ⟨⟨0, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (Γ.zero :: l), Turing.ListBlank.mk (List.replicate r1 Γ.one ++ List.cons Γ.zero r)⟩⟩)
(p : Nat.Prime (r1+1)) :
∃ j, nth_cfg (i+j) = some ⟨⟨22, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (r1+1) Γ.one ++ List.cons Γ.zero r)⟩⟩ :=
match h : r1 with
| Nat.zero => by subst r1
                 exfalso
                 apply Nat.not_prime_one p
| Nat.succ Nat.zero => by
  subst r1
  forward g g i
  forward g g (1+i)
  forward g g (2+i)
  forward g g (3+i)
  forward g g (4+i)
  use 5
  ring_nf at *
  simp [g]
| Nat.succ (Nat.succ Nat.zero) => by
  subst r1
  forward g g i
  forward g g (1+i)
  forward g g (2+i)
  forward g g (3+i)
  forward g g (4+i)
  forward g g (5+i)
  forward g g (6+i)
  use 7
  ring_nf at *
  simp [g]
| Nat.succ (Nat.succ (Nat.succ r1)) => by
  clear h
  forward g g i
  forward g g (1+i)
  forward g g (2+i)
  forward g g (3+i)
  forward g g (4+i)
  forward g g (5+i)
  forward g g (6+i)
  forward g g (7+i)
  forward g g (8+i)
  forward g g (9+i)
  forward g g (10+i)
  forward g g (11+i)
  forward g g (12+i)
  forward g g (13+i)
  apply (leap_12_prime _ _ 0) at g
  simp! at p
  ring_nf at g p
  specialize g p
  obtain ⟨j, g⟩ := g
  forward g g (14+i+j)
  forward g g (15+i+j)
  forward g g (16+i+j)
  forward g g (17+i+j)
  cases r1 with
  | zero => exfalso
            have g : ¬ Nat.Prime 4 := by decide
            apply g p
  | succ r1 => forward g g (18+i+j)
               apply lemma_17_to_20 at g
               obtain ⟨k, g⟩ := g
               forward g g (k+(19+i+j))
               apply rec21 at g
               forward g g (20 + k + i + j + r1 + 1)
               forward g g (22 + k + i + j + r1)
               forward g g (23 + k + i + j + r1)
               rw [List.append_cons, ← List.replicate_succ'] at g
               rw [List.append_cons, ← List.replicate_succ'] at g
               rw [← List.cons_append] at g
               rw [← List.replicate_succ] at g
               rw [← List.cons_append] at g
               rw [← List.replicate_succ] at g
               apply rec22 at g
               use (24 + k + j + r1 + (r1 + 1 + 1 + 1 + 1) + 1)
               ring_nf at *
               simp [g]
               ring_nf

--    l 0 1 0  [lb 11]    0  0  [rb 1] 0 r
--          c1            ^  c2
--                        12
--
--    l 0 1 1  [lb 11]    1  1  [rb 1] 0 r
--      ^
--      18
theorem leap_12_dvd  (rb : ℕ) : ∀ (i lb: ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨12, by omega⟩, ⟨Γ.zero,
  Turing.ListBlank.mk (List.replicate lb Γ.one ++ Γ.zero :: Γ.one :: Γ.zero :: l),
  Turing.ListBlank.mk (List.cons Γ.zero (List.replicate rb Γ.one ++ List.cons Γ.zero r))⟩⟩ →
(∃ divisor, divisor ≥ (lb+2) /\ divisor < lb + rb + 4 /\ divisor ∣ (lb + rb + 4)) →
∃ j, nth_cfg (i+j) = some ⟨⟨18, by omega⟩, ⟨Γ.zero,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate (lb+rb+4) Γ.one ++ List.cons Γ.zero r)⟩⟩
:= by
induction rb with intros i lb l r g hd
| zero => by_cases (lb+2) ∣ 2 <;> rename_i h
          . apply step_12_dvd at g
            apply g h
          . obtain ⟨divisor, _, _, h₃⟩ := hd
            have g : divisor = lb + 2 \/ divisor = lb + 3 := by omega
            have h₁ : divisor ∣ divisor := Nat.dvd_refl _
            ring_nf at *
            cases g <;> subst divisor
            . have g := Nat.dvd_sub (by omega) h₃ h₁
              have h₁ : lb+0+4-(lb+2) = 2 := by omega
              rw [h₁] at g
              specialize h g
              tauto
            . have g := Nat.dvd_sub (by omega) h₃ h₁
              have h : lb+0+4-(lb+3) = 1 := by omega
              rw [h] at g
              apply Nat.eq_one_of_dvd_one at g
              omega
| succ rb =>  by_cases h : (lb+2) ∣ rb+3
              . apply step_12_dvd at g
                apply g h
              . apply step_12_n_dvd at g
                specialize g h
                obtain ⟨j, g⟩ := g
                rename_i induction_step
                apply induction_step at g
                have h : (∃ divisor ≥ lb + 1 + 2, divisor < lb + 1 + rb + 4 ∧ divisor ∣ lb + 1 + rb + 4) := by
                  obtain ⟨divisor, h₁, h₂, h₃⟩ := hd
                  use divisor
                  ring_nf at *
                  repeat any_goals apply And.intro
                  any_goals omega
                  by_cases h : divisor = 2+lb
                  . subst divisor
                    exfalso
                    apply h
                    have h := Nat.dvd_sub (by omega) h₃ (Nat.dvd_refl _)
                    have g : (5 + lb + rb - (2+lb)) = 3 + rb := by omega
                    rw [g] at h
                    assumption
                  . omega
                specialize g h
                obtain ⟨k, g⟩ := g
                use (j+k)
                ring_nf at *
                simp [g]
