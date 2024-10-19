import GoldbachTm.Tm27.TuringMachine27
import GoldbachTm.Tm27.Transition
import GoldbachTm.Tm27.Miscellaneous

namespace Tm27

-- c1++, c2++
--    l 0 [la 11] 0  [lb 11] 0 [ra 11111] 0  [(rb+1) 1] 0 r
--                c1         ^            c2
--
--    l 0 [la' 1] 0  [lb' 1] 0 [(ra+1) 1] 0  [rb 11111] 0 r
--                c1         ^            c2
private lemma step_10_pointer (i la lb ra rb: ℕ) (l r : List Γ) :
nth_cfg i = some ⟨⟨10, by omega⟩, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate lb Γ.one ++ List.cons Γ.zero (List.replicate la Γ.one ++ List.cons Γ.zero l)),
  Turing.ListBlank.mk (List.replicate ra Γ.one ++ List.cons Γ.zero (List.replicate (rb+1) Γ.one ++ List.cons Γ.zero r))⟩⟩ →
  (ra + 2) ≡ (la + 1) [MOD (la + lb + 1)] →
∃ j>i, ∃ la' lb', nth_cfg j = some ⟨⟨10, by omega⟩, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate lb' Γ.one ++ List.cons Γ.zero (List.replicate la' Γ.one ++ List.cons Γ.zero l)),
  Turing.ListBlank.mk (List.replicate (ra+1) Γ.one ++ List.cons Γ.zero (List.replicate rb Γ.one ++ List.cons Γ.zero r))⟩⟩
  /\ (ra + 3) ≡ (la' + 1) [MOD (la + lb + 1)]
  /\ la + lb = la' + lb'
:= by
intros g hm
apply lemma_10_to_11 at g
obtain ⟨j, g⟩ := g
forward g
forward g
apply rec13 at g
forward g
cases lb with simp_all
| zero => forward g
          cases la with simp_all
          | zero => forward g
                    forward g
                    use (7+j+i+ra)
                    constructor
                    . omega
                    . simp [g]
                      use! 0, 0
                      simp!
                      apply Nat.modEq_one
          | succ la => simp! at g
                       apply lemma8 at g
                       forward g
                       rw [List.append_cons] at g
                       rw [← List.replicate_succ'] at g
                       simp! at g
                       apply lemma10 at g
                       use (8+j+i+ra+la+la+1)
                       constructor
                       . omega
                       . use! 0, (la+1)
                         rw [g]
                         simp!
                         apply Nat.ModEq.add_right 1
                         apply Nat.ModEq.trans hm
                         rw [Nat.modEq_zero_iff_dvd]
| succ lb =>  simp! at g
              apply lemma_6_to_7 at g
              obtain ⟨k, _,  g⟩ := g
              forward g
              apply lemma_9_to_10 at g
              obtain ⟨n, _,  g⟩ := g
              use n
              constructor
              . omega
              . use! (la+1), lb
                simp! [g]
                constructor
                . apply Nat.ModEq.add_right 1 hm
                . omega

-- c1++, c2++
--    l 0 [la 11] 0  [lb 11] 0 [ra 11111111] 0  [rb 1] 0 r
--                c1         ^               c2
--
--    l 0 [la' 1] 0  [lb' 1] 0 [(ra+rb) 111] 0         0 r
--                c1         ^               c2
theorem end_10  (rb : ℕ): ∀ (i la lb ra : ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨10, by omega⟩, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate lb Γ.one ++ List.cons Γ.zero (List.replicate la Γ.one ++ List.cons Γ.zero l)),
  Turing.ListBlank.mk (List.replicate ra Γ.one ++ List.cons Γ.zero (List.replicate rb Γ.one ++ List.cons Γ.zero r))⟩⟩ →
  (ra + 2) ≡ (la + 1) [MOD (la + lb + 1)] →
∃ j≥i, ∃ la' lb', nth_cfg j = some ⟨⟨10, by omega⟩, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate lb' Γ.one ++ List.cons Γ.zero (List.replicate la' Γ.one ++ List.cons Γ.zero l)),
  Turing.ListBlank.mk (List.replicate (ra+rb) Γ.one ++ List.cons Γ.zero (List.cons Γ.zero r))⟩⟩
  /\ (ra + rb + 2) ≡ (la' + 1) [MOD (la + lb + 1)]
  /\ la + lb = la' + lb'
:= by
induction rb with intros i la lb ra l r g hm
| zero => use! i
          constructor
          . omega
          . use! la, lb
            simp [g, hm]
| succ rb =>  rename_i induction_step
              apply step_10_pointer at g
              specialize g hm
              obtain ⟨j, _, la', lb', g, h₁, h₂⟩ := g
              apply induction_step at g
              rw [← h₂] at g
              ring_nf at *
              specialize g h₁
              obtain ⟨k, _, la'', lb'', g, h₃, h₄⟩ := g
              use! k
              constructor
              . omega
              . use! la'', lb''
                ring_nf at *
                repeat any_goals constructor
                all_goals tauto


--    l 0 1 0  [lb 11]    0  0  [(rb+1) 1] 0 r
--          c1            ^  c2
--
--    l 0 1 0  [(lb+1) 1] 0  0  [rb 11111] 0 r
--          c1            ^  c2
theorem step_10_n_dvd (i lb rb: ℕ) (l r : List Γ) :
nth_cfg i = some ⟨⟨10, by omega⟩, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate lb Γ.one ++ Γ.zero :: Γ.one :: Γ.zero :: l),
  Turing.ListBlank.mk (List.cons Γ.zero (List.replicate (rb+1) Γ.one ++ List.cons Γ.zero r))⟩⟩ →
  ¬ (lb + 2) ∣ (rb + 3) →
∃ j>i, nth_cfg j = some ⟨⟨10, by omega⟩, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate (lb+1) Γ.one ++ Γ.zero :: Γ.one :: Γ.zero :: l),
  Turing.ListBlank.mk (List.cons Γ.zero (List.replicate rb Γ.one ++ List.cons Γ.zero r))⟩⟩
:= by
intros g ne_dvd
have h := end_10 (rb+1) i 1 lb 0 l r
simp at h
specialize h g rfl
clear g
obtain ⟨j, _, la', lb', g, h₁, h₂⟩ := h
apply lemma_10_to_11 at g
obtain ⟨k, g⟩ := g
forward g
forward g
rw [← List.cons_append, ← List.replicate.eq_2] at g
apply rec14 at g
forward g
cases lb' with (simp! [*, -nth_cfg] at g; simp_all)
| zero => subst la'
          exfalso
          apply ne_dvd
          rw [← Nat.modEq_zero_iff_dvd]
          ring_nf at *
          apply Nat.ModEq.trans h₁
          rw [Nat.modEq_zero_iff_dvd]
| succ lb' => apply lemma_15_to_19 at g
              obtain ⟨m, g⟩ := g
              forward g
              apply rec20 at g
              forward g
              forward g
              forward g
              forward g
              rw [← List.cons_append] at g
              rw [← List.replicate.eq_2] at g
              rw [ List.append_cons ] at g
              rw [← List.replicate_succ'] at g
              rw [← List.append_assoc] at g
              rw [← List.replicate_add] at g
              apply lemma5 at g
              forward g
              rw [List.replicate_add] at g
              rw [List.replicate_add] at g
              simp! [*, -nth_cfg] at g
              forward g
              rw [List.replicate_add] at g
              rw [List.replicate_add] at g
              simp! [*, -nth_cfg] at g
              apply lemma10 at g
              use (17 + m + k + j + rb + lb' * 2 + la' + (1 + lb' + la' - 1) + 1)
              constructor
              . omega
              . rw [g]
                simp!
                repeat any_goals first | omega | rfl | apply congr

--    l 0 1 0  [lb 11]    0  0  [rb 1] 0 r
--          c1            ^  c2
--                        10
--
--    l 0 1 1  [lb 11]    1  1  [rb 1] 0 r
--      ^
--      17
theorem step_10_dvd (i lb rb: ℕ) (l r : List Γ) :
nth_cfg i = some ⟨⟨10, by omega⟩, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate lb Γ.one ++ Γ.zero :: Γ.one :: Γ.zero :: l),
  Turing.ListBlank.mk (List.cons Γ.zero (List.replicate rb Γ.one ++ List.cons Γ.zero r))⟩⟩ →
  (lb + 2) ∣ (rb + 2) →
∃ j>i, nth_cfg j = some ⟨⟨17, by omega⟩, ⟨Γ.zero,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate (lb+rb+4) Γ.one ++ List.cons Γ.zero r)⟩⟩
:= by
intros g dvd
have h := end_10 rb i 1 lb 0 l r
simp at h
specialize h g rfl
clear g
obtain ⟨j, _, la', lb', g, h₁, h₂⟩ := h
apply lemma_10_to_11 at g
obtain ⟨k, g⟩ := g
forward g
forward g
apply rec14 at g
forward g
rw [← List.cons_append] at g
cases lb' with (simp! [*, -nth_cfg] at g; simp_all)
| zero => subst la'
          forward g
          forward g
          apply rec17 at g
          use (6 + k + j + rb + (1+lb)+1)
          constructor
          . omega
          . simp [g]
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
theorem leap_10_prime (rb : ℕ) : ∀ (i lb: ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨10, by omega⟩, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate lb Γ.one ++ Γ.zero :: Γ.one :: Γ.zero :: l),
  Turing.ListBlank.mk (List.cons Γ.zero (List.replicate rb Γ.one ++ List.cons Γ.zero r))⟩⟩ →
Nat.Prime (lb+rb+4) →
∃ j≥i, nth_cfg j = some ⟨⟨10, by omega⟩, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate (lb+rb) Γ.one ++ Γ.zero :: Γ.one :: Γ.zero :: l),
  Turing.ListBlank.mk (Γ.zero :: Γ.zero :: r)⟩⟩
:= by
induction rb with intros i lb l r g p
| zero => use i
          constructor
          . omega
          . simp! [g]
| succ rb => apply step_10_n_dvd at g
             by_cases h : (lb + 2 ∣ rb + 3)
             . have g : (lb + 2 ∣ lb + 2) := Nat.dvd_refl _
               have g := Nat.dvd_add g h
               ring_nf at p g
               rw [Nat.Prime.dvd_iff_eq] at g
               any_goals omega
               all_goals assumption
             . specialize g h
               rename_i induction_step
               obtain ⟨j, _, g⟩ := g
               apply induction_step at g
               ring_nf at g p
               specialize g p
               obtain ⟨k, _, g⟩ := g
               use k
               constructor
               . omega
               . simp! [g]
                 rw [← List.cons_append]
                 rw [← List.replicate_succ]
                 ring_nf

theorem prime_21 (i r1: ℕ) (l r : List Γ)
(g :
nth_cfg i = some ⟨⟨0, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (Γ.zero :: l), Turing.ListBlank.mk (List.replicate r1 Γ.one ++ List.cons Γ.zero r)⟩⟩)
(p : Nat.Prime (r1+1)) :
∃ j>i, nth_cfg j = some ⟨⟨21, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (r1+1) Γ.one ++ List.cons Γ.zero r)⟩⟩ :=
match h : r1 with
| Nat.zero => by subst r1
                 exfalso
                 apply Nat.not_prime_one p
| Nat.succ Nat.zero => by
  subst r1
  forward g
  forward g
  forward g
  forward g
  forward g
  use (5+i)
  simp [g]
| Nat.succ (Nat.succ Nat.zero) => by
  subst r1
  forward g
  forward g
  forward g
  forward g
  forward g
  forward g
  forward g
  use (7+i)
  simp [g]
| Nat.succ (Nat.succ (Nat.succ r1)) => by
  clear h
  forward g
  forward g
  forward g
  forward g
  forward g
  forward g
  forward g
  forward g
  forward g
  forward g
  apply (leap_10_prime _ _ 0) at g
  have h : r1.succ.succ.succ + 1 = 0 + r1 +4 := by omega
  rw [h] at p
  specialize g p
  obtain ⟨j, _, g⟩ := g
  forward g
  forward g
  forward g
  forward g
  forward g
  cases r1 with
  | zero => exfalso
            have g : ¬ Nat.Prime 4 := by decide
            apply g p
  | succ r1 => apply lemma_15_to_19 at g
               obtain ⟨k, g⟩ := g
               forward g
               apply rec20 at g
               forward g
               forward g
               forward g
               forward g
               rw [List.append_cons, ← List.replicate_succ'] at g
               rw [List.append_cons, ← List.replicate_succ'] at g
               rw [← List.cons_append] at g
               rw [← List.replicate_succ] at g
               apply rec21 at g
               use (11 + k + j + r1 + (r1 + 1 + 1 + 1) + 1)
               constructor
               . omega
               . rw [g]
                 simp
                 rw [List.append_cons, ← List.replicate_succ']


--    l 0 1 0  [lb 11]    0  0  [rb 1] 0 r
--          c1            ^  c2
--                        10
--
--    l 0 1 1  [lb 11]    1  1  [rb 1] 0 r
--      ^
--      17
theorem leap_10_dvd  (rb : ℕ) : ∀ (i lb: ℕ) (l r : List Γ),
nth_cfg i = some ⟨⟨10, by omega⟩, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate lb Γ.one ++ Γ.zero :: Γ.one :: Γ.zero :: l),
  Turing.ListBlank.mk (List.cons Γ.zero (List.replicate rb Γ.one ++ List.cons Γ.zero r))⟩⟩ →
(∃ divisor, divisor ≥ (lb+2) /\ divisor < lb + rb + 4 /\ divisor ∣ (lb + rb + 4)) →
∃ j>i, nth_cfg j = some ⟨⟨17, by omega⟩, ⟨Γ.zero,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate (lb+rb+4) Γ.one ++ List.cons Γ.zero r)⟩⟩
:= by
induction rb with intros i lb l r g hd
| zero => by_cases h : (lb+2) ∣ 2
          . apply step_10_dvd at g
            ring_nf at *
            apply g h
          . obtain ⟨divisor, _, _, h₃⟩ := hd
            have g : divisor = lb + 2 \/ divisor = lb + 3 := by omega
            have h₁ : divisor ∣ divisor := Nat.dvd_refl _
            ring_nf at *
            cases g <;> subst divisor
            . have g := Nat.dvd_sub (by omega) h₃ h₁
              have h₁ : 4+lb-(2+lb) = 2 := by omega
              rw [h₁] at g
              specialize h g
              tauto
            . have g := Nat.dvd_sub (by omega) h₃ h₁
              have h : 4+lb-(3+lb) = 1 := by omega
              rw [h] at g
              apply Nat.eq_one_of_dvd_one at g
              omega
| succ rb =>  by_cases h : (lb+2) ∣ rb+3
              . apply step_10_dvd at g
                apply g h
              . apply step_10_n_dvd at g
                specialize g h
                rename_i induction_step
                obtain ⟨j, _, g⟩ := g
                apply induction_step at g
                refine (?_ ∘ g) ?_
                . intros g
                  obtain ⟨k, _, g⟩ := g
                  use k
                  constructor
                  . omega
                  . simp [g]
                    ring_nf
                . obtain ⟨divisor, h₁, h₂, h₃⟩ := hd
                  use divisor
                  ring_nf at *
                  repeat any_goals apply And.intro
                  any_goals omega
                  by_cases h : divisor = 2 + lb
                  . subst divisor
                    exfalso
                    apply h
                    have h := Nat.dvd_sub (by omega) h₃ (Nat.dvd_refl _)
                    have g : (5 + lb + rb - (2+lb)) = 3 + rb := by omega
                    rw [g] at h
                    assumption
                  . omega

theorem n_prime_17 (i r1: ℕ) (l r : List Γ)
(g :
nth_cfg i = some ⟨⟨0, by omega⟩, ⟨Γ.one, Turing.ListBlank.mk (Γ.zero :: l), Turing.ListBlank.mk (List.replicate r1 Γ.one ++ List.cons Γ.zero r)⟩⟩)
(hp : ¬ Nat.Prime (r1+1)) :
∃ j>i, nth_cfg j = some ⟨⟨17, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk l, Turing.ListBlank.mk (List.replicate (r1+1) Γ.one ++ List.cons Γ.zero r)⟩⟩ :=
match r1 with
| Nat.zero => by simp_all
                 forward g
                 forward g
                 forward g
                 use (3+i)
                 rw [← g]
                 simp
| Nat.succ Nat.zero => by exfalso
                          apply hp
                          decide
| Nat.succ (Nat.succ Nat.zero) => by exfalso
                                     apply hp
                                     decide
| Nat.succ (Nat.succ (Nat.succ r1)) => by
  forward g
  forward g
  forward g
  forward g
  forward g
  forward g
  forward g
  forward g
  forward g
  forward g
  apply (leap_10_dvd _ _ 0) at g
  refine (?_ ∘ g) ?_
  . intros h
    obtain ⟨j, _, h⟩ := h
    use j
    constructor
    . omega
    . simp [h]
  . rw [Nat.not_prime_iff_exists_dvd_lt] at hp <;> try omega
    obtain ⟨p, h, g, hp⟩ := hp
    use p
    repeat any_goals apply And.intro
    any_goals omega
    have g : r1.succ.succ.succ +1 = 0+r1+4 := by omega
    rw [g] at h
    exact h

end Tm27
