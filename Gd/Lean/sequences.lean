import Mathlib
import Mathlib.Algebra.Order.Field.Basic

import Mathlib.Data.Real.Basic

-- Simple lemma showing that if $a > 0$ and $b \leq c$ then $b*a \leq c*a$
theorem multiply_both_sides {a b c : Real} (ha : 0 < a) (hbc : b ≤ c) : b*a ≤ c*a := by
  exact (mul_le_mul_right ha).mpr hbc

-- Simple lemma showing that if
-- a_{k} ≤ D_{k} - D_{k+1} and a_{k+1} ≤ a_{k}
-- then a_{k} ≤ D_{0} / (k+1) for all k
theorem rate_from_monotonic_and_telescope_ub (a : Nat -> Real) (D : Nat → NNReal) :
(∀ k : Nat, (a k ≤ D k - D (k+1)) ∧ (a (k+1) ≤ a k)) ->
(∀ k : Nat , a k ≤ (D 0) / ↑(k+1)) := by
  intro h
  suffices h_hat : (∀ (k : Nat), D (k+1) ≤ D 0 - (a k)*(k+1))
  . intro k
    let ak := a k
    let D0 := D 0
    let r : NNReal := ↑(k+1)
    have hr : 0 < r := by simp
    have h1 : D (k+1) ≤ D 0 - (a k) * r := by simp [h_hat k]
    have h2 : (a k) * r + D (k+1) ≤ D 0 := by linarith
    have h3 : (a k) * r ≤  (a k) * r + D (k+1) := by simp
    have h4 : (a k) * r ≤ D 0 := by linarith
    have h5 : (a k) ≤ D 0 / r := ((@le_div_iff ℝ _ ak ↑D0 r) hr).mpr h4
    have h6 : (a k) ≤ (D 0) / ↑(k+1) := h5
    exact h6

  intro k
  apply Nat.recOn (motive := (fun x : Nat => D (x+1) ≤ D Nat.zero - (a x)*(x+1))) k
    (by
    have h_base : (Nat.zero + 1)*a Nat.zero ≤ D Nat.zero - D (Nat.zero+1) := by simp [(h Nat.zero).left]
    linarith
    )
    (fun (k : Nat) (ih : D (k+1) ≤ D 0 - (a k)*(k+1)) => by
      let r := ↑(k+1)
      have hpp : 0 < (r : NNReal) := by simp
      have h1 : a (Nat.succ k) ≤ a k := (h k).right
      have h1': - (a k) ≤ - (a (Nat.succ k)) := by linarith
      have h1'': - (a k)*↑(k+1) ≤ - (a (Nat.succ k))*↑(k+1) := multiply_both_sides hpp h1'
      have h2 : a (Nat.succ k) ≤ D (Nat.succ k) - D (Nat.succ k+1) := (h (Nat.succ k)).left
      have h3 : D (Nat.succ k+1) ≤ D (Nat.succ k) - (a (Nat.succ k)) := by linarith
      have h4 : D (Nat.succ k+1) ≤ D 0 - (a k)*(k+1) - (a (Nat.succ k)) := by linarith [h3, ih]
      have h4' : D (Nat.succ k+1) ≤ D 0 - (a k)*↑(k+1) - (a (Nat.succ k)) := by simp [h4]
      have h4 : D (Nat.succ k+1) ≤ D 0 - (a (Nat.succ k))*r - (a (Nat.succ k)) := by linarith [h1'']
      have h5 : D (Nat.succ k+1) ≤ D 0 - (a (Nat.succ k))*(Nat.succ k+1) := by linarith
      exact h5
    )
