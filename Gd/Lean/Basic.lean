import Mathlib

open Filter Metric Asymptotics


---------------------------------------------------------
-- Lemmatta to help with asymptotic proofs
---------------------------------------------------------


----- Little o preservation under reparamterization of the range.
------- Suppose that $φ : ℝ → ℝ$ is a function such that $φ = o(t)$ as $x → 0$.
--------- Suppose that $f(x) = o(1)$ as $x → 0$.
--------- Suppose that $f(x) = o(u)$ as $x → 0$.
------- Then φ∘f = o(u) as $x → 0$.
theorem IsLittleO_comp_left {α : Type u_1} {f : α → ℝ} {l : Filter α} {u : α → ℝ} {φ : ℝ → ℝ} (h_φ : φ=O[(nhds 0)] (fun x : ℝ => x)) (h_f_LittleO_1 : f=o[l] fun _x => (1 : ℝ)) :
  f =o[l] u → (fun y => φ (f y)) =o[l] u := by
  -- First prove that Filter.Tendsto f l (nhds 0)
  have h_f_filter : (Filter.Tendsto f l (nhds 0)) := by
    rw [isLittleO_one_iff] at h_f_LittleO_1
    exact h_f_LittleO_1
  -- Then apply Asymptotics.IsBigO.comp_tendsto
  have h_comp : (fun y => φ (f y)) =O[l] f := by
    exact IsBigO.comp_tendsto h_φ h_f_filter

  intro h_f_LittleO_u
  have h_comp' : (fun y => φ (f y)) =o[l] u := by
    exact IsBigO.trans_isLittleO h_comp h_f_LittleO_u

  exact h_comp'

-- Theorem shows that min{x, 0} is O(x).
theorem min_with_zero_is_BigO_id : (fun x : ℝ => min x 0) =O[(nhds 0)] (fun x : ℝ => x) := by
  rw [@IsBigO_def]
  use 1
  rw [@isBigOWith_iff]
  rw [@Metric.eventually_nhds_iff]
  use 1
  constructor
  . linarith -- prove 1 > 0
  . intro y hy
    cases (le_or_lt y 0) with
    | inl h_y_nonpos =>
      simp [h_y_nonpos]
    | inr h_y_pos =>
      have h_y_pos' : |y| = y := by exact abs_of_pos h_y_pos
      simp [h_y_pos']
      have h_min_pos : min y 0 = 0 := by exact min_eq_right_of_lt h_y_pos
      calc |min y 0|
        _ = 0 := by simp [h_min_pos]
        _ ≤ y := by linarith
