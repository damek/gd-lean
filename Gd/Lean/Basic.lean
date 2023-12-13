import Mathlib

open Filter Metric Asymptotics Gradient InnerProductSpace


---------------------------------------------------------
-- Lemmatta to help with asymptotic proofs
---------------------------------------------------------

------------------------------------------------------------------------------
----- Little o preservation under reparamterization of the range.
------- Suppose that $φ : ℝ → ℝ$ is a function such that $φ = o(t)$ as $x → 0$.
--------- Suppose that $f(x) = o(1)$ as $x → 0$.
--------- Suppose that $f(x) = o(u)$ as $x → 0$.
------- Then φ∘f = o(u) as $x → 0$.
------------------------------------------------------------------------------
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

---------------------------------------------------------
-- Facts about inner products and norms
---------------------------------------------------------

theorem ExpansionOfScaledNormSquared
{F : Type u_2}
[NormedAddCommGroup F]
[InnerProductSpace ℝ F]
[CompleteSpace F] :
 ∀ L : ℝ, ∀ a b : F, ∀ L : ℝ, ∀ a b : F, L*‖a‖^2 - L*‖b‖^2 - 2*inner (L • b) (a - b) = L*‖a - b‖^2  := by

  have h_norm_identity : ∀ a b : F, ‖a‖^2 - ‖b‖^2 - 2 * inner b (a - b) = ‖a - b‖^2 := by
    intro a b
    calc ‖a‖^2 - ‖b‖^2 - 2 * inner b (a - b)
      _ = ‖a‖^2 - ‖b‖^2 - 2 * (inner b a - inner b b) := by simp [inner_sub_left]; rw [@inner_sub_right]
      _ = ‖a‖^2 - ‖b‖^2 - 2 * inner b a + 2 * inner b b := by ring
      _ = ‖a‖^2 - ‖b‖^2 - 2 * inner b a + 2 * ‖b‖^2 := by rw [@add_left_cancel_iff]; rw [@real_inner_self_eq_norm_sq]
      _ = ‖a‖^2 - 2 * inner b a + ‖b‖^2 := by ring
      _  = ‖a - b‖^2 := by simp [norm_sub_sq_real]; rw [@real_inner_comm]

  replace h_norm_identity : ∀ L : ℝ, ∀ a b : F, L*‖a‖^2 - L*‖b‖^2 - L*2*inner (b) (a - b) = L*‖a - b‖^2 := by
    intro L a b
    have _ : ‖a‖^2 - ‖b‖^2 - 2 * inner b (a - b) = ‖a - b‖^2 := by exact h_norm_identity a b
    rw [← h_norm_identity a b]
    ring

  replace h_norm_identity : ∀ L : ℝ, ∀ a b : F, L*‖a‖^2 - L*‖b‖^2 - 2*inner (L • b) (a - b) = L*‖a - b‖^2 := by
    intro L a b
    have _ : L*‖a‖^2 - L*‖b‖^2 - L*2*inner (b) (a - b) = L*‖a - b‖^2 := by exact h_norm_identity L a b
    rw [← h_norm_identity L a b]
    field_simp
    rw [@real_inner_smul_left]
    linarith

  simp [h_norm_identity]


---------------------------------------------------------
-- Gradient of the norm squared
---------------------------------------------------------
theorem GradientOfNormSquaredWithin
{F : Type u_2}
[NormedAddCommGroup F]
[InnerProductSpace ℝ F]
[CompleteSpace F]
(s : Set F) :
(∀ L : ℝ, ∀ x ∈ s, ∀ y ∈ s, HasGradientWithinAt (fun z => (L/2)*norm (z - x)^2) (L•(y-x)) s y) := by

  intro L x _ y _
  rw [@hasGradientWithinAt_iff_tendsto]
  -- metric reformulation
  rw [@Metric.tendsto_nhdsWithin_nhds]

  intro ε h_ε_pos
  let δ := ε / (max |L| 1)
  use δ
  constructor
  . simp [δ, h_ε_pos]; rw [@div_pos_iff];
    constructor
    constructor
    . exact h_ε_pos
    . rw [@lt_max_iff]
      simp
  . intro x' _ h_x'_δ
    rw [@dist_eq_norm] at h_x'_δ
    field_simp
    have h_norm :
      L*‖x' - x‖ ^ 2 - L*‖y - x‖ ^ 2 - 2* inner (L • (y - x)) (x' - y)
        = L*‖x' - y‖^2 := by
      have h_ap : L*‖x' - x‖ ^ 2 - L*‖y - x‖ ^ 2 - 2 * inner (L • (y - x)) (x' - x - (y - x))
        = L*‖x' - x - (y - x)‖^2 := by apply ExpansionOfScaledNormSquared L (x' - x) (y - x)
      simp at h_ap
      exact h_ap

    --- if  ‖x' - y‖ = 0, then we are done
    cases (eq_or_ne (‖x' - y‖) 0) with
    | inl h_norm_zero =>
      rw [h_norm_zero]
      simp [h_ε_pos]
    | inr h_norm_pos =>
      replace h_norm_pos : 0 < ‖x' - y‖ := by simp_all only [gt_iff_lt, ge_iff_le, ne_eq, norm_eq_zero,
                                                    norm_pos_iff, not_false_eq_true]
      replace h_norm_pos : 0 < (max |L| 1)*‖x' - y‖ := by
        rw [propext (zero_lt_mul_right h_norm_pos)]
        rw [@lt_max_iff]
        simp

      have h_numerator : |L * ‖x' - y‖ ^ 2| < ε * ‖x' - y‖ := by
        calc |L * ‖x' - y‖^2|
          _ = |L| * |‖x' - y‖^2| := by rw [@abs_mul]
          _ = |L| * ‖x' - y‖^2 := by rw [@abs_sq]
          _ = ‖x' - y‖*(|L| * ‖x' - y‖)  := by ring
          _ ≤ ‖x' - y‖*((max |L| 1)* ‖x' - y‖)  := by ring_nf; gcongr; rw [@le_max_iff]; simp
          _ < δ*((max |L| 1) * ‖x' - y‖) := by apply mul_lt_mul_of_pos_right h_x'_δ (h_norm_pos)
          _ = (ε/(max |L| 1))*(max |L| 1) * ‖x' - y‖ := by rw [@Mathlib.Tactic.RingNF.mul_assoc_rev]
          _ = ε * ‖x' - y‖ := by field_simp

      simp [h_norm]
      replace h_norm_pos : 0 < ‖ x' - y‖*2 := by aesop

      calc |L * ‖x' - y‖ ^ 2| / (‖x' - y‖ * 2)
        _ < ε * ‖x' - y‖ / (‖x' - y‖ * 2) := by apply div_lt_div_of_lt h_norm_pos h_numerator
        _ = ε / 2 := by field_simp; ring
        _ < ε := by linarith


---------------------------------------------------------
----  A sum rule for gradients
---- Basically an application of HasFDerivWithinAt.add
---------------------------------------------------------

theorem HasGradientWithinAt.add
{F : Type u_2}
[NormedAddCommGroup F]
[InnerProductSpace ℝ F]
[CompleteSpace F]
{f : F → ℝ}
{g : F → ℝ}
{f' : F}
{g' : F}
{x : F}
{s : Set F}
(hf : HasGradientWithinAt f f' s x)
(hg : HasGradientWithinAt g g' s x) :
HasGradientWithinAt (fun (y : F) => f y + g y) (f' + g') s x := by

  have hf_FDeriv : HasFDerivWithinAt f ((toDual ℝ F) (f')) s x := by
    exact hasGradientWithinAt_iff_hasFDerivWithinAt.mp hf

  have hg_FDeriv : HasFDerivWithinAt g ((toDual ℝ F) (g')) s x := by
    exact hasGradientWithinAt_iff_hasFDerivWithinAt.mp hg

  have h_lin : (toDual ℝ F) (f' + g') = (toDual ℝ F) (f') + (toDual ℝ F) (g') := by
    simp [toDual_apply]

  have h_sum : HasFDerivWithinAt (fun (y : F) => f y + g y) ((toDual ℝ F) (f' + g')) s x := by
    simp [h_lin]
    apply HasFDerivWithinAt.add hf_FDeriv hg_FDeriv

  apply hasGradientWithinAt_iff_hasFDerivWithinAt.mpr h_sum
