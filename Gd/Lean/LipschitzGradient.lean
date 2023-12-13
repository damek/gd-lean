import Mathlib
import Gd.Lean.Basic

open Gradient MetricSpace InnerProductSpace Real


--------------------------------------------------------------------------------
---- Definition of Lipschitz continuity of the gradient on a set
--------------------------------------------------------------------------------
def LipschitzGradientOnWith
{F : Type u_2}
[NormedAddCommGroup F]
[InnerProductSpace ℝ F]
[CompleteSpace F]
(L : NNReal)
(f : F → ℝ)
(s : Set F)
(f' : F → F) :=
(∀ x ∈ s, HasGradientWithinAt f (f' x) s x) ∧ (LipschitzOnWith L f' s)

-- A version of domain_mvt for gradient, instead of FDeriv dual formulation
theorem domain_mvt_gradient
{F : Type u_2}
[NormedAddCommGroup F]
[InnerProductSpace ℝ F]
[CompleteSpace F]
(f : F → ℝ)
(s : Set F)
(f' : F → F)
(x : F)
(y : F)
(hf : ∀ x ∈ s, HasGradientWithinAt f (f' x) s x)
(hs : Convex ℝ s)
(xs : x ∈ s)
(ys : y ∈ s) :
∃ z ∈ segment ℝ x y, f y - f x = inner (f' z) (y - x) := by

  have hf_FDeriv : ∀ x' ∈ s, HasFDerivWithinAt f ((toDual ℝ F) (f' x')) s x' := by
    intro x' xs'
    exact hasGradientWithinAt_iff_hasFDerivWithinAt.mp (hf x' xs')

  -- let gradient_as_linear_mapping :=

  have h_mvt_with_dual : ∃ z ∈ segment ℝ x y, f y - f x =  ((toDual ℝ F) (f' z)) (y - x) := by
    exact domain_mvt hf_FDeriv hs xs ys

  apply Exists.elim h_mvt_with_dual
  intro z hz
  use z
  constructor
  . exact hz.1
  . have h_equivalence : inner (f' z) (y - x) = ((InnerProductSpace.toDual ℝ F) (f' z)) (y-x):= by
      simp [InnerProductSpace.toDual_apply]
      rw [@inner_sub_right]

    exact hz.right ▸ h_equivalence.symm


--------------------------------------------------------------------------------
---- Descent lemma:
---- If ∇ f(x) is Lipschitz continuous on a set s, then
------ f(y) ≤ f(x) + ⟨∇f(x), y-x⟩ + L/2 * ||y-x||^2 (∀ x, y ∈ s)
---- Proof:
----- Let g(y) = f(y) - L/2 * ||y-x||^2.
----- Apply the mean value theorem:
----- ∃ z ∈ [x, y], g(y) - g(x) = ⟨∇g(z), y-x⟩
-------- i.e., f(y) - f(x) - L/2 * ||y-x||^2 = ⟨∇f(z) - L(z-x), y-x⟩
-------- = ⟨∇f(x), y-x⟩ + ⟨∇f(z) - ∇f(x), y-x⟩ - ⟨L(z-x), y-x⟩.
------ Now since z ∈ [x, y], we have z = a*x + b*y for some a, b ∈ [0, 1] with a + b = 1.
------- Thus, z - x = b*(y-x), and ⟨L(z-x), y-x⟩ = L*b*||y-x||^2.
------- Also, since ∇f is Lipschitz continuous, we have
---------- ||∇f(z) - ∇f(x)|| ≤ L*||z-x|| = L*b*||y-x||.
------- Thus, ⟨∇f(z) - ∇f(x), y-x⟩ ≤ L*b*||y-x||^2.
------- Putting it all together, we have
------- f(y) - f(x) - L/2 * ||y-x||^2 ≤ ⟨∇f(x), y-x⟩ + L*b*||y-x||^2 - L*b*||y-x||^2
------- = ⟨∇f(x), y-x⟩
--------------------------------------------------------------------------------
theorem DescentLemmaOnWith
{F : Type u_2}
[NormedAddCommGroup F]
[InnerProductSpace ℝ F]
[CompleteSpace F]
(L : ℝ)
(h_L : 0 ≤ L)
(f : F → ℝ)
(s : Set F)
(f' : F → F)
(h_s_convex : Convex ℝ s)
(h_lg : LipschitzGradientOnWith (toNNReal L) f s f'):
∀ x ∈ s, ∀ y ∈ s, f (y) ≤ f (x) + inner (f' x) (y-x) + (L/2) * norm (y-x)^2 := by
  intro x xs y ys
  let g := fun x' : F => f (x') + (-L/2)*norm (x' - x)^2
  let g' := fun z => f' z + (-L)•(z - x)
  ----------------------------------------------------------------------------------------------
  ----- The mean value theorem holds for g on s, since g is differentiable on s.
  ----------------------------------------------------------------------------------------------
  have h_mvt : ∃ z ∈ segment ℝ x y, g y - g x = inner (g' z) (y - x) := by

    have h_sum_deriv : ∀ z ∈ s, HasGradientWithinAt g (f' z + -L•(z - x)) s z := by
      have h_f_deriv : ∀ z ∈ s, HasGradientWithinAt f (f' z) s z := by
        exact h_lg.left
      have h_norm_deriv : ∀ z ∈ s, HasGradientWithinAt (fun z => (-L/2)*(norm (z - x))^2) (-L • (z - x)) s z := by
        intro z zs
        apply (GradientOfNormSquaredWithin s)
        . exact xs
        . exact zs

      intro z zs
      simp [h_norm_deriv]
      have h_sum_to_simp : HasGradientWithinAt (fun y ↦ f y + -L / 2 * ‖y - x‖ ^ 2) (f' z + -L • (z - x)) s z:=
          by exact HasGradientWithinAt.add (h_f_deriv z zs) (h_norm_deriv z zs)
      simp_all only [ge_iff_le, neg_smul]

    exact domain_mvt_gradient g s g' x y h_sum_deriv h_s_convex xs ys
  ----------------------------------------------------------------------------------------------

  ----------------------------------------------------------------------------------------------
  --- Set up the z ∈ segment x y and g y - g x = inner (g' z) (y - x) from the mean value theorem
  ----------------------------------------------------------------------------------------------
  apply Exists.elim h_mvt
  intro z hz
  have zs : z ∈ s := by
    -- follows since z ∈ segment x y and s is convex
    exact h_s_convex.segment_subset xs ys hz.1

  let h_seg := hz.1
  rw [mem_segment_iff_div] at h_seg
  apply Exists.elim h_seg
  intro t ht
  apply Exists.elim ht
  intro t' ht'
  let a := t / (t + t')
  have h_a : 0 ≤ a := by
    simp [a]
    apply div_nonneg
    exact ht'.left
    linarith [ht'.right.right.left]
  let b := t' / (t + t')
  have h_b : 0 ≤ b := by
    simp [b]
    apply div_nonneg
    exact ht'.right.left
    linarith [ht'.right.right.left]

  have h_sum_weights : a + b = 1 := by
    simp [a, b]
    rw [←add_div]
    rw [div_self]
    linarith

  have h_z : z = a • x + b • y := by
    simp [a, b]
    simp [ht'.2.2.2]

  replace h_z : z - x = b • (y - x) := by
    calc z - x
      _ = a • x + b • y - x := by rw [h_z]
      _ = a • x + b • y - (a + b) • x := by rw [h_sum_weights]; simp
      _ = b • (y - x) := by simp [add_smul, sub_smul]; rw [←smul_sub]

  ----------------------------------------------------------------------------------------------

  ----------------------------------------------------------------------------------------------
  --- Set up the conclusion of the descent lemma
  ----------------------------------------------------------------------------------------------
  suffices h_conclusion : f (y) - f (x) - (L/2) * norm (y-x)^2 ≤ inner (f' x) (y-x)
  . linarith
  suffices h_conclusion : g (y) - g (x) ≤ inner (f' x) (y-x)
  . have h_equality : g y = f (y) - (L/2) * norm (y-x)^2 := by
      simp [g]
      ring
    have h_equality' : g x = f (x) := by
      simp [g]
    have h_equality'' : g y - g x = f (y) - f (x) - (L/2) * norm (y-x)^2 := by
      simp [g]
      ring
    simp_all only [ge_iff_le, neg_smul, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow',
      mul_zero, add_zero, tsub_le_iff_right]
  ----------------------------------------------------------------------------------------------


  ----------------------------------------------------------------------------------------------
  --- Simplify the dot product
  ----------------------------------------------------------------------------------------------
  have h_inner_z : inner (-L•(z - x)) (y - x) = -L * b * ‖ y - x‖^2 := by
    calc inner (- L •(z - x)) (y - x)
      _ = - L * inner (z - x) (y - x) := by simp [inner_smul_right]; rw [@real_inner_smul_left]
      _ = - L * inner (b • (y - x)) (y - x) := by rw [h_z]
      _ = - L * b * inner (y - x) (y - x) := by rw [@real_inner_smul_left]; ring
      _ = - L * b * ‖ y - x‖^2 := by rw [@real_inner_self_eq_norm_sq]

  ----------------------------------------------------------------------------------------------
  -- Apply the Lipschitz continuity of ∇f to bound the dot product
  ----------------------------------------------------------------------------------------------

  have h_norm_bound : ‖f' z - f' x‖ ≤ L * ‖z - x‖ := by
    calc ‖f' z - f' x‖
      _ = dist (f' z) (f' x) := by rw [dist_eq_norm]
      _ ≤ (toNNReal L) * dist z x := by exact h_lg.right.dist_le_mul z zs x xs
      _ ≤ (toNNReal L) * ‖z - x‖ := by rw [dist_eq_norm]
      _ = L * ‖z - x‖ := by simp [toNNReal]; apply Or.inl h_L

  have h_cauchy_Lip : inner (f' z - f' x) (y - x) ≤ L * b * ‖y - x‖^2 := by
    calc inner (f' z - f' x) (y - x)
      _ ≤ ‖f' z - f' x‖ * ‖y - x‖ := by exact real_inner_le_norm (f' z - f' x) (y - x)
      _ ≤ L * ‖z - x‖ * ‖y - x‖ := by exact mul_le_mul_of_nonneg_right h_norm_bound (norm_nonneg _)
      _ = L * ‖ b• (y - x)‖ * ‖ y - x‖ := by rw [h_z]
      _ = L * ‖b‖ * ‖ y - x‖ * ‖ y - x‖ := by rw [norm_smul]; ring
      _ = (L * ‖b‖) * ‖ y - x‖^2 := by ring
      _ = L * b * ‖y - x‖^2 := by rw [norm_eq_abs]; simp [abs_of_nonneg h_b]

  ----------------------------------------------------------------------------------------------

  ----------------------------------------------------------------------------------------------
  --- Put it all together
  ----------------------------------------------------------------------------------------------

  calc g y - g x
    _ = inner (g' z) (y - x) := hz.right
    _ = inner (f' z + -L•(z - x)) (y - x) := by simp [g']
    _ = inner (f' z) (y - x) + inner (-L•(z - x)) (y - x) := by rw [inner_add_left]
    _ = inner (f' z) (y - x) + -L * b * ‖ y - x‖^2 := by rw [h_inner_z]
    _ = inner (f' z - f' x) (y - x) + inner (f' x) (y - x) + -L * b * ‖ y - x‖^2 := by rw [←inner_add_left]; simp_all only [ge_iff_le,
                                                                                                                     sub_self,
                                                                                                                     norm_zero,
                                                                                                                     ne_eq,
                                                                                                                     OfNat.ofNat_ne_zero,
                                                                                                                     not_false_eq_true,
                                                                                                                     zero_pow',
                                                                                                                     mul_zero,
                                                                                                                     add_zero,
                                                                                                                     neg_smul,
                                                                                                                     exists_and_left,
                                                                                                                     true_and,
                                                                                                                     inner_neg_left,
                                                                                                                     neg_mul,
                                                                                                                     neg_inj,
                                                                                                                     sub_add_cancel]
    _ ≤ L * b * ‖ y - x‖^2  + inner (f' x) (y - x) + -L * b * ‖ y - x‖^2 := by linarith [h_cauchy_Lip]
    _ = inner (f' x) (y - x) := by ring
