import Mathlib
import Gd.Lean.Basic
import Gd.Lean.ConvexFunction
import Gd.Lean.LipschitzGradient
import Gd.Lean.sequences

open Filter Metric Asymptotics Gradient InnerProductSpace Set Real

--------------------------------------------------------------------------------
---- Convergence theorem for gradient descent on smooth convex functions
--------------------------------------------------------------------------------

/--
Theorem showing that gradient descent converges at the rate of O(1/k) for
functions that are convex and have Lipschitz continuous gradients.

The proof follows these key steps:
1. Define one step of gradient descent: x_{k+1} = x_k - (1/L)∇f(x_k)
2. Define a_k = f(x_k) - inf f, and D_k = ‖x_k - x*‖² where x* is any minimizer
3. Prove that a_k ≤ D_k - D_{k+1}
4. Apply rate_from_monotonic_and_telescope_ub to get the O(1/k) convergence rate
-/
theorem gradient_descent_convergence 
{F : Type u_2}
[NormedAddCommGroup F]
[InnerProductSpace ℝ F]
[CompleteSpace F]
(f : F → ℝ)
(s : Set F)
(h_s_convex : Convex ℝ s)
(L : ℝ)
(h_L_pos : 0 < L)
(f' : F → F)
(h_lipschitz : LipschitzGradientOnWith (toNNReal L) f s f')
(h_f_bounded_below : BddBelow (f '' s))
(x₀ : F)
(h_x₀_in_s : x₀ ∈ s)
(h_min_exists : ∃ x_star ∈ s, f x_star = sInf (f '' s)) :
∃ (x_seq : ℕ → F) (C : ℝ), C > 0 ∧
  (x_seq 0 = x₀) ∧ 
  (∀ k, x_seq k ∈ s) ∧
  (∀ k, x_seq (k+1) = x_seq k - (1/L) • (f' (x_seq k))) ∧
  (∀ k, f (x_seq k) - sInf (f '' s) ≤ C / (k+1)) := sorry