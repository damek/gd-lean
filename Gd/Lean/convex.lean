import Mathlib
import Gd.Lean.Basic

open Set InnerProductSpace Filter Metric Convex Group Asymptotics

--------------------------------------------------------------------------------
---- The heart of the theorem ----
--------------------------------------------------------------------------------

-- Theorem shows that if $f x = 0$ and f y ≥ o(y-x) on a convex set s, then f y ≥ 0 for all y in s.
---- Pf: Without loss of generality $x = 0$.
------- For all t ∈ (0, 1), we have
------- f(y) ≥ f(ty)/t ≥ o(t)/t.
------- The left hand side is constant, while the right hand side tends to zero as t → 0.
---- Note: for smooth functions, we have the stronger assumption f(y) = o(y - x);
------ I'm working with the weaker assumption here since it may prove useful later.
theorem LittleO_convex_lb_non_neg
{F : Type u}
[NormedAddCommGroup F]
[InnerProductSpace ℝ F]
[CompleteSpace F]
(f : F → ℝ)
(x : F)
(s : Set F)
(h_zero : x ∈ s)
(h_convex : ConvexOn ℝ s f)
(h_base_point : f x = 0)
(h_LittleO : (fun y => min (f y) 0) =o[(nhds x)] (fun y => norm (y-x))):
∀ y ∈ s, 0 ≤ f y := by

  ------------------- Setting up the WLOG part of the proof -------------------
  have h_filter : Filter.Tendsto (fun y => y + x) (nhds 0) (nhds x) := by
    simp [@tendsto_nhds_nhds]
    intro ε hε
    use ε
    constructor
    . exact hε
    . intro y hy
      exact hy

  ---- Use this to deduce that g : y ↦ mapsto f(y + x) is little o of norm y using IsLittleO.comp_tendsto
  have shift_is_littleO : (fun y => min (f (y + x) ) 0) =o[(nhds 0)] (fun y => norm (y+ x - x)) := by
    exact IsLittleO.comp_tendsto h_LittleO h_filter

  let g := fun y => f (y + x)
  replace shift_is_littleO : (fun (y : F) => min (g y) 0 )=o[(nhds 0)] (fun (y : F) => norm y) := by
    simp [g] at *
    exact shift_is_littleO

  have h_gconvex : ConvexOn ℝ ((fun (z : F) => x + z) ⁻¹' s) g := by
    exact ConvexOn.translate_left h_convex x
  have h_gbase : g 0 = 0 := by
    simp [g, h_base_point]
  have h_zero_shift : 0 ∈ ((fun (z : F) => x + z) ⁻¹' s) := by
    simp [h_zero]

  suffices h_gnonneg : ∀ y ∈ ((fun (z : F) => x + z) ⁻¹' s), 0 ≤ g y
  . intro y hys
    have h_shift_y : y - x ∈ ((fun (z : F) => x + z) ⁻¹' s) := by
      simp [hys]

    calc f y
      _ = g (y - x) := by simp [g]
      _ ≥ 0 := by exact h_gnonneg (y - x) h_shift_y
  ------------------- End WLOG part of the proof -------------------

  ------------------- Main part of the proof -------------------
  intro y hys
  -- Replace the LittleO with a Tendsto
  have h_2 : Tendsto (fun x => (min (g x) 0) / norm x) (nhds 0) (nhds 0) := IsLittleO.tendsto_div_nhds_zero shift_is_littleO
  -- Replace Tendsto with epsilon delta notation.
  simp [@tendsto_nhds_nhds] at h_2
  have h_3 : ∀ (ε : ℝ), 0 < ε → ∃ δ, 0 < δ ∧ ∀ {t : ℝ}, ‖t•y‖ < δ → |min (g (t•y)) 0| / ‖t•y‖ < ε := by
    intro ε hε
    apply Exists.elim (h_2 ε hε)
    intro δ hδ
    apply Exists.intro δ
    apply And.intro hδ.left
    intro t ht
    exact hδ.right ht
  -- Prove that f(y) ≥ f(t y)/t on the line.
  have h_4 : ∀ (t : ℝ), (0 < t) ∧ (t < 1) → (g y) ≥ g (t•y)/t:= by
    intro t ht
    have sum_cond : 1- t + t = 1 := by
      rw [@sub_add_cancel]
    have nb_pos : 0 < (1-t) := by
      linarith

    rw [convexOn_iff_forall_pos] at h_gconvex
    have h_4' : t•(g y) ≥ g (t•y) := by
      calc t•(g y)
        _ = 0 + t•(g y)  := by rw [@self_eq_add_left]
        _ = (g 0) + t•(g y) := by rw [h_gbase]
        _ = (1-t)•(g 0) + t•(g y) := by field_simp; ring_nf; simp; apply Or.inr; exact h_base_point
        _ ≥ g ((1-t)•0 + t•y) := by apply h_gconvex.right h_zero_shift hys nb_pos ht.left sum_cond
        _ = g (t•y) := by simp
    simp
    simp at h_4'
    have ht' : 0 < t := by
      linarith
    have h_4'' : g (t•y) ≤ (g y)*t := by rw [mul_comm]; exact h_4'
    exact (div_le_iff ht').mpr h_4''

  -- To prove that f y is nonnegative, give your self an epsilon of room.
  suffices h_1 : ∀ ε > 0, 0 - ε ≤ g y
  . exact le_of_forall_sub_le h_1

  intro ε hε
  cases (eq_or_ne y 0) with
  -- if y = 0, then f y = 0, so we are done
  | inl h_eq =>
    rw [h_eq]
    simp [h_base_point]
    linarith
   -- The y ≠ 0
  | inr h_neq =>
    -------------- Setting up the epsilon and delta for the proof
    let ε' := ε/(norm y)
    have hε' : ε' > 0 := by
      simp [ε']
      exact div_pos hε (norm_pos_iff.mpr h_neq)
    apply Exists.elim (h_3 ε' hε')
    intro δ hδ
    let t_1 := (δ/((norm y)))
    have ht_1 : 0 < t_1 := by
      simp [t_1]
      exact div_pos hδ.left (norm_pos_iff.mpr h_neq)
    have ht : 0 < (min t_1 1)/2 := by positivity
    let t := (min t_1 1)/2
    replace ht : 0 < t := by simp [t]; exact ht
    have ht_ds : t < 1 := by
      calc t
        _ = (min (δ/((norm y))) 1)/2 := by simp [t]
        _ ≤ 1/2                      := by rw [div_le_div_right]; apply min_le_right; linarith
        _ < 1                        := by linarith
    replace ht_ds : (0 < t)∧(t < 1) := by
      exact ⟨ht, ht_ds⟩
    --------------
    ---- Proving that t meets the assumptions of h_4
    have ht_up : t ≤ t_1/2 := by simp [t_1]; gcongr; apply (min_le_left t_1 1)
    have ht' : norm (t • y) < δ := by
      simp [t]
      calc norm (t • y)
      _ =  (norm t) * norm y := norm_smul t y
      _ =  (min t_1 1)/2 * norm y := by simp [t, h_neq]; field_simp; linarith [ht_1]
      _ ≤  (t_1/2) * norm y := by simp; gcongr
      _ =  δ/2 := by simp; field_simp; ring_nf; field_simp; apply mul_inv_cancel_right₀; linarith [norm_pos_iff.mpr h_neq]
      _ < δ := by linarith

    -- Simplifying the epsilon of room.
    suffices _ : ε ≥ - g y
    . linarith

    -- Applying hδ to upper bound the min.
    have h_sub : ε/(norm y) > abs (min (g (t • y)) 0) / (t * (norm y))
      := calc ε/(norm y)
        _ = ε' := by apply Eq.symm; simp [ε']
        _ > abs (min (g (t • y)) 0) / ‖t • y‖ := by apply hδ.right; exact ht'
        _ = abs (min (g (t • y)) 0) / (t * (norm y)) := by rw [norm_smul_of_nonneg]; linarith

    ---- Replacing previous hypothesis after multiplying by norm y
    replace h_sub : ε > abs (min (g (t • y)) 0) / t :=
      calc ε
        _ = (ε / norm y) * norm y := by apply Eq.symm; field_simp; apply mul_inv_cancel_right₀; linarith [norm_pos_iff.mpr h_neq]
        _ > (abs (min (g (t • y)) 0) / (t * (norm y))) * norm y := by rw [gt_iff_lt]; exact mul_lt_mul_of_pos_right h_sub (norm_pos_iff.mpr h_neq)
        _ = (abs (min (g (t • y)) 0) /t) * norm y * (norm y)⁻¹ := by field_simp
        _ = (abs (min (g (t • y)) 0) /t) := by apply mul_inv_cancel_right₀; linarith [norm_pos_iff.mpr h_neq]

    -- Lower bound the min by - g(ty)
    have h_remove_min : abs (min (g (t • y)) 0) ≥ -(g (t•y)) :=
      calc abs (min (g (t • y)) 0)
        _ ≥ -(min (g (t • y)) 0) := by exact neg_le_abs_self (min (g (t • y)) 0)
        _ = max (-(g (t • y))) (-0) := by apply Eq.symm; exact max_neg_neg (g (t • y)) 0
        _ ≥ -(g (t • y)) := by exact le_max_left (-g (t • y)) (-0)

    ---- Dividing both sides by t.
    replace h_remove_min : abs (min (g (t • y)) 0)/t ≥ -(g (t•y))/t := by
      exact (div_le_div_right ht).mpr h_remove_min

    -- Reversing some hypothesis foruse in the final calculation
    have h_4_reverse :  -g y ≤ -((g (t•y))/t) := by
      exact neg_le_neg (h_4 t ht_ds)
    replace h_4_reverse :  -(g (t•y)/t) ≥ -g y := by
      exact h_4_reverse

    ---- Final calculation: combining h_sub, h_remove_min, and h_4_reverse.
    calc ε
      _ ≥ abs (min (g (t • y)) 0) / t := by linarith [h_sub]
      _ ≥ -(g (t•y))/t := h_remove_min
      _ ≥ -((g (t•y))/t) := by field_simp
      _ ≥ -(g y) := by exact h_4_reverse


---- Theorem shows that if f is convex on a set s and differentiable at a point x ∈ s, then ∀ y ∈ s, f y ≥ f x + inner f' (y - x)
---- Proof:
------ We consider the convex function g(y) := f(y) - f(x) - inner f' (y-x).
------ By assumption g(y) = o(y) on s, so by LittleO_convex_lb_non_neg, g(y) ≥ 0 for all y ∈ s.
theorem differentiable_gradient_inequality
{F : Type u}
[NormedAddCommGroup F]
[InnerProductSpace ℝ F]
[CompleteSpace F]
(f : F → ℝ)
(x : F)
(f' : F)
(h_grad_exists : HasGradientAt f f' x)
(s : Set F)
(h_x_in_s : x ∈ s)
(h : ConvexOn ℝ s f) :
∀ y ∈ s, f y ≥ f x + inner f' (y - x) := by

------------- Show that the function y → f y - inner f' y is convex ----------------
  ---- Will add the constant term in later in the proof.
  ------ An Alternative way would be to define a linear mapping and use that such mappings are convex.
  ------ I got frustrated reading the API, so I did it directly.
  let g_1 := fun y => f y - inner f' y
  have h_gconvex : ConvexOn ℝ s g_1 := by
    rw [convexOn_iff_forall_pos]
    rw [convexOn_iff_forall_pos] at h
    apply And.intro h.left
    intro x' hx' y' hy' a b ha hb hab
    calc g_1 (a • x' + b • y')
      _ = f (a • x' + b • y') - inner f' (a • x' + b • y') := by simp [g_1]
      _ = f (a • x' + b • y') - (inner f' (a • x') + inner f' (b • y')) := by simp [inner_add_right]
      _ = f (a • x' + b • y') - (a • inner f' x' + b • inner f' y') := by simp [inner_smul_right]
      _ = f (a • x' + b • y') - a • inner f' x' - b • inner f' y' := by rw [@sub_add_eq_sub_sub]
      _ ≤ a•(f x') + b•(f y') - a • inner f' x' - b • inner f' y' := by simp; exact h.right hx' hy' ha hb hab
      _ = a•(f x' - inner f' x') + b•(f y' - inner f' y') := by simp; ring
      _ = a•(g_1 x') + b•(g_1 y') := by simp [g_1]
  --- Now we add in the constant term and call a preexisting lemma to verify the resulting function is convex.
  let g :=  g_1  + fun _ => - f x + inner f' x
  have h_g : ConvexOn ℝ s g := by
    exact ConvexOn.add_const h_gconvex (-f x + inner f' x)

  --- Show that g x = 0.
  have h_g0 : g x = 0 := by
    calc g x
      _ = (f x - inner f' x) + (fun _ => - f x + inner f' x) x := by simp
      _ = 0 := by simp

  ---- Now we introduce the gradient.
  have h1 := (hasGradientAt_iff_isLittleO).mp h_grad_exists

  ---- The g = (f - linearization) is little o by definition of the gradient.
  ---- I wanted to deduce this automatically, but lean isn't sure that g agrees with (f - linearization) on s, so I just verified.
  ------ Probably a smarter way to do this.
  have h_eq : ∀ y, (fun x' ↦ f x' - f x - inner f' (x' - x)) y = g y := by
    intro y
    calc (fun x' ↦ f x' - f x - inner f' (x' - x)) y
      _ = f y - f x - inner f' (y - x) := by simp
      _ = f y - f x - (inner f' y - inner f' x) := by simp [inner_sub_right]
      _ = f y - inner f' y + (- f x + inner f' x) := by ring
      _ = f y - inner f' y + (fun _ => - f x + inner f' x) y := by simp

  have h_lin_equal_g : (fun x' ↦ f x' - f x - inner f' (x' - x)) = g := funext h_eq

  have h_g' : g =o[(nhds x)] (fun y : F => norm (y-x)) := by
    simp [h_lin_equal_g] at h1
    simp [h1]
  ----------

  ----------
  -- We know that g = o(y - x). I want to deduce that min{g(y), 0} =o(y - x), which is equivalent to g(y) ≥ o(y - x)).
  ---- To do this, we need to apply IsLittleO_comp_left, which allows us to scale a little o identity by a φ=O(x) identity.
  ---- To apply the theorem, we first need to show that norm (y-x) =o(1). I couldn't find this in the lean library.
  ------ We will later apply this result to ensure that g = o(1), which is needed for the theorem.
  have h_norm_LittleO_1 : (Filter.Tendsto (fun y : F => norm (y - x)) (nhds x) (nhds 0)) := by
    rw [@tendsto_nhds_nhds]
    intro ε hε
    use ε
    constructor
    . exact hε
    . intro y hy
      calc dist (norm (y - x)) 0
        _ = norm (y-x) := by simp
        _ = dist y x := by rw [← @dist_eq_norm]
        _ < ε := by exact hy

  ---- By transitivity g is o(1)
  have h_g_littleO_one : g =o[(nhds x)] (fun _x ↦ (1 : ℝ)) := by
    rw [isLittleO_one_iff]
    exact IsLittleO.trans_tendsto h_g' h_norm_LittleO_1

  ---- Now show that the outer function φ is O(x)
  have h_φ : (fun (x : ℝ) ↦ min x 0) =O[nhds 0] (fun (x : ℝ) ↦ x) := by
    exact min_with_zero_is_BigO_id

  ---- Now apply IsLittleO_comp_left to get that min g 0 = φ ∘ g = o(y-x)
  have h_g_min : (fun y => min (g y) 0) =o[(nhds x)] (fun y => norm (y-x)) := by
    exact IsLittleO_comp_left h_φ h_g_littleO_one h_g'

  ---- With this, we can apply the hammer to deduce that g y ≥ 0 for all y ∈ s
  have h_gnonneg : ∀ y ∈ s, 0 ≤ g y := by
    exact LittleO_convex_lb_non_neg g x s h_x_in_s h_g h_g0 h_g_min

  ---- The final part of the theorem does the straightforward calculation to show that f y ≥ f x + inner f' (y - x).
  intro y hys
  have h_gy : 0 ≤ g y := by
    exact h_gnonneg y hys

  simp [g] at h_gy
  calc f x + inner f' (y - x)
    _ = f x + inner f' y - inner f' x := by rw [@inner_sub_right]; ring
    _ ≤ f y := by linarith [g]

---- End: Main theorem ----
