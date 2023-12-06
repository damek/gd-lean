import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Algebra.Abs
import Mathlib.Topology.Basic
import Mathlib.Algebra.Module.Basic



open Set

def R_set : Set ℝ := Set.univ

def f : ℝ → ℝ := fun x => x

open InnerProductSpace

theorem gradient_inequality
{F : Type u}
[NormedAddCommGroup F]
[InnerProductSpace ℝ F]
[CompleteSpace F]
(f : F → ℝ)
(x : F)
(f' : F)
(h_grad_exists : HasGradientAt f f' x)
(s : Set F)
(h : ConvexOn ℝ s f) :
∀ y : F, f y ≥ f x + inner f' (y - x) := by
  let h1 := (hasGradientAt_iff_isLittleO).mp h_grad_exists
  intro y
  have linearized_fun := fun y => (f y) - (f x) - (inner f' (y - x))
  have diff_fun := fun y => y - x
  have big_O := (Asymptotics.isLittleO_iff_forall_isBigOWith).mp h1

  -- let f_y := fun (t : ℝ) => f (y + t•(x-y)) - f x - t*inner f' (y - x)
  -- We have f_y(t)/t → 0 as t → 0
  -- let k := fun t : ℝ => x + t•(y - x)
  -- have hk := Filter.Tendsto k (nhds 0) (nhds x)
  -- have hcomp := Asymptotics.IsLittleO.comp_tendsto hk h1
  -- have h2 := comp_tendsto h1


  -- have h2 : Filter.Tendsto (fun (y : F) => (f_y t)/t (nhds x) (nhds 0) := by
    -- sorry

  -- suffices h2 : Filter.
  -- let h2 = fun (y : F) => NegPart (f y - f x - inner f' (y - x))
  -- suffices h_neg : Filter.Tendsto (fun (y : F) => min (f y - f x - inner f' (y - x)) 0) (nhds x) (nhds 0)
  -- .
  sorry
