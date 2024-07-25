import Mathlib.Analysis.NormedSpace.BoundedLinearMaps
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs

open Set Function Topology Metric ContinuousLinearMap Filter Units

section NewtonKantorovich1Constant

-- Define the variables for Banach spaces X and Y
variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable [Nontrivial X] [Nontrivial Y]
-- Define the open subset Ω of X
variable (Ω : Set X) (hΩ : IsOpen Ω)
-- Define the point x₀ in Ω
variable (x₀ : X) (hx₀ : x₀ ∈ Ω)
-- Define the C¹ mapping f: Ω → Y
variable (f : X → Y) (hf : ContDiffOn ℝ 1 f Ω)
-- Define the radius r
variable (r : ℝ) (hr : 0 < r)
-- Define f' as a mapping
variable (f' : X → X →L[ℝ] Y)
         (hf' : ∀ x ∈ Ω, HasFDerivAt f (f' x) x)

-- Assumptions
variable (h_subset : closedBall x₀ r ⊆ Ω)
variable (h_bound1 : ‖(f' x₀).inverse (f x₀)‖ ≤ r / 2)
variable (h_bound2 : ∀ (u v : X), u ∈ closedBall x₀ r → v ∈ closedBall x₀ r →
  -- ∀ x : X, ‖(f' x₀).inverse ((f' u - f' v) x)‖ ≤ (1 / r) * ‖u - v‖ * ‖x‖)
  ‖(f' x₀).inverse.comp (f' u - f' v)‖ ≤ (1 / r) * ‖u - v‖)

-- Newton iteration sequence
noncomputable def newton_seq : Nat → X
| 0       => x₀
| (n + 1) => newton_seq n - (f' (newton_seq n)).inverse (f (newton_seq n))

-- Auxiliary function h
noncomputable def h (x : X) : X := (f' x₀).inverse (f x)
noncomputable def h' (x : X) : X →L[ℝ] X := (f' x₀).inverse.comp (f' x)
variable (hh' : ∀ x ∈ Ω, HasFDerivAt (h x₀ f f') (h' x₀ f' x) x)

lemma invertible_of_near_invertible
  (A B : X ≃L[ℝ] Y)
  (h_norm : ‖(A.symm : Y →L[ℝ] X).comp ((B : X →L[ℝ] Y) - (A : X →L[ℝ] Y))‖ < 1) :
  ‖(B.symm : Y →L[ℝ] X)‖ ≤ ‖(A.symm : Y →L[ℝ] X)‖ / (1 - ‖(A.symm : Y →L[ℝ] X).comp ((B : X →L[ℝ] Y) - (A : X →L[ℝ] Y))‖) := by
  -- Let t be the perturbation
  let t := (A.symm : Y →L[ℝ] X).comp ((B : X →L[ℝ] Y) - (A : X →L[ℝ] Y))
  have ht : ‖-t‖ < 1 := by
    simp
    exact h_norm

  -- Use `oneSub` to get the inverse of (1 - (-t)) = 1 + t
  let u := oneSub (-t) ht
  have hu : u.val = 1 + t := by
    rw [← sub_neg_eq_add]
    rfl

  -- Now we know that (B : X →L[ℝ] Y) = A ∘ (u.val)
  have hB : (B : X →L[ℝ] Y) = (A : X →L[ℝ] Y).comp (u.val) := by
    rw [hu]
    rw [comp_add, ← comp_assoc]
    have : 1 = ContinuousLinearMap.id ℝ X := by
      exact rfl
    simp [this]

  -- Hence, B is invertible and its inverse is given by (u⁻¹).comp A⁻¹
  have hB_inv : (B.symm : Y →L[ℝ] X) = (u.inv).comp (A.symm : Y →L[ℝ] X) := by
    -- We'll prove this by showing that both sides are left inverses of B
    apply ContinuousLinearMap.ext
    intro y

    -- Show that B.symm (B x) = x
    have h1 : ∀ x, (B.symm : Y →L[ℝ] X) ((B : X →L[ℝ] Y) x) = x := by
      intro x
      exact ContinuousLinearEquiv.symm_apply_apply B x

    -- Show that (u.inv ∘ A.symm) (B x) = x
    have h2 : ∀ x, ((u.inv).comp (A.symm : Y →L[ℝ] X)) ((B : X →L[ℝ] Y) x) = x := by
      intro x
      calc ((u.inv).comp (A.symm : Y →L[ℝ] X)) ((B : X →L[ℝ] Y) x)
        = u.inv ((A.symm : Y →L[ℝ] X) ((B : X →L[ℝ] Y) x)) := by rfl
        _ = u.inv ((A.symm : Y →L[ℝ] X) ((A : X →L[ℝ] Y) (u.val x))) := by rw [hB]; rfl
        _ = u.inv (u.val x) := by simp
        _ = x := by
          have h_inv : u.inv.comp u.val = ContinuousLinearMap.id ℝ X := u.inv_val
          rw [← ContinuousLinearMap.comp_apply]
          exact congrArg (fun f => f x) h_inv

    -- Now we can conclude that the two expressions are equal
    calc (B.symm : Y →L[ℝ] X) y
      = (B.symm : Y →L[ℝ] X) ((B : X →L[ℝ] Y) ((B.symm : Y →L[ℝ] X) y)) := by simp
      _ = (B.symm : Y →L[ℝ] X) y := by rw [h1 ((B.symm : Y →L[ℝ] X) y)]
      _ = ((u.inv).comp (A.symm : Y →L[ℝ] X)) ((B : X →L[ℝ] Y) ((B.symm : Y →L[ℝ] X) y)) := by
        have h_eq := h2 ((B.symm : Y →L[ℝ] X) y)
        nth_rw 1 [← h_eq]
      _ = ((u.inv).comp (A.symm : Y →L[ℝ] X)) y := by simp

  -- Use `NormedRing.tsum_geometric_of_norm_lt_one` to bound the norm of u.inv
  have h_u_inv : ‖u.inv‖ ≤ (1 - ‖t‖)⁻¹ := by
    have h_geom_series := NormedRing.tsum_geometric_of_norm_lt_one (-t) ht
    have h_one_norm : ‖(1 : X →L[ℝ] X)‖ = 1 := norm_id
    rw [h_one_norm] at h_geom_series
    simp at h_geom_series
    simp
    exact h_geom_series

  calc
    ‖(B.symm : Y →L[ℝ] X)‖ = ‖(u.inv).comp (A.symm : Y →L[ℝ] X)‖ := by rw [hB_inv]
    _ ≤ ‖u.inv‖ * ‖(A.symm : Y →L[ℝ] X)‖ := by exact opNorm_comp_le u.inv (A.symm : Y →L[ℝ] X)
    _ ≤ (1 - ‖t‖)⁻¹ * ‖(A.symm : Y →L[ℝ] X)‖ := mul_le_mul_of_nonneg_right h_u_inv (norm_nonneg _)
    _ = ‖(A.symm : Y →L[ℝ] X)‖ / (1 - ‖t‖) := by exact Eq.symm (div_eq_inv_mul ‖(A.symm : Y →L[ℝ] X)‖ (1 - ‖t‖))

-- (i) Estimates

lemma h_inverse_bound (x : X) (hx : x ∈ ball x₀ r) :
  ‖(h' x₀ f' x).inverse‖ ≤ 1 / (1 - ‖x - x₀‖ / r) := by
  have h_derivative_bound : ‖h' x₀ f' x - h' x₀ f' x₀‖ < 1 := by
    have hx_in_ball : x ∈ closedBall x₀ r := by
      exact ball_subset_closedBall hx
    have h_bound := h_bound2 x x₀ hx_in_ball (mem_closedBall_self (le_of_lt hr))
    repeat' rw [h']
    calc
      ‖(f' x₀).inverse.comp (f' x) - (f' x₀).inverse.comp (f' x₀)‖
      = ‖(f' x₀).inverse.comp (f' x - f' x₀)‖ := by simp [sub_eq_add_neg, comp_sub]
      _ ≤ 1 / r * ‖x - x₀‖ := by apply h_bound
      _ < 1 := by
        simp
        apply (inv_mul_lt_iff hr).mpr
        simp
        exact mem_ball_iff_norm.mp hx

  sorry
  -- apply invertible_near_bounded_linear_map (h' x₀) (h' x) (h_derivative_bound)

lemma h_difference_bound (u v : X) (hu : u ∈ closedBall x₀ r) (hv : v ∈ closedBall x₀ r) :
  ‖h x₀ f f' u - h x₀ f f'  v - h' x₀ f' v (u - v)‖ ≤ (1 / (2 * r)) * ‖u - v‖^2 := by
sorry

-- (ii) Newton iterates properties
lemma newton_iterates_properties :
  ∀ k : ℕ,
    newton_seq x₀ f f' k ∈ ball x₀ r ∧
    ‖newton_seq x₀ f f' k - newton_seq x₀ f f' (k-1)‖ ≤ r / 2^k ∧
    ‖newton_seq x₀ f f' k - x₀‖ ≤ r * (1 - 1 / 2^k) ∧
    ‖(h' x₀ f' (newton_seq x₀ f f' k)).inverse‖ ≤ 2^k ∧
    ‖h x₀ f f' (newton_seq x₀ f f' k)‖ ≤ r / 2^(2*k+1) := by
sorry

-- (iii) Convergence to zero
lemma newton_seq_converges :
  ∃ a, a ∈ closedBall x₀ r ∧
      Tendsto (newton_seq x₀ f f') atTop (𝓝 a) ∧
      f a = 0 ∧
      ∀ k, ‖newton_seq x₀ f f' k - a‖ ≤ r / 2^k := by
sorry

-- (iv) Uniqueness of zero
lemma zero_unique (a b : X) (ha : a ∈ closedBall x₀ r) (hb : b ∈ closedBall x₀ r)
  (hfa : f a = 0) (hfb : f b = 0) : a = b := by
sorry

theorem newton_kantorovich_1_const :
  (∀ k : Nat, (newton_seq x₀ f f' k) ∈ closedBall x₀ r) ∧
  (∃! a ∈ closedBall x₀ r, f a = 0 ∧ ∀ k : Nat, ‖newton_seq x₀ f f' k - a‖ ≤ r / 2^k) := by
sorry

end NewtonKantorovich1Constant
