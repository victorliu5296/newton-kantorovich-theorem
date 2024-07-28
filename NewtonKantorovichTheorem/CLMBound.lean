import Mathlib.Tactic
-- For some reason you need at least 1 import or it doesn't recognize mathlib

open ContinuousLinearMap

-- Define the variables for Banach spaces X and Y
variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable [Nontrivial X] [Nontrivial Y]

lemma ContinuousLinearMap.inverse_norm_le
    (A B : X ≃L[ℝ] Y)
    (h_norm : ‖(A.symm : Y →L[ℝ] X).comp ((B : X →L[ℝ] Y) - (A : X →L[ℝ] Y))‖ < 1) :
    ‖(B.symm : Y →L[ℝ] X)‖ ≤ ‖(A.symm : Y →L[ℝ] X)‖ / (1 - ‖(A.symm : Y →L[ℝ] X).comp ((B : X →L[ℝ] Y) - (A : X →L[ℝ] Y))‖) := by
  -- Let t be the perturbation
  let t := (A.symm : Y →L[ℝ] X).comp ((B : X →L[ℝ] Y) - (A : X →L[ℝ] Y))
  have ht : ‖-t‖ < 1 := by
    simp
    exact h_norm

  -- Use `oneSub` to get the inverse of (1 - (-t)) = 1 + t
  let u := Units.oneSub (-t) ht
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
