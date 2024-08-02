import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import NewtonKantorovichTheorem.MeanValueBanach
import NewtonKantorovichTheorem.CLMBound

open Set Topology Metric ContinuousLinearMap

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
-- Define f' as a mapping
variable (f' : X → X ≃L[ℝ] Y)
         (hf' : ∀ x ∈ Ω, HasFDerivAt f (f' x : X →L[ℝ] Y) x)
variable (a b : X) (hab : ∀ t, t ∈ Icc (0 : ℝ) 1 → (a + t • (b - a)) ∈ Ω)

-- Define the parameteric path γ from a to b
def γ (a b : X) : ℝ → X := fun t ↦ a + t • (b - a)

lemma γ_continuous (a b : X) (t : ℝ) : ContinuousWithinAt (γ a b) (Icc 0 1) t := by
  apply ContinuousWithinAt.add continuousWithinAt_const
  · apply ContinuousWithinAt.smul
    · exact continuousWithinAt_id
    · exact continuousWithinAt_const

noncomputable def f'_clm : X → X →L[ℝ] Y := fun x ↦ (f' x).toContinuousLinearMap

lemma f'_clm_continuous {Ω : Set X}  {f : X → Y}
    {f' : X → X ≃L[ℝ] Y}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω)
    (hf' : ∀ x ∈ Ω, HasFDerivAt f (f' x : X →L[ℝ] Y) x) :
    ContinuousOn (f'_clm f') Ω := by
  have h_fderiv_cont : ContinuousOn (fun x ↦ fderiv ℝ f x) Ω := by
    apply ContDiffOn.continuousOn_fderiv_of_isOpen hf hΩ
    norm_num
  apply ContinuousOn.congr h_fderiv_cont
  intro x hx
  simp [f'_clm]
  exact Eq.symm (HasFDerivAt.fderiv (hf' x hx))

lemma f'_cont_a_b :
    ContinuousOn (fun t : ℝ ↦
      (f' (a + t • (b - a)) : X →L[ℝ] Y)) (Icc 0 1) := by
  have h_comp : ContinuousOn (f'_clm f' ∘ γ a b) (Icc 0 1):= by
    apply ContinuousOn.comp
    · exact f'_clm_continuous hΩ hf hf'
    · intro t _
      exact γ_continuous a b t
    · exact hab
  exact h_comp

-- Auxiliary function h
noncomputable def h (x : X) : X := (f' x₀).symm (f x)
noncomputable def h' (x : X) : X ≃L[ℝ] X := (f' x).trans (f' x₀).symm
noncomputable def h'_clm : X → X →L[ℝ] X := fun x ↦ (h' x₀ f' x).toContinuousLinearMap

lemma h'_deriv : ∀ x ∈ Ω, HasFDerivAt (h x₀ f f') (h'_clm x₀ f' x) x := by
  intro x hx
  -- Step 1: Express h as a composition
  have h_comp : h x₀ f f' = (f' x₀).symm ∘ f := rfl
  have h'_comp : h'_clm x₀ f' x = ((f' x₀).symm : Y →L[ℝ] X).comp (f' x : X →L[ℝ] Y) := rfl
  rw [h_comp, h'_comp]
  exact (ContinuousLinearEquiv.comp_hasFDerivAt_iff (f' x₀).symm).mpr (hf' x hx)

lemma h'_eq_deriv : ∀ x ∈ Ω, h' x₀ f' x = fderiv ℝ (h x₀ f f') x := by
  exact fun x a ↦ Eq.symm (HasFDerivAt.fderiv ((h'_deriv Ω x₀ f f' hf') x a))

lemma h'_cont : ∀ x ∈ Ω, ContinuousOn (h'_clm x₀ f' x) Ω := by fun_prop

lemma h_contDiffOn : ContDiffOn ℝ 1 (h x₀ f f') Ω := by
  have h_comp : h x₀ f f' = (f' x₀).symm ∘ f := rfl
  rw [h_comp]
  -- Apply the chain rule for ContDiffOn
  rw [ContinuousLinearEquiv.comp_contDiffOn_iff (f' x₀).symm]
  exact hf

lemma h'_cont_a_b {Ω : Set X} {x₀ a b : X} {f : X → Y} {f' : X → X ≃L[ℝ] Y}
    (hab : ∀ t, t ∈ Icc (0 : ℝ) 1 → (a + t • (b - a)) ∈ Ω)
    (hΩ : IsOpen Ω)
    (hh_contDiffOn : ContDiffOn ℝ 1 (h x₀ f f') Ω)
    (hh' : ∀ x ∈ Ω, HasFDerivAt (h x₀ f f') (h' x₀ f' x : X →L[ℝ] X) x) :
    ContinuousOn (fun t : ℝ ↦
      ((h' x₀ f') (a + t • (b - a)) : X →L[ℝ] X)) (Icc 0 1) := by
  exact f'_cont_a_b Ω hΩ (h x₀ f f') hh_contDiffOn (h' x₀ f') hh' a b hab

lemma h'x₀_eq_id : h' x₀ f' x₀ = ContinuousLinearMap.id ℝ X := by
  unfold h'
  ext x₀.symm_apply_apply
  aesop

lemma h'x₀_symm_eq_id: (h' x₀ f' x₀).symm = ContinuousLinearMap.id ℝ X := by
  unfold h'
  ext x₀.symm_apply_apply
  aesop

-- Define the radius r
variable (r : ℝ) (hr : 0 < r)

-- Assumptions
variable (h_subset : closedBall x₀ r ⊆ Ω)
variable (h_bound1 : ‖(f' x₀).symm (f x₀)‖ ≤ r / 2)
variable (h_bound2 : ∀ (u v : X), u ∈ closedBall x₀ r → v ∈ closedBall x₀ r →
  -- ∀ x : X, ‖(f' x₀).inverse ((f' u - f' v) x)‖ ≤ (1 / r) * ‖u - v‖ * ‖x‖)
  ‖((f' x₀).symm : Y →L[ℝ] X).comp ((f' u : X →L[ℝ] Y) - (f' v : X →L[ℝ] Y))‖ ≤ (1 / r) * ‖u - v‖)

-- Newton iteration sequence
noncomputable def newton_seq : Nat → X
| 0       => x₀
| (n + 1) => newton_seq n - (f' (newton_seq n)).symm (f (newton_seq n))

-- (i) Estimates
lemma h_inverse_bound (x : X) (hx : x ∈ ball x₀ r) :
    ‖((h' x₀ f' x).symm : X →L[ℝ] X)‖ ≤ 1 / (1 - ‖x - x₀‖ / r) := by
  have h_derivative_bound : ‖(h' x₀ f' x : X →L[ℝ] X) - (h' x₀ f' x₀ : X →L[ℝ] X)‖ ≤ ‖x - x₀‖ / r := by
    have hx_in_ball : x ∈ closedBall x₀ r := by
      exact ball_subset_closedBall hx
    have h_bound := h_bound2 x x₀ hx_in_ball (mem_closedBall_self (le_of_lt hr))
    repeat' rw [h']
    calc ‖(((f' x₀).symm : Y →L[ℝ] X).comp (f' x : X →L[ℝ] Y)) - (((f' x₀).symm : Y →L[ℝ] X).comp (f' x₀ : X →L[ℝ] Y))‖
      _ = ‖((f' x₀).symm : Y →L[ℝ] X).comp ((f' x : X →L[ℝ] Y) - (f' x₀ : X →L[ℝ] Y))‖ := by simp [sub_eq_add_neg, comp_sub]
      _ ≤ 1 / r * ‖x - x₀‖ := by apply h_bound
      _ = ‖x - x₀‖ / r := by rw [mul_comm, mul_div]; simp

  have dist_lt_one : ‖x - x₀‖ / r < 1 := by
    refine (div_lt_one hr).mpr ?_
    exact mem_ball_iff_norm.mp hx

  have h_derivative_lt_one : ‖(h' x₀ f' x : X →L[ℝ] X) - (h' x₀ f' x₀ : X →L[ℝ] X)‖ < 1 := by
    apply lt_of_lt_of_le'
    · exact dist_lt_one
    · exact h_derivative_bound

  calc ‖((h' x₀ f' x).symm : X →L[ℝ] X)‖
    _ ≤ ‖((h' x₀ f' x₀).symm : X →L[ℝ] X)‖ / (1 -
    ‖((h' x₀ f' x₀).symm : X →L[ℝ] X).comp
    ((h' x₀ f' x : X →L[ℝ] X) - (h' x₀ f' x₀ : X →L[ℝ] X))‖) := by
      apply inverse_norm_le
      rw [h'x₀_symm_eq_id]
      simp [h_derivative_lt_one]
    _ = 1 / (1 - ‖(h' x₀ f' x : X →L[ℝ] X) - (h' x₀ f' x₀ : X →L[ℝ] X)‖) := by
      simp [h'x₀_eq_id, h'x₀_symm_eq_id]
    _ ≤ 1 / (1 - ‖x - x₀‖ / r) := by
      refine one_div_le_one_div_of_le ?ha ?h
      · linarith [dist_lt_one]
      · linarith [h_derivative_bound]

lemma h_difference_bound (u v : X) (hu : u ∈ closedBall x₀ r) (hv : v ∈ closedBall x₀ r) :
    ‖h x₀ f f' u - h x₀ f f'  v - h' x₀ f' v (u - v)‖ ≤ (1 / (2 * r)) * ‖u - v‖^2 := by
sorry

-- (ii) Newton iterates properties
lemma newton_iterates_properties (k : ℕ):
    newton_seq x₀ f f' k ∈ ball x₀ r ∧
    ‖newton_seq x₀ f f' k - newton_seq x₀ f f' (k-1)‖ ≤ r / 2^k ∧
    ‖newton_seq x₀ f f' k - x₀‖ ≤ r * (1 - 1 / 2^k) ∧
    ‖((h' x₀ f' (newton_seq x₀ f f' k)).symm : X →L[ℝ] X)‖ ≤ 2^k ∧
    ‖h x₀ f f' (newton_seq x₀ f f' k)‖ ≤ r / 2^(2*k+1) := by
sorry

-- (iii) Convergence to zero
lemma newton_seq_converges :
  ∃ a, a ∈ closedBall x₀ r ∧
      Filter.Tendsto (newton_seq x₀ f f') atTop (𝓝 a) ∧
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
