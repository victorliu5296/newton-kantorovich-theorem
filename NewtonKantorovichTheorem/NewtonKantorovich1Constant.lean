import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals
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

lemma h'_ab_deriv : ∀ (t : ℝ), t ∈ Icc 0 1 → HasFDerivAt
    (h x₀ f f') (h'_clm x₀ f' (a + t • (b - a))) (a + t • (b - a)) := by
  intro t ht
  exact h'_deriv Ω x₀ f f' hf' (a + t • (b - a)) (hab t ht)

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
      ((h'_clm x₀ f') (a + t • (b - a)) : X →L[ℝ] X)) (Icc 0 1) := by
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
variable (assumption_subset : closedBall x₀ r ⊆ Ω)
variable (assumption_bound1 : ‖(f' x₀).symm (f x₀)‖ ≤ r / 2)
variable (assumption_bound2 : ∀ (u v : X), u ∈ closedBall x₀ r → v ∈ closedBall x₀ r →
  ‖((f' x₀).symm : Y →L[ℝ] X).comp ((f' u : X →L[ℝ] Y) - (f' v : X →L[ℝ] Y))‖
    ≤ ‖u - v‖ / r)

-- Newton iteration sequence
noncomputable def newton_seq : Nat → X
| 0       => x₀
| (n + 1) => newton_seq n - (f' (newton_seq n)).symm (f (newton_seq n))

lemma hx₀_bound : ‖h x₀ f f' x₀‖ ≤ r / 2 := assumption_bound1

lemma h'_sub_bound (u v : X) (hu : u ∈ closedBall x₀ r) (hv : v ∈ closedBall x₀ r) :
    ‖h'_clm x₀ f' u - h'_clm x₀ f' v‖ ≤ ‖u - v‖ / r := by
  dsimp [h'_clm, h']
  convert assumption_bound2 u v hu hv
  repeat' rw [← ContinuousLinearEquiv.comp_coe]
  exact Eq.symm (comp_sub (f' x₀).symm.toContinuousLinearMap
    (f' u).toContinuousLinearMap (f' v).toContinuousLinearMap)

-- (i) Estimates
lemma h_inverse_bound (x : X) (hx : x ∈ ball x₀ r) :
    ‖((h' x₀ f' x).symm : X →L[ℝ] X)‖ ≤ 1 / (1 - ‖x - x₀‖ / r) := by
  have h_derivative_bound :
      ‖(h' x₀ f' x : X →L[ℝ] X) - (h' x₀ f' x₀ : X →L[ℝ] X)‖
      ≤ ‖x - x₀‖ / r := by
    have hx_in_ball : x ∈ closedBall x₀ r := by
      exact ball_subset_closedBall hx
    have h_bound := assumption_bound2 x x₀ hx_in_ball (mem_closedBall_self (le_of_lt hr))
    repeat' rw [h']
    calc ‖(((f' x₀).symm : Y →L[ℝ] X).comp (f' x : X →L[ℝ] Y))
          - (((f' x₀).symm : Y →L[ℝ] X).comp (f' x₀ : X →L[ℝ] Y))‖
      _ = ‖((f' x₀).symm : Y →L[ℝ] X).comp ((f' x : X →L[ℝ] Y)
          - (f' x₀ : X →L[ℝ] Y))‖ := by simp [sub_eq_add_neg, comp_sub]
      _ ≤ ‖x - x₀‖ / r := h_bound

  have dist_lt_one : ‖x - x₀‖ / r < 1 := by
    refine (div_lt_one hr).mpr ?_
    exact mem_ball_iff_norm.mp hx

  have h_derivative_lt_one :
      ‖(h' x₀ f' x : X →L[ℝ] X) - (h' x₀ f' x₀ : X →L[ℝ] X)‖ < 1 := by
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

lemma h_difference_bound (ha : a ∈ closedBall x₀ r)
    (hb : b ∈ closedBall x₀ r) :
    ‖h x₀ f f' b - h x₀ f f' a - h'_clm x₀ f' a (b - a)‖
    ≤ ‖b - a‖ ^ 2 / (2 * r) := by
  have integrable_h'a_t_smul_b_sub_a_at_b_sub_a : IntervalIntegrable
      (fun t ↦ (h'_clm x₀ f' (a + t • (b - a))) (b - a))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.clm_apply _ continuousOn_const
    · simp only [zero_le_one, uIcc_of_le]
      exact h'_cont_a_b hab hΩ (h_contDiffOn Ω x₀ f hf f')
        (h'_deriv Ω x₀ f f' hf')

  have integrable_h'a_b_sub_a : IntervalIntegrable
      (fun t ↦ (h'_clm x₀ f' a) (b - a)) MeasureTheory.volume 0 1 := by
    exact ContinuousOn.intervalIntegrable continuousOn_const

  have integrable_h'a_t_smul_b_sub_a_sub_h'a_at_b_sub_a : IntervalIntegrable
    (fun t ↦ (h'_clm x₀ f' (a + t • (b - a)) - h'_clm x₀ f' a) (b - a))
    MeasureTheory.volume 0 1 := by
    exact IntervalIntegrable.sub
      integrable_h'a_t_smul_b_sub_a_at_b_sub_a integrable_h'a_b_sub_a

  have integrable_norm_h'a_t_smul_b_sub_a_sub_h'a : IntervalIntegrable
      (fun x ↦ ‖h'_clm x₀ f' (a + x • (b - a)) - h'_clm x₀ f' a‖)
      MeasureTheory.volume 0 1 := by
    apply IntervalIntegrable.norm
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.sub
    · simp only [zero_le_one, uIcc_of_le]
      exact h'_cont_a_b hab hΩ (h_contDiffOn Ω x₀ f hf f') (h'_deriv Ω x₀ f f' hf')
    · simp only [zero_le_one, uIcc_of_le]
      exact continuousOn_const

  have smul_integrable : IntervalIntegrable
    (fun x ↦ ‖x • (b - a)‖) MeasureTheory.volume 0 1 := by
      apply IntervalIntegrable.norm
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.smul
      · exact continuousOn_id
      · exact continuousOn_const

  calc ‖h x₀ f f' b - h x₀ f f' a - h'_clm x₀ f' a (b - a)‖
    _ = ‖∫ (t : ℝ) in (0 : ℝ)..(1 : ℝ),
        (h'_clm x₀ f' (a + t • (b - a)) - h'_clm x₀ f' a) (b - a)‖ := by
      rw [integral_eq_sub_of_hasFDerivAt
        (h'_cont_a_b
          hab hΩ (h_contDiffOn Ω x₀ f hf f') (h'_deriv Ω x₀ f f' hf'))
        (h'_ab_deriv Ω x₀ f f' hf' a b hab)]
      simp only [coe_sub', Pi.sub_apply]
      rw [intervalIntegral.integral_sub]
      simp only [map_sub, intervalIntegrable_const, intervalIntegral.integral_sub,
        intervalIntegral.integral_const, sub_zero, one_smul]
      · exact integrable_h'a_t_smul_b_sub_a_at_b_sub_a
      · exact ContinuousOn.intervalIntegrable continuousOn_const
    _ ≤ ∫ (t : ℝ) in Ι (0 : ℝ) (1 :ℝ),
        ‖(h'_clm x₀ f' (a + t • (b - a)) - h'_clm x₀ f' a) (b - a)‖ := by
      -- apply intervalIntegral.norm_integral_le_abs_integral_norm
      exact intervalIntegral.norm_integral_le_integral_norm_Ioc
    _ = ∫ (t : ℝ) in (0 : ℝ)..(1 : ℝ),
        ‖(h'_clm x₀ f' (a + t • (b - a)) - h'_clm x₀ f' a) (b - a)‖ := by
      rw [intervalIntegral.integral_of_le]
      · simp only [zero_le_one, uIoc_of_le, map_sub, coe_sub', Pi.sub_apply]
      · exact zero_le_one' ℝ
    _ ≤ ∫ (t : ℝ) in (0 : ℝ)..(1 : ℝ),
        ‖h'_clm x₀ f' (a + t • (b - a)) - h'_clm x₀ f' a‖ * ‖b - a‖  := by
      apply intervalIntegral.integral_mono_on (zero_le_one' ℝ)
      · exact IntervalIntegrable.norm integrable_h'a_t_smul_b_sub_a_sub_h'a_at_b_sub_a
      · apply IntervalIntegrable.mul_const
        exact integrable_norm_h'a_t_smul_b_sub_a_sub_h'a
      · intro t ht
        exact le_opNorm (h'_clm x₀ f' (a + t • (b - a)) - h'_clm x₀ f' a) (b - a)
    _ = (∫ (t : ℝ) in (0 : ℝ)..(1 : ℝ),
        ‖h'_clm x₀ f' (a + t • (b - a)) - h'_clm x₀ f' a‖) * ‖b - a‖ := by
      exact
        intervalIntegral.integral_mul_const ‖b - a‖ fun x ↦
          ‖h'_clm x₀ f' (a + x • (b - a)) - h'_clm x₀ f' a‖
    _ ≤ (∫ (t : ℝ) in (0 : ℝ)..(1 : ℝ), ‖a + t • (b - a) - a‖ / r) * ‖b - a‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg (b - a))
      apply intervalIntegral.integral_mono_on (zero_le_one' ℝ)
      · exact integrable_norm_h'a_t_smul_b_sub_a_sub_h'a
      · simp only [add_sub_cancel_left]
        apply IntervalIntegrable.div_const
        exact smul_integrable
      · intro t ht
        have : (a + t • (b - a)) ∈ closedBall x₀ r := by
          simp at ht
          have tnonneg : 0 ≤ t := by
            exact ht.1
          have one_sub_t_nonneg : 0 ≤ 1 - t := by
            linarith [ht.2]
          have reorganize : ‖a + t • (b - a) - x₀‖ =
              ‖(1 - t) • (a - x₀) + t • (b - x₀)‖ := by
            congr
            simp [smul_sub, sub_smul]
            abel
          have triangle_inequality : ‖(1 - t) • (a - x₀) + t • (b - x₀)‖ ≤ (1 - t) * ‖a - x₀‖ + t * ‖b - x₀‖ := by
            have triangle_ineq := norm_add_le ((1 - t) • (a - x₀)) (t • (b - x₀))
            have : ‖(1 - t) • (a - x₀)‖ + ‖t • (b - x₀)‖ = (1 - t) * ‖a - x₀‖ + t * ‖b - x₀‖ := by
              rw [norm_smul_of_nonneg, norm_smul_of_nonneg]
              · exact tnonneg
              · exact one_sub_t_nonneg
            exact le_of_le_of_eq triangle_ineq this
          have a_dist : ‖a - x₀‖ ≤ r := mem_closedBall_iff_norm.mp ha
          have b_dist : ‖b - x₀‖ ≤ r := mem_closedBall_iff_norm.mp hb
          have : (1 - t) * ‖a - x₀‖ ≤ (1 - t) * r :=
            mul_le_mul_of_nonneg_left a_dist one_sub_t_nonneg
          have : t * ‖b - x₀‖ ≤ t * r :=
            mul_le_mul_of_nonneg_left b_dist tnonneg
          have : (1 - t) * r + t * r = r := by ring
          simp
          rw [dist_eq_norm_sub]
          rw [reorganize]
          apply le_trans triangle_inequality
          rw [← this]
          linarith
        exact h'_sub_bound x₀ f' r assumption_bound2 (a + t • (b - a)) a this ha
    _ = (∫ (t : ℝ) in (0 : ℝ)..(1 : ℝ), ‖t • (b - a)‖ / r) * ‖b - a‖ := by simp
    _ = (∫ (t : ℝ) in (0 : ℝ)..(1 : ℝ), ‖t • (b - a)‖) * ‖b - a‖ / r := by field_simp
    _ = (∫ (t : ℝ) in (0 : ℝ)..(1 : ℝ), t * ‖b - a‖) * ‖b - a‖ / r := by
      congr 2
      apply intervalIntegral.integral_congr
      intro t ht
      apply norm_smul_of_nonneg _ (b - a)
      simp only [zero_le_one, uIcc_of_le, mem_Icc] at ht
      exact ht.1
    _ = (∫ (t : ℝ) in (0 : ℝ)..(1 : ℝ), t) * ‖b - a‖ ^ 2 / r := by
      field_simp
      rw [pow_two]
    _ = ‖b - a‖ ^ 2 / (2 * r) := by
      have : (∫ (t : ℝ) in (0 : ℝ)..(1 : ℝ), t) = 1 / 2 := by simp
      field_simp

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
