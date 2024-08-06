import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals
import NewtonKantorovichTheorem.MeanValueBanach
import NewtonKantorovichTheorem.CLMBound

open Set Topology Metric ContinuousLinearMap Filter

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
      ((h'_clm x₀ f') (a + t • (b - a)) : X →L[ℝ] X)) (Icc 0 1) :=
  f'_cont_a_b Ω hΩ (h x₀ f f') hh_contDiffOn (h' x₀ f') hh' a b hab

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

lemma hx₀_bound : ‖h x₀ f f' x₀‖ ≤ r / 2 := assumption_bound1

lemma h'_sub_bound (u v : X) (hu : u ∈ closedBall x₀ r) (hv : v ∈ closedBall x₀ r) :
    ‖h'_clm x₀ f' u - h'_clm x₀ f' v‖ ≤ ‖u - v‖ / r := by
  dsimp [h'_clm, h']
  convert assumption_bound2 u v hu hv
  repeat' rw [← ContinuousLinearEquiv.comp_coe]
  exact Eq.symm (comp_sub (f' x₀).symm.toContinuousLinearMap
    (f' u).toContinuousLinearMap (f' v).toContinuousLinearMap)

-- (i) Estimates
lemma h'_inverse_bound (x : X) (hx : x ∈ ball x₀ r) :
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

lemma h_h'_difference_bound (ha : a ∈ closedBall x₀ r)
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
      (fun _ ↦ (h'_clm x₀ f' a) (b - a)) MeasureTheory.volume 0 1 := by
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
      · intro t _
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

-- Newton iteration sequence
noncomputable def newton_step (x : X) : X := (f' x).symm (f x)
noncomputable def newton_step_h (x : X) : X := (h' x₀ f' x).symm (h x₀ f f' x)

lemma newton_step_equiv : newton_step f f' = newton_step_h x₀ f f' := by
  ext x
  unfold newton_step newton_step_h
  unfold h h'
  simp

noncomputable def newton_seq : ℕ → X
| 0       => x₀
| (n + 1) => newton_seq n - newton_step_h x₀ f f' (newton_seq n)

-- (ii) Newton iterates properties
lemma newton_iterates_properties (k : ℕ):
    newton_seq x₀ f f' k ∈ ball x₀ r ∧
    ‖newton_seq x₀ f f' k - newton_seq x₀ f f' (k - 1)‖ ≤ r / 2 ^ k ∧
    ‖newton_seq x₀ f f' k - x₀‖ ≤ r * (1 - 1 / 2 ^ k) ∧
    ‖((h' x₀ f' (newton_seq x₀ f f' k)).symm : X →L[ℝ] X)‖ ≤ 2 ^ k ∧
    ‖h x₀ f f' (newton_seq x₀ f f' k)‖ ≤ r / 2 ^ (2 * k + 1) := by
  induction k with
  | zero =>
    -- Base case: k = 0
    repeat' constructor
    · show newton_seq x₀ f f' 0 ∈ ball x₀ r
      exact mem_ball_self hr
    · show ‖newton_seq x₀ f f' 0 - newton_seq x₀ f f' (0 - 1)‖ ≤ r / 2 ^ 0
      unfold newton_seq
      simp only [sub_self, norm_zero, pow_zero, div_one]
      linarith
    · show ‖newton_seq x₀ f f' 0 - x₀‖ ≤ r * (1 - 1 / 2 ^ 0)
      unfold newton_seq
      simp
    · show ‖((h' x₀ f' (newton_seq x₀ f f' 0)).symm : X →L[ℝ] X)‖ ≤ 2^0
      unfold newton_seq h'
      have : (f' x₀).trans (f' x₀).symm = ContinuousLinearEquiv.refl ℝ X := by
        ext
        simp
      simp [this, ContinuousLinearEquiv.refl_symm]
    · show ‖h x₀ f f' (newton_seq x₀ f f' 0)‖ ≤ r / 2 ^ (2 * 0 + 1)
      unfold newton_seq h
      simp
      exact assumption_bound1
  | succ k ih =>
    -- Inductive step
    have ih_ball := ih.1
    have ih_dist := ih.2.2.1
    have ih_inverse := ih.2.2.2.1
    have ih_h := ih.2.2.2.2

    -- Prove each property for k+1
    have diff_k_plus_1 : ‖newton_seq x₀ f f' (k + 1) - newton_seq x₀ f f' k‖ ≤ r / 2 ^ (k + 1) := by
      calc ‖newton_seq x₀ f f' (k + 1) - newton_seq x₀ f f' k‖
        _ = ‖((h' x₀ f' (newton_seq x₀ f f' k)).symm : X →L[ℝ] X)
            (h x₀ f f' (newton_seq x₀ f f' k))‖ := by
          rw [newton_seq]
          simp
          rw [newton_step_h]
        _ ≤ ‖((h' x₀ f' (newton_seq x₀ f f' k)).symm : X →L[ℝ] X)‖
            * ‖h x₀ f f' (newton_seq x₀ f f' k)‖ := le_opNorm
            ((h' x₀ f' (newton_seq x₀ f f' k)).symm : X →L[ℝ] X)
            (h x₀ f f' (newton_seq x₀ f f' k))
        _ ≤ (2 ^ k) * (r / 2 ^ (2 * k + 1)) := by
          apply mul_le_mul ih_inverse ih_h
          · exact norm_nonneg (h x₀ f f' (newton_seq x₀ f f' k))
          · norm_num
        _ = r / 2 ^ (k + 1) := by
          field_simp
          ring

    have ball_k_plus_one : newton_seq x₀ f f' (k + 1) ∈ ball x₀ r := by
      rw [newton_seq]
      have dist_triangle : ‖(newton_seq x₀ f f' k
          - newton_step_h x₀ f f' (newton_seq x₀ f f' k)) - x₀‖
            ≤ ‖newton_seq x₀ f f' k - x₀‖
            + ‖newton_step_h x₀ f f' (newton_seq x₀ f f' k)‖ := by
        have rewrite_eq : (newton_seq x₀ f f' k
            - newton_step_h x₀ f f' (newton_seq x₀ f f' k)) - x₀
              = (newton_seq x₀ f f' k - x₀)
              - newton_step_h x₀ f f' (newton_seq x₀ f f' k) := by
          abel
        rw [rewrite_eq]
        exact
          norm_sub_le (newton_seq x₀ f f' k - x₀)
            (newton_step_h x₀ f f' (newton_seq x₀ f f' k))
      simp only [mem_ball, dist_sub_eq_dist_add_left, gt_iff_lt]
      rw [dist_eq_norm]
      simp only [mem_ball] at ih_ball
      -- Use the induction hypothesis for the first term
      have ih_dist_bound : ‖newton_seq x₀ f f' k - x₀‖
          ≤ r * (1 - 1 / 2^k) := ih_dist
      -- For the second term, we can use the property of newton_step_h
      have newton_step_bound : ‖newton_step_h x₀ f f' (newton_seq x₀ f f' k)‖
          ≤ r / 2 ^ (k + 1) := by
        have : newton_step_h x₀ f f' (newton_seq x₀ f f' k)
            = - (newton_seq x₀ f f' (k + 1) - newton_seq x₀ f f' k) := by
          rw [newton_seq]
          simp
        rw [this, norm_neg]
        exact diff_k_plus_1

      calc ‖newton_seq x₀ f f' k - (x₀ + newton_step_h x₀ f f' (newton_seq x₀ f f' k))‖
        _ = ‖(newton_seq x₀ f f' k)
              - newton_step_h x₀ f f' (newton_seq x₀ f f' k) - x₀‖ := by abel_nf
        _ ≤ ‖newton_seq x₀ f f' k - x₀‖ + ‖newton_step_h x₀ f f' (newton_seq x₀ f f' k)‖ := dist_triangle
        _ ≤ r * (1 - 1 / 2 ^ k) + r / 2 ^ (k + 1) := by linarith [ih_dist_bound, newton_step_bound]
        _ < r := by
          have : r * (1 - 1 / 2 ^ k) + r / 2 ^ (k + 1)
              = r * (1 - 1 / 2 ^ (k + 1)) := by ring
          rw [this]
          nth_rw 2 [← mul_one r]
          apply mul_lt_mul_of_pos_left _ hr
          simp only [one_div, sub_lt_self_iff, inv_pos, Nat.ofNat_pos, pow_pos]

    have dist_k_plus_one : ‖newton_seq x₀ f f' (k + 1) - x₀‖
        ≤ r * (1 - 1 / 2 ^ (k + 1)) := by
      calc ‖newton_seq x₀ f f' (k + 1) - x₀‖
        _ = ‖(newton_seq x₀ f f' k
            - newton_step_h x₀ f f' (newton_seq x₀ f f' k)) - x₀‖ := by
          rw [newton_seq]
        _ ≤ ‖newton_seq x₀ f f' k - x₀‖
            + ‖newton_step_h x₀ f f' (newton_seq x₀ f f' k)‖ := by
          rw [sub_right_comm]
          exact
            norm_sub_le (newton_seq x₀ f f' k - x₀)
              (newton_step_h x₀ f f' (newton_seq x₀ f f' k))
        _ = ‖newton_seq x₀ f f' k - x₀‖
            + ‖newton_seq x₀ f f' (k + 1) - newton_seq x₀ f f' k‖ := by
          rw [newton_seq]
          simp only [sub_sub_cancel_left, norm_neg]
        _ ≤ r * (1 - 1 / 2 ^ k) + r / 2 ^ (k + 1) := by
          exact add_le_add ih_dist diff_k_plus_1
        _ = r * (1 - 1 / 2 ^ (k + 1)) := by
          field_simp
          ring
    repeat' constructor
    · show newton_seq x₀ f f' (k + 1) ∈ ball x₀ r
      exact ball_k_plus_one
    · show ‖newton_seq x₀ f f' (k + 1) - newton_seq x₀ f f' k‖ ≤ r / 2 ^ (k + 1)
      exact diff_k_plus_1
    · show ‖newton_seq x₀ f f' (k + 1) - x₀‖ ≤ r * (1 - 1 / 2 ^ (k + 1))
      exact dist_k_plus_one
    · show ‖((h' x₀ f' (newton_seq x₀ f f' (k + 1))).symm : X →L[ℝ] X)‖
        ≤ 2 ^ (k + 1)
      apply le_trans
      apply h'_inverse_bound x₀ f' r hr assumption_bound2
        (newton_seq x₀ f f' (k + 1))
      · exact ball_k_plus_one
      · rw [← one_div_one_div (2 ^ (k + 1) : ℝ)]
        apply one_div_le_one_div_of_le (by norm_num)
        rw [le_sub_comm, div_le_iff hr, mul_comm]
        exact dist_k_plus_one
    · show ‖h x₀ f f' (newton_seq x₀ f f' (k + 1))‖ ≤ r / 2 ^ (2 * (k + 1) + 1)
      have : ‖h x₀ f f' (newton_seq x₀ f f' (k + 1))‖
          = ‖(h x₀ f f' (newton_seq x₀ f f' (k + 1)))
              - h x₀ f f' (newton_seq x₀ f f' k)
              - h' x₀ f' (newton_seq x₀ f f' k)
              (newton_seq x₀ f f' (k + 1) - newton_seq x₀ f f' k)‖ := by
        congr
        rw [sub_sub, sub_eq_add_neg]
        apply self_eq_add_right.mpr
        rw [newton_seq]
        unfold newton_step_h
        simp
      rw [this]
      have line_in_domain :
          ∀ t ∈ Icc (0 : ℝ) 1, ((newton_seq x₀ f f' k)
          + t • (newton_seq x₀ f f' (k + 1) - newton_seq x₀ f f' k)) ∈ Ω := by
        intro t ht
        have hk_in_ball : newton_seq x₀ f f' k ∈ ball x₀ r := ih_ball
        have hk1_in_ball : newton_seq x₀ f f' (k + 1) ∈ ball x₀ r := ball_k_plus_one
        have linear_combination_form : newton_seq x₀ f f' k
            + t • (newton_seq x₀ f f' (k + 1) - newton_seq x₀ f f' k)
            = (1 - t) • newton_seq x₀ f f' k + t • (newton_seq x₀ f f' (k + 1)) := by
          rw [newton_seq]
          simp only [sub_smul, one_smul, smul_sub]
          abel_nf
        have convex_in_ball : ((newton_seq x₀ f f' k)
            + t • (newton_seq x₀ f f' (k + 1) - newton_seq x₀ f f' k)) ∈ ball x₀ r := by
          rw [linear_combination_form]
          simp only [mem_Icc] at ht
          apply convex_ball
          · exact hk_in_ball
          · exact hk1_in_ball
          · linarith [ht.1]
          · linarith
          · norm_num
        have ball_subset_domain : ball x₀ r ⊆ Ω :=
          Subset.trans ball_subset_closedBall assumption_subset
        exact ball_subset_domain convex_in_ball
      apply le_trans
      apply h_h'_difference_bound Ω hΩ x₀ f hf f' hf'
        (newton_seq x₀ f f' k) (newton_seq x₀ f f' (k + 1))
        line_in_domain r hr assumption_bound2
      · exact mem_of_mem_of_subset ih_ball ball_subset_closedBall
      · exact mem_of_mem_of_subset ball_k_plus_one ball_subset_closedBall
      · have : ‖newton_seq x₀ f f' (k + 1) - newton_seq x₀ f f' k‖ ^ 2 / (2 * r)
            ≤ (r / 2 ^ (k + 1)) ^ 2 / (2 * r) := by
          apply (div_le_div_right (by linarith)).mpr
          rw [pow_two, pow_two]
          apply mul_self_le_mul_self (by norm_num)
          exact diff_k_plus_1
        apply le_of_le_of_eq this
        field_simp
        ring

-- (iii) Convergence to zero
lemma newton_seq_converges :
    ∃ a_zero, a_zero ∈ closedBall x₀ r ∧
    Tendsto (newton_seq x₀ f f') atTop (𝓝 a_zero) ∧
    f a_zero = 0 ∧
    ∀ k, ‖newton_seq x₀ f f' k - a_zero‖ ≤ r / 2^k := by
  -- Prove that (xₖ) is a Cauchy sequence
  have cauchy_seq : CauchySeq (newton_seq x₀ f f') := by
    apply cauchySeq_of_le_geometric (1 / 2) (r / 2)
    · linarith
    · intro n
      rw [dist_eq_norm, ← norm_neg]
      field_simp
      nth_rw 1 [← pow_one 2]
      rw [← pow_add, add_comm 1 n]
      have := (newton_iterates_properties
        Ω hΩ x₀ f hf f' hf' r hr assumption_subset
        assumption_bound1 assumption_bound2 (n + 1)).2.1
      simp at this
      exact this

  -- Since xₖ ∈ B(x₀; r) ⊆ B̄(x₀; r) and B̄(x₀; r) is complete
  have complete_space : CompleteSpace (closedBall x₀ r) :=
    IsClosed.completeSpace_coe isClosed_ball

  -- Use the completeness to obtain the limit point a
  obtain ⟨a_zero, ha_tendsto⟩ : ∃ a, Tendsto (newton_seq x₀ f f') atTop (𝓝 a) :=
    cauchySeq_tendsto_of_complete cauchy_seq

  -- Show that a ∈ closedBall x₀ r
  have ha_in_ball : a_zero ∈ closedBall x₀ r := by
    apply isClosed_ball.mem_of_tendsto ha_tendsto
    apply eventually_of_forall
    intro n
    have in_open_ball := (newton_iterates_properties
              Ω hΩ x₀ f hf f' hf' r hr assumption_subset
              assumption_bound1 assumption_bound2 n).1
    apply ball_subset_closedBall
    exact in_open_ball

  -- Show that h(a) = 0
  have h_lim : Tendsto (h x₀ f f' ∘ newton_seq x₀ f f') atTop (𝓝 0) := by
    have zero_tendsto_zero : Tendsto (fun (k : ℕ) ↦ (0 : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds
    have zero_le_norm : (fun (k : ℕ) ↦ (0 : ℝ))
        ≤ (fun (k : ℕ) ↦ ‖(h x₀ f f' ∘ newton_seq x₀ f f') k‖) := by
      intro k
      simp
    have le_bound : (fun (k : ℕ) ↦ ‖(h x₀ f f' ∘ newton_seq x₀ f f') k‖)
        ≤ fun (k : ℕ) ↦ r / 2 ^ (2 * k + 1) := by
      intro k
      exact (newton_iterates_properties
        Ω hΩ x₀ f hf f' hf' r hr assumption_subset
        assumption_bound1 assumption_bound2 k).2.2.2.2
    have bound_vanishes : Tendsto (fun k ↦ r / 2 ^ (2 * k + 1)) atTop (𝓝 0) := by
      have (k : ℕ) : r / 2 ^ (2 * k + 1) = r * (1 / 2) ^ ((2 * k + 1) : ℤ) := by
        field_simp
        left
        rfl
      simp only [this]
      have geom_vanishes : Tendsto (fun k ↦ (1 / 2 : ℝ) ^ (2 * k + 1)) atTop (𝓝 0) := by
        have zero_le_geom : (fun (k : ℕ) ↦ (0 : ℝ))
            ≤ (fun (k : ℕ) ↦ (1 / 2 : ℝ) ^ (2 * k + 1)) := by
          intro k
          field_simp
          norm_num
        have geom_tendsto_zero : Tendsto (fun k ↦ (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
          have one_half_lt_one : |(1 / 2 : ℝ)| < 1 := by
            rw [abs_of_nonneg (by linarith)]
            linarith
          exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one one_half_lt_one
        have le_geom : (fun (k : ℕ) ↦ (1 / 2 : ℝ) ^ (2 * k + 1))
            ≤ (fun (k : ℕ) ↦ (1 / 2 : ℝ) ^ k) := by
          intro k
          field_simp
          exact one_div_pow_le_one_div_pow_of_le (by norm_num) (by linarith)
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le
          zero_tendsto_zero geom_tendsto_zero zero_le_geom le_geom
      rw [← mul_zero r]
      exact Tendsto.const_mul r geom_vanishes
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      zero_tendsto_zero bound_vanishes zero_le_norm le_bound

  have ha_eq_zero : h x₀ f f' a_zero = 0 := by
    have newton_iterates_in_ball (k : ℕ) := (newton_iterates_properties
      Ω hΩ x₀ f hf f' hf' r hr assumption_subset
      assumption_bound1 assumption_bound2 k).1
    have h_continuousAt_a : ContinuousAt (h x₀ f f') a_zero := by
      apply ((h_contDiffOn Ω x₀ f hf f').continuousOn.continuousWithinAt
        (assumption_subset ha_in_ball)).continuousAt
      exact IsOpen.mem_nhds hΩ (assumption_subset ha_in_ball)
    apply Eq.symm
    apply tendsto_nhds_unique h_lim
    exact Tendsto.comp h_continuousAt_a ha_tendsto

  -- Show that f(a) = 0
  have fa_eq_zero : f a_zero = 0 := by
    unfold h at ha_eq_zero
    exact (LinearEquiv.map_eq_zero_iff (f' x₀).symm.toLinearEquiv).mp ha_eq_zero

  -- Show that the distance at the k-th iteration is bounded by r / 2^k
  have dist_k_le_r : ∀ k, ‖newton_seq x₀ f f' k - a_zero‖ ≤ r / 2^k := by
    sorry

  exact ⟨a_zero, ha_in_ball, ha_tendsto, fa_eq_zero, dist_k_le_r⟩

-- (iv) Uniqueness of zero
lemma zero_unique (a₁ a₂ : X)
    (ha : a₁ ∈ closedBall x₀ r) (hb : a₂ ∈ closedBall x₀ r)
    (hfa : f a₁ = 0) (hfb : f a₂ = 0) : a₁ = a₂ := by
  sorry

theorem newton_kantorovich_1_const :
    (∀ k : Nat, (newton_seq x₀ f f' k) ∈ closedBall x₀ r) ∧
    (∃! a ∈ closedBall x₀ r, f a = 0 ∧ ∀ k : Nat, ‖newton_seq x₀ f f' k - a‖ ≤ r / 2^k) := by
  sorry

end NewtonKantorovich1Constant
