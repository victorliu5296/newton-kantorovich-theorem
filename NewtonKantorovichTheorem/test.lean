import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.FundThmCalculus

section MeanValueBanach

open Set

/-- **Fundamental theorem of calculus-2** or **Mean Value Theorem** for Banach spaces: If `f : X → Y` is differentiable along the line segment
from `a` to `b`, then the change in `f` equals the integral of its derivative along this path. -/
lemma integral_eq_sub_of_hasFDerivAt
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {f : X → Y} {f' : X → X →L[ℝ] Y} {a b : X}
    (hcont : ContinuousOn (fun t : ℝ ↦
      (f' (a + t • (b - a)) : X →L[ℝ] Y)) (Set.Icc 0 1))
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasFDerivAt f (f' (a + t • (b - a)) : X →L[ℝ] Y) (a + t • (b - a))) :
    f b - f a = ∫ (t : ℝ) in (0:ℝ)..(1:ℝ),
      (f' (a + t • (b - a)) : X →L[ℝ] Y) (b - a) := by
  -- Step 1: Define the path from a to b
  let γ : ℝ → X := fun t ↦ a + t • (b - a)
  have γ_continuous (t : ℝ) : ContinuousWithinAt γ (Icc 0 1) t := by
    simp [γ]
    apply ContinuousWithinAt.add
    · exact continuousWithinAt_const
    · apply ContinuousWithinAt.smul
      · exact continuousWithinAt_id
      · exact continuousWithinAt_const
  have hint : IntervalIntegrable (fun t ↦ (f' (γ t)) (b - a))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simp only [γ]
    apply ContinuousOn.clm_apply
    · simp
      exact hcont
    · exact continuousOn_const
  have hderiv' : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (f ∘ γ) ((f' (γ t)) (b - a)) t := by
    intro t ht
    apply HasFDerivAt.comp_hasDerivAt
    · aesop
    · simpa [γ, neg_add_eq_sub] using ((hasDerivAt_const _ a).add
        ((hasDerivAt_id' t).smul_const (b - a)))
  have : ∫ (t : ℝ) in (0 : ℝ)..1, (f' (a + t • (b - a))) (b - a)
      = (f ∘ γ) 1 - (f ∘ γ) 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    · exact zero_le_one' ℝ
    · intro x hx
      exact ContinuousAt.comp_continuousWithinAt
        (HasFDerivAt.continuousAt (hderiv x hx)) (γ_continuous x)
    · intro x hx
      dsimp [γ] at hderiv'
      dsimp [γ]
      have hx' : x ∈ uIcc 0 1 := by
        simp only [zero_le_one, uIcc_of_le, mem_Icc]
        simp only [mem_Ioo] at hx
        constructor
        · linarith [hx.left]
        · linarith [hx.right]
      exact HasDerivAt.hasDerivWithinAt (hderiv' x hx')
    · exact hint
  have : ∫ (t : ℝ) in (0 : ℝ)..1, (f' (a + t • (b - a))) (b - a)
    = f b - f a := by aesop
  exact _root_.id (Eq.symm this)

end MeanValueBanach

section NewtonKantorovich1Constant

open Set Topology Metric ContinuousLinearMap


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
variable (h_subset : closedBall x₀ r ⊆ Ω)
variable (h_bound1 : ‖(f' x₀).symm (f x₀)‖ ≤ r / 2)
variable (h_bound2 : ∀ (u v : X), u ∈ closedBall x₀ r → v ∈ closedBall x₀ r →
  ‖((f' x₀).symm : Y →L[ℝ] X).comp ((f' u : X →L[ℝ] Y) - (f' v : X →L[ℝ] Y))‖
   ≤ (1 / r) * ‖u - v‖)

lemma h_difference_bound (ha : a ∈ closedBall x₀ r)
    (hb : b ∈ closedBall x₀ r) :
    ‖h x₀ f f' b - h x₀ f f' a - h'_clm x₀ f' a (b - a)‖
    ≤ (1 / (2 * r)) * ‖b - a‖^2 := by
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

  calc ‖h x₀ f f' b - h x₀ f f' a - h'_clm x₀ f' a (b - a)‖
    _ = ‖∫ (t : ℝ) in (0 : ℝ)..(1 : ℝ),
        (h'_clm x₀ f' (a + t • (b - a)) - h'_clm x₀ f' a) (b - a)‖ := by
      rw [integral_eq_sub_of_hasFDerivAt
        (h'_cont_a_b
          hab hΩ (h_contDiffOn Ω x₀ f hf f') (h'_deriv Ω x₀ f f' hf'))
        (h'_ab_deriv Ω x₀ f f' hf' a b hab)]
      simp only [coe_sub', Pi.sub_apply]
      rw [intervalIntegral.integral_sub]
      simp
      · exact integrable_h'a_t_smul_b_sub_a_at_b_sub_a
      · exact ContinuousOn.intervalIntegrable continuousOn_const
    _ ≤ ∫ (t : ℝ) in Ι (0 : ℝ) (1 :ℝ),
        ‖(h'_clm x₀ f' (a + t • (b - a)) - h'_clm x₀ f' a) (b - a)‖ := by
      -- apply intervalIntegral.norm_integral_le_abs_integral_norm
      exact intervalIntegral.norm_integral_le_integral_norm_Ioc
    _ = ∫ (t : ℝ) in (0 : ℝ)..(1 : ℝ),
        ‖(h'_clm x₀ f' (a + t • (b - a)) - h'_clm x₀ f' a) (b - a)‖ := by
      rw [intervalIntegral.integral_of_le]
      · simp
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
    _ ≤ (∫ (t : ℝ) in (0 : ℝ)..(1 : ℝ), 1 / r * ‖a + t • (b - a) - a‖) * ‖b - a‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg (b - a))
      apply intervalIntegral.integral_mono_on (zero_le_one' ℝ)
      · exact integrable_norm_h'a_t_smul_b_sub_a_sub_h'a
      · simp
        apply IntervalIntegrable.const_mul
        apply IntervalIntegrable.norm
        -- apply IntervalIntegrable.smul -- this line appears problematic

end NewtonKantorovich1Constant
