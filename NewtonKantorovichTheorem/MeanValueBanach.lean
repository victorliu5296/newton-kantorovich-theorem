import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.FundThmCalculus

open Set

section MeanValueBanach

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
