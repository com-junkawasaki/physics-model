import PhysicsModel.Chirality
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp

/-! # One-loop running coupling and renormalization-group flow

Using logarithmic scale time `t = log (μ/μ₀)`, the one-loop equation is
`d(1/g²)/dt = b`.  Its exact affine inverse-coupling solution yields the usual
asymptotic-freedom and Landau-pole alternatives according to the sign of `b`.
-/

namespace PhysicsModel.RunningCoupling

/-- Exact one-loop inverse squared coupling. -/
def inverseCouplingSq (initialInverse betaCoefficient scaleTime : ℝ) : ℝ :=
  initialInverse + betaCoefficient * scaleTime

/-- Exact squared coupling wherever the inverse coupling is nonzero. -/
noncomputable def couplingSq (initialInverse betaCoefficient scaleTime : ℝ) : ℝ :=
  (inverseCouplingSq initialInverse betaCoefficient scaleTime)⁻¹

@[simp] theorem inverseCouplingSq_at_reference (initialInverse betaCoefficient : ℝ) :
    inverseCouplingSq initialInverse betaCoefficient 0 = initialInverse := by
  simp [inverseCouplingSq]

theorem couplingSq_at_reference (initialInverse betaCoefficient : ℝ) :
    couplingSq initialInverse betaCoefficient 0 = 1 / initialInverse := by
  simp [couplingSq, inverseCouplingSq, one_div]

/-- The inverse coupling solves its one-loop RG equation exactly. -/
theorem inverseCouplingSq_hasDerivAt (initialInverse betaCoefficient scaleTime : ℝ) :
    HasDerivAt (inverseCouplingSq initialInverse betaCoefficient)
      betaCoefficient scaleTime := by
  unfold inverseCouplingSq
  apply (hasDerivAt_const_add_iff initialInverse).2
  simpa only [id_eq, mul_one] using
    ((hasDerivAt_id scaleTime).const_mul betaCoefficient)

/-- Equivalent beta function for the squared coupling: `d g²/dt = -b g⁴`. -/
theorem couplingSq_hasDerivAt {initialInverse betaCoefficient scaleTime : ℝ}
    (regular : inverseCouplingSq initialInverse betaCoefficient scaleTime ≠ 0) :
    HasDerivAt (couplingSq initialInverse betaCoefficient)
      (-betaCoefficient * (couplingSq initialInverse betaCoefficient scaleTime) ^ 2)
      scaleTime := by
  have h := (inverseCouplingSq_hasDerivAt initialInverse betaCoefficient scaleTime).inv regular
  unfold couplingSq
  convert h using 1
  field_simp

theorem couplingSq_positive {initialInverse betaCoefficient scaleTime : ℝ}
    (positive : 0 < inverseCouplingSq initialInverse betaCoefficient scaleTime) :
    0 < couplingSq initialInverse betaCoefficient scaleTime := by
  simpa [couplingSq, one_div] using one_div_pos.mpr positive

/-- Positive beta coefficient makes the coupling decrease with energy scale. -/
theorem asymptotic_freedom_monotone {initialInverse betaCoefficient t₁ t₂ : ℝ}
    (betaPositive : 0 < betaCoefficient) (timeOrder : t₁ ≤ t₂)
    (denominatorPositive : 0 < inverseCouplingSq initialInverse betaCoefficient t₁) :
    couplingSq initialInverse betaCoefficient t₂ ≤
      couplingSq initialInverse betaCoefficient t₁ := by
  have hden : inverseCouplingSq initialInverse betaCoefficient t₁ ≤
      inverseCouplingSq initialInverse betaCoefficient t₂ := by
    unfold inverseCouplingSq
    exact add_le_add_left (mul_le_mul_of_nonneg_left timeOrder betaPositive.le) _
  have hpositive₂ : 0 < inverseCouplingSq initialInverse betaCoefficient t₂ :=
    denominatorPositive.trans_le hden
  unfold couplingSq
  simpa [one_div] using one_div_le_one_div_of_le denominatorPositive hden

/-- For `b>0`, the squared coupling can be made smaller than any positive target. -/
theorem asymptotic_freedom_arbitrarily_small {initialInverse betaCoefficient target : ℝ}
    (betaPositive : 0 < betaCoefficient) (targetPositive : 0 < target) :
    ∃ scaleTime,
      couplingSq initialInverse betaCoefficient scaleTime = target := by
  refine ⟨(1 / target - initialInverse) / betaCoefficient, ?_⟩
  have hb : betaCoefficient ≠ 0 := ne_of_gt betaPositive
  have ht : target ≠ 0 := ne_of_gt targetPositive
  unfold couplingSq inverseCouplingSq
  field_simp
  ring

/-- For `b<0`, the one-loop inverse coupling vanishes at a finite RG time. -/
noncomputable def landauPoleTime (initialInverse betaCoefficient : ℝ) : ℝ :=
  -initialInverse / betaCoefficient

theorem inverseCoupling_vanishes_at_landauPole {initialInverse betaCoefficient : ℝ}
    (betaNonzero : betaCoefficient ≠ 0) :
    inverseCouplingSq initialInverse betaCoefficient
      (landauPoleTime initialInverse betaCoefficient) = 0 := by
  unfold inverseCouplingSq landauPoleTime
  field_simp
  ring

/-- With positive initial inverse coupling and `b<0`, the pole lies at positive RG time. -/
theorem landauPoleTime_positive {initialInverse betaCoefficient : ℝ}
    (initialPositive : 0 < initialInverse) (betaNegative : betaCoefficient < 0) :
    0 < landauPoleTime initialInverse betaCoefficient := by
  unfold landauPoleTime
  exact div_pos_of_neg_of_neg (neg_lt_zero.mpr initialPositive) betaNegative

/-- The squared-coupling formula is singular at the Landau pole denominator. -/
theorem landauPole_denominator_zero {initialInverse betaCoefficient : ℝ}
    (betaNegative : betaCoefficient < 0) :
    inverseCouplingSq initialInverse betaCoefficient
      (landauPoleTime initialInverse betaCoefficient) = 0 :=
  inverseCoupling_vanishes_at_landauPole (ne_of_lt betaNegative)

end PhysicsModel.RunningCoupling
