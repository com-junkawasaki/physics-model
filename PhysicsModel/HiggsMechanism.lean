import Mathlib.Analysis.Complex.Circle

/-! # A checked abelian Higgs vacuum mechanism

This is the radial sector of a complex Higgs field.  It proves gauge invariance
of the potential, characterizes its minima, and shows that a positive vacuum
scale admits a nonzero vacuum while the phase orbit remains degenerate.
-/

namespace PhysicsModel.Higgs

/-- Mexican-hat potential expressed through the gauge-invariant radial norm. -/
noncomputable def potential (coupling vacuumScale : ℝ) (field : ℂ) : ℝ :=
  coupling * (Complex.normSq field - vacuumScale ^ 2) ^ 2

theorem potential_nonnegative {coupling : ℝ} (vacuumScale : ℝ) (field : ℂ)
    (coupling_nonnegative : 0 ≤ coupling) :
    0 ≤ potential coupling vacuumScale field := by
  exact mul_nonneg coupling_nonnegative (sq_nonneg _)

/-- Local U(1) phases leave the Higgs potential invariant. -/
theorem potential_gauge_invariant (coupling vacuumScale : ℝ)
    (phase : Circle) (field : ℂ) :
    potential coupling vacuumScale ((phase : ℂ) * field) =
      potential coupling vacuumScale field := by
  unfold potential
  rw [Complex.normSq_mul, Circle.normSq_coe, one_mul]

/-- For positive coupling, zero potential is exactly the vacuum-radius equation. -/
theorem potential_eq_zero_iff {coupling vacuumScale : ℝ} {field : ℂ}
    (coupling_positive : 0 < coupling) :
    potential coupling vacuumScale field = 0 ↔
      Complex.normSq field = vacuumScale ^ 2 := by
  unfold potential
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hcoupling | hsquare
    · exact False.elim (ne_of_gt coupling_positive hcoupling)
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · intro h
    rw [h, sub_self]
    norm_num

/-- The positive real representative lies on the vacuum manifold. -/
theorem real_vacuum_has_zero_potential (coupling vacuumScale : ℝ) :
    potential coupling vacuumScale (vacuumScale : ℂ) = 0 := by
  unfold potential Complex.normSq
  dsimp
  ring

/-- A strictly positive vacuum scale gives a genuinely nonzero vacuum field. -/
theorem real_vacuum_nonzero {vacuumScale : ℝ} (vacuum_positive : 0 < vacuumScale) :
    (vacuumScale : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt vacuum_positive

/-- Every phase rotation of a vacuum is another energetically degenerate vacuum. -/
theorem vacuum_orbit_degenerate {coupling vacuumScale : ℝ} (phase : Circle)
    (field : ℂ) (vacuum : potential coupling vacuumScale field = 0) :
    potential coupling vacuumScale ((phase : ℂ) * field) = 0 := by
  rw [potential_gauge_invariant, vacuum]

/-- Positive coupling makes every vacuum a global minimum. -/
theorem vacuum_is_global_minimum {coupling vacuumScale : ℝ} {field : ℂ}
    (coupling_nonnegative : 0 ≤ coupling)
    (vacuum : potential coupling vacuumScale field = 0) (other : ℂ) :
    potential coupling vacuumScale field ≤ potential coupling vacuumScale other := by
  rw [vacuum]
  exact potential_nonnegative vacuumScale other coupling_nonnegative

end PhysicsModel.Higgs
