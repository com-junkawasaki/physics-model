import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import IncRQM.Analytic.U1

/-! # Born probabilities from normalized relational amplitudes

This closes the finite-dimensional mathematical step from complex amplitudes to
probabilities.  The physical claim that amplitudes, rather than another response
function, are selected by the fundamental dynamics remains an explicit premise.
-/

namespace PhysicsModel

open scoped BigOperators

universe u

/-- A finite exhaustive measurement with normalized complex amplitudes. -/
structure BornMeasurement where
  Outcome : Type u
  finiteOutcome : Fintype Outcome
  amplitude : Outcome → ℂ
  normalized : ∑ outcome, Complex.normSq (amplitude outcome) = 1

attribute [instance] BornMeasurement.finiteOutcome

namespace BornMeasurement

noncomputable def probability (measurement : BornMeasurement) (outcome : measurement.Outcome) : ℝ :=
  Complex.normSq (measurement.amplitude outcome)

theorem probability_nonnegative (measurement : BornMeasurement)
    (outcome : measurement.Outcome) : 0 ≤ measurement.probability outcome :=
  Complex.normSq_nonneg _

theorem probability_normalized (measurement : BornMeasurement) :
    ∑ outcome, measurement.probability outcome = 1 := measurement.normalized

theorem probability_le_one (measurement : BornMeasurement)
    (outcome : measurement.Outcome) : measurement.probability outcome ≤ 1 := by
  rw [← measurement.probability_normalized]
  exact Finset.single_le_sum
    (fun other _ => measurement.probability_nonnegative other) (Finset.mem_univ outcome)

/-- Multiplying every amplitude by a unit complex phase changes no Born probability. -/
theorem global_phase_invariant (measurement : BornMeasurement) (phase : ℂ)
    (unit : Complex.normSq phase = 1) (outcome : measurement.Outcome) :
    Complex.normSq (phase * measurement.amplitude outcome) =
      measurement.probability outcome := by
  rw [Complex.normSq_mul, unit, one_mul]
  rfl

end BornMeasurement

/-- Inc--RQM already supplies a concrete gauge-invariant two-path Born intensity. -/
theorem inc_rqm_born_is_frame_independent
    (frame : IncRQM.ABVertex → Circle)
    (field : IncRQM.LinkField IncRQM.ABVertex Circle) :
    IncRQM.AnalyticU1.abBornExperiment.observe (IncRQM.gaugeTransform frame field) =
      IncRQM.AnalyticU1.abBornExperiment.observe field :=
  IncRQM.AnalyticU1.abBorn_gauge_invariant frame field

end PhysicsModel
