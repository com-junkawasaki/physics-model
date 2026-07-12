import PhysicsModel.Born
import PhysicsModel.StandardModel

/-! # Concrete bridges from Inc--RQM

This module replaces two abstract certificates by explicit constructions:
local U(1) frames acting on the finite AB link field, and a normalized two-port
Born measurement.  It also imports the proved Wilson-to-Maxwell continuum limit.
-/

namespace PhysicsModel

open scoped IncRQM.AbelianGaugeGroup BigOperators

namespace IncU1Bridge

abbrev Frame := IncRQM.ABVertex → Circle
abbrev Field := IncRQM.LinkField IncRQM.ABVertex Circle

noncomputable def compose (first second : Frame) : Frame :=
  fun vertex => first vertex * second vertex

theorem transform_compose (first second : Frame) (field : Field) :
    IncRQM.gaugeTransform (compose first second) field =
      IncRQM.gaugeTransform first (IncRQM.gaugeTransform second field) := by
  funext a b
  simp only [IncRQM.gaugeTransform, compose]
  rw [IncRQM.AbelianGaugeGroup.inv_mul_distrib']
  simp only [IncRQM.AbelianGaugeGroup.mul_assoc']
  rw [IncRQM.AbelianGaugeGroup.mul_comm' (first b) (second b)]

/-- A concrete gauge-matter sector: fields are AB link comparisons and the
effective action value is their relational Born intensity. -/
noncomputable def bornGaugeSector : GaugeMatterSector Frame Field ℝ where
  compose := compose
  transform := IncRQM.gaugeTransform
  transform_compose := transform_compose
  effectiveAction := IncRQM.AnalyticU1.abBornExperiment.observe
  invariant := IncRQM.AnalyticU1.abBorn_gauge_invariant

theorem concrete_born_action_gauge_invariant (frame : Frame) (field : Field) :
    bornGaugeSector.effectiveAction (bornGaugeSector.transform frame field) =
      bornGaugeSector.effectiveAction field :=
  bornGaugeSector.action_gauge_invariant frame field

end IncU1Bridge

namespace TwoPortBorn

/-- Beam-splitter output amplitudes for relative unit phase `u`. -/
noncomputable def amplitude (u : Circle) : Bool → ℂ
  | false => (1 + (u : ℂ)) / 2
  | true => (1 - (u : ℂ)) / 2

theorem normalized (u : Circle) :
    ∑ outcome : Bool, Complex.normSq (amplitude u outcome) = 1 := by
  rw [Fintype.sum_bool]
  simp only [amplitude, Complex.normSq_div, Complex.normSq_ofNat]
  rw [Complex.normSq_add, Complex.normSq_sub, Circle.normSq_coe]
  norm_num
  ring

/-- The explicit relational two-port apparatus is a certified Born measurement. -/
noncomputable def measurement (u : Circle) : BornMeasurement where
  Outcome := Bool
  finiteOutcome := inferInstance
  amplitude := amplitude u
  normalized := normalized u

theorem detector_probabilities_sum_to_one (u : Circle) :
    ∑ outcome, (measurement u).probability outcome = 1 :=
  (measurement u).probability_normalized

theorem detector_probability_bounds (u : Circle) (outcome : Bool) :
    0 ≤ (measurement u).probability outcome ∧
      (measurement u).probability outcome ≤ 1 :=
  ⟨(measurement u).probability_nonnegative outcome,
    (measurement u).probability_le_one outcome⟩

end TwoPortBorn

end PhysicsModel
