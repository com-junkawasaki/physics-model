import PhysicsModel.Core

/-! # Page--Wootters-style conditional predictions -/

namespace PhysicsModel

universe u v w

/-- A clock is a subsystem whose readings condition predictions about a system. -/
structure RelationalExperiment where
  ClockReading : Type u
  SystemOutcome : Type v
  joint : ClockReading → SystemOutcome → Prop

namespace RelationalExperiment

/-- Conditional state/proposition: the system outcome relative to a clock reading. -/
def conditioned (experiment : RelationalExperiment) (τ : experiment.ClockReading) :
    experiment.SystemOutcome → Prop := experiment.joint τ

@[simp] theorem conditioned_iff (experiment : RelationalExperiment)
    (τ : experiment.ClockReading) (a : experiment.SystemOutcome) :
    experiment.conditioned τ a ↔ experiment.joint τ a := Iff.rfl

end RelationalExperiment

/-- Two internal clocks are physically equivalent when translation preserves
all conditional predictions. -/
structure ClockEquivalence (first second : RelationalExperiment) where
  translate : first.ClockReading → second.ClockReading
  outcome : first.SystemOutcome = second.SystemOutcome
  invariant : ∀ τ a, first.joint τ a ↔
    second.joint (translate τ) (outcome ▸ a)

theorem clock_choice_independent {first second : RelationalExperiment}
    (equiv : ClockEquivalence first second) (τ : first.ClockReading)
    (a : first.SystemOutcome) :
    first.conditioned τ a ↔
      second.conditioned (equiv.translate τ) (equiv.outcome ▸ a) :=
  equiv.invariant τ a

end PhysicsModel
