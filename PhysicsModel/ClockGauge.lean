import PhysicsModel.Conditional
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! # Internal-clock gauge and prediction independence

Unlike the earlier one-way `ClockEquivalence`, a clock isomorphism contains
invertible translations of both readings and outcome labels.  These maps form a
groupoid, and conditional physical predictions are invariant along every
identity, inverse, and composite clock change.
-/

namespace PhysicsModel

/-- Reversible change of internal clock and outcome coordinates. -/
structure ClockIsomorphism (first second : RelationalExperiment) where
  reading : first.ClockReading ≃ second.ClockReading
  outcome : first.SystemOutcome ≃ second.SystemOutcome
  invariant : ∀ τ a,
    first.joint τ a ↔ second.joint (reading τ) (outcome a)

namespace ClockIsomorphism

def refl (experiment : RelationalExperiment) : ClockIsomorphism experiment experiment where
  reading := Equiv.refl _
  outcome := Equiv.refl _
  invariant := by intro τ a; rfl

def symm {first second : RelationalExperiment}
    (iso : ClockIsomorphism first second) : ClockIsomorphism second first where
  reading := iso.reading.symm
  outcome := iso.outcome.symm
  invariant := by
    intro τ a
    simpa using
      (iso.invariant (iso.reading.symm τ) (iso.outcome.symm a)).symm

def trans {first second third : RelationalExperiment}
    (firstIso : ClockIsomorphism first second)
    (secondIso : ClockIsomorphism second third) : ClockIsomorphism first third where
  reading := firstIso.reading.trans secondIso.reading
  outcome := firstIso.outcome.trans secondIso.outcome
  invariant := by
    intro τ a
    exact (firstIso.invariant τ a).trans
      (secondIso.invariant (firstIso.reading τ) (firstIso.outcome a))

@[simp] theorem refl_reading (experiment : RelationalExperiment)
    (τ : experiment.ClockReading) : (refl experiment).reading τ = τ := rfl

@[simp] theorem refl_outcome (experiment : RelationalExperiment)
    (a : experiment.SystemOutcome) : (refl experiment).outcome a = a := rfl

@[simp] theorem symm_reading_apply {first second : RelationalExperiment}
    (iso : ClockIsomorphism first second) (τ : first.ClockReading) :
    iso.symm.reading (iso.reading τ) = τ := iso.reading.left_inv τ

@[simp] theorem symm_outcome_apply {first second : RelationalExperiment}
    (iso : ClockIsomorphism first second) (a : first.SystemOutcome) :
    iso.symm.outcome (iso.outcome a) = a := iso.outcome.left_inv a

/-- Conditional predictions are invariant under a reversible clock change. -/
theorem conditioned_invariant {first second : RelationalExperiment}
    (iso : ClockIsomorphism first second)
    (τ : first.ClockReading) (a : first.SystemOutcome) :
    first.conditioned τ a ↔
      second.conditioned (iso.reading τ) (iso.outcome a) :=
  iso.invariant τ a

/-- Round-tripping through another clock restores the original prediction. -/
theorem conditioned_roundtrip {first second : RelationalExperiment}
    (iso : ClockIsomorphism first second)
    (τ : first.ClockReading) (a : first.SystemOutcome) :
    first.conditioned τ a ↔
      first.conditioned (iso.symm.reading (iso.reading τ))
        (iso.symm.outcome (iso.outcome a)) := by
  simp

/-- Prediction invariance along two successive internal-clock choices. -/
theorem conditioned_transitive {first second third : RelationalExperiment}
    (firstIso : ClockIsomorphism first second)
    (secondIso : ClockIsomorphism second third)
    (τ : first.ClockReading) (a : first.SystemOutcome) :
    first.conditioned τ a ↔
      third.conditioned ((firstIso.trans secondIso).reading τ)
        ((firstIso.trans secondIso).outcome a) :=
  (firstIso.trans secondIso).conditioned_invariant τ a

end ClockIsomorphism

/-- Rewrite an experiment using any equivalent clock-reading coordinate. -/
def RelationalExperiment.reparametrize (experiment : RelationalExperiment)
    {NewReading : Type*} (coordinate : experiment.ClockReading ≃ NewReading) :
    RelationalExperiment where
  ClockReading := NewReading
  SystemOutcome := experiment.SystemOutcome
  joint := fun τ a => experiment.joint (coordinate.symm τ) a

/-- Every reversible clock reparametrization is a physical clock isomorphism. -/
def ClockIsomorphism.reparametrize (experiment : RelationalExperiment)
    {NewReading : Type*} (coordinate : experiment.ClockReading ≃ NewReading) :
    ClockIsomorphism experiment (experiment.reparametrize coordinate) where
  reading := coordinate
  outcome := Equiv.refl _
  invariant := by
    intro τ a
    simp [RelationalExperiment.reparametrize]

theorem reparametrized_prediction_independent (experiment : RelationalExperiment)
    {NewReading : Type*} (coordinate : experiment.ClockReading ≃ NewReading)
    (τ : experiment.ClockReading) (a : experiment.SystemOutcome) :
    experiment.conditioned τ a ↔
      (experiment.reparametrize coordinate).conditioned (coordinate τ) a :=
  (ClockIsomorphism.reparametrize experiment coordinate).conditioned_invariant τ a

/-! ## Finite-accuracy quantum clocks -/

/-- Conditional probability predictions for a clock and observed system. -/
structure ProbabilisticExperiment where
  ClockReading : Type*
  SystemOutcome : Type*
  probability : ClockReading → SystemOutcome → ℝ

/-- Clock translation whose prediction mismatch, including backreaction, is at most `error`. -/
structure ApproximateClockChange
    (first second : ProbabilisticExperiment) where
  reading : first.ClockReading → second.ClockReading
  outcome : first.SystemOutcome → second.SystemOutcome
  error : ℝ
  error_nonnegative : 0 ≤ error
  controlled : ∀ τ a,
    |first.probability τ a - second.probability (reading τ) (outcome a)| ≤ error

namespace ApproximateClockChange

def refl (experiment : ProbabilisticExperiment) :
    ApproximateClockChange experiment experiment where
  reading := id
  outcome := id
  error := 0
  error_nonnegative := le_rfl
  controlled := by intro τ a; simp

/-- Independent finite clock errors add under successive clock changes. -/
def trans {first second third : ProbabilisticExperiment}
    (firstChange : ApproximateClockChange first second)
    (secondChange : ApproximateClockChange second third) :
    ApproximateClockChange first third where
  reading := secondChange.reading ∘ firstChange.reading
  outcome := secondChange.outcome ∘ firstChange.outcome
  error := firstChange.error + secondChange.error
  error_nonnegative := add_nonneg firstChange.error_nonnegative secondChange.error_nonnegative
  controlled := by
    intro τ a
    change |first.probability τ a -
      third.probability (secondChange.reading (firstChange.reading τ))
        (secondChange.outcome (firstChange.outcome a))| ≤ _
    rw [show first.probability τ a -
        third.probability (secondChange.reading (firstChange.reading τ))
          (secondChange.outcome (firstChange.outcome a)) =
      (first.probability τ a -
        second.probability (firstChange.reading τ) (firstChange.outcome a)) +
      (second.probability (firstChange.reading τ) (firstChange.outcome a) -
        third.probability (secondChange.reading (firstChange.reading τ))
          (secondChange.outcome (firstChange.outcome a))) by ring]
    exact (abs_add _ _).trans
      (add_le_add (firstChange.controlled τ a)
        (secondChange.controlled (firstChange.reading τ) (firstChange.outcome a)))

/-- Zero clock/backreaction error recovers exact equality of probabilities. -/
theorem exact_of_zero_error {first second : ProbabilisticExperiment}
    (change : ApproximateClockChange first second) (zeroError : change.error = 0)
    (τ : first.ClockReading) (a : first.SystemOutcome) :
    first.probability τ a =
      second.probability (change.reading τ) (change.outcome a) := by
  have h := change.controlled τ a
  rw [zeroError] at h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

end ApproximateClockChange

end PhysicsModel
