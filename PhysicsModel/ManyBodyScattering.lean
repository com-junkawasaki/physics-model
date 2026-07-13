import PhysicsModel.Born
import PhysicsModel.LorentzScattering
import PhysicsModel.RelativisticScattering
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Finite families of general `n → m` scattering processes

The `RelativisticScattering.Process` type already models arbitrary finite
incoming and outgoing particle counts.  This module lifts that to finite
families of processes and proves that conservation of total four-momentum is
stable under a common Lorentz frame.
-/

namespace PhysicsModel.ManyBodyScattering

open scoped BigOperators
open PhysicsModel.RelativisticScattering
open PhysicsModel.GeneralLorentz4
open PhysicsModel.Scattering

universe u v w

/-- A finite family of general scattering processes. -/
structure ProcessFamily
    (Index : Type u) [Fintype Index]
    (Incoming : Type v) [Fintype Incoming]
    (Outgoing : Type w) [Fintype Outgoing] where
  process : Index → Process Incoming Outgoing

namespace ProcessFamily

variable {Index : Type u} {Incoming : Type v} {Outgoing : Type w}
  [Fintype Index] [Fintype Incoming] [Fintype Outgoing]

/-- Total incoming four-momentum of a finite family of processes. -/
def totalIncoming (family : ProcessFamily Index Incoming Outgoing) : SpacetimeVector :=
  ∑ i, totalMomentum (family.process i).incoming

/-- Total outgoing four-momentum of a finite family of processes. -/
def totalOutgoing (family : ProcessFamily Index Incoming Outgoing) : SpacetimeVector :=
  ∑ i, totalMomentum (family.process i).outgoing

/-- Each process conserves momentum, so the whole family does too. -/
theorem totalMomentum_conserved (family : ProcessFamily Index Incoming Outgoing) :
    totalIncoming family = totalOutgoing family := by
  unfold totalIncoming totalOutgoing
  exact Finset.sum_congr rfl fun i hi => (family.process i).conserves

/-- A common Lorentz frame acts pointwise on a finite family of processes. -/
def transform (family : ProcessFamily Index Incoming Outgoing)
    (lorentz : Transform) : ProcessFamily Index Incoming Outgoing where
  process := fun i => (family.process i).transform lorentz

/-- The family total incoming momentum transforms covariantly. -/
theorem totalIncoming_transform
    (family : ProcessFamily Index Incoming Outgoing) (lorentz : Transform) :
    totalIncoming (family.transform lorentz) = lorentz (totalIncoming family) := by
  unfold totalIncoming transform
  simpa [Process.transform, RelativisticScattering.totalMomentum_transform] using
    (map_sum lorentz.toLinearEquiv
      (fun i => totalMomentum (family.process i).incoming) Finset.univ).symm

/-- The family total outgoing momentum transforms covariantly. -/
theorem totalOutgoing_transform
    (family : ProcessFamily Index Incoming Outgoing) (lorentz : Transform) :
    totalOutgoing (family.transform lorentz) = lorentz (totalOutgoing family) := by
  unfold totalOutgoing transform
  simpa [Process.transform, RelativisticScattering.totalMomentum_transform] using
    (map_sum lorentz.toLinearEquiv
      (fun i => totalMomentum (family.process i).outgoing) Finset.univ).symm

/-- The family-level transformed process is still momentum conserving. -/
theorem transform_preserves_conservation
    (family : ProcessFamily Index Incoming Outgoing) (lorentz : Transform) :
    totalIncoming (family.transform lorentz) = totalOutgoing (family.transform lorentz) := by
  rw [totalIncoming_transform, totalOutgoing_transform, totalMomentum_conserved]

end ProcessFamily

/-! A finite family of processes can be viewed directly as a Born measurement. -/
section BornFamily

variable {Index : Type u} {Incoming : Type v} {Outgoing : Type w}
  [Fintype Index] [Fintype Incoming] [Fintype Outgoing]

/-- A finite family of processes with a normalized amplitude on each process. -/
noncomputable def processMeasurement (family : ProcessFamily Index Incoming Outgoing)
    (amp : Process Incoming Outgoing → ℂ)
    (normalized : ∑ i, Complex.normSq (amp (family.process i)) = 1) : BornMeasurement where
  Outcome := Index
  finiteOutcome := inferInstance
  amplitude := fun i => amp (family.process i)
  normalized := normalized

/-- The process family directly yields a normalized Born measurement. -/
theorem processMeasurement_probability_sum (family : ProcessFamily Index Incoming Outgoing)
    (amp : Process Incoming Outgoing → ℂ)
    (normalized : ∑ i, Complex.normSq (amp (family.process i)) = 1) :
    ∑ i, (processMeasurement family amp normalized).probability i = 1 :=
  (processMeasurement family amp normalized).probability_normalized

/-- Channel-wise unit phases for a process family. -/
structure ProcessPhaseFamily
    (Index : Type u) [Fintype Index] where
  phase : Index → ℂ
  unit : ∀ i, Complex.normSq (phase i) = 1

/-- A phase-twisted Born measurement on a process family. -/
noncomputable def processPhaseMeasurement
    {Index : Type u} {Incoming : Type v} {Outgoing : Type w}
    [Fintype Index] [Fintype Incoming] [Fintype Outgoing]
    (phased : ProcessPhaseFamily Index)
    (family : ProcessFamily Index Incoming Outgoing)
    (amp : Process Incoming Outgoing → ℂ)
    (normalized : ∑ i, Complex.normSq (amp (family.process i)) = 1) : BornMeasurement where
  Outcome := Index
  finiteOutcome := inferInstance
  amplitude := fun i => phased.phase i * amp (family.process i)
  normalized := by
    simp [Complex.normSq_mul, phased.unit, normalized]

/-- Phase twists preserve the total Born weight of a process family. -/
theorem processPhaseMeasurement_probability_sum
    {Index : Type u} {Incoming : Type v} {Outgoing : Type w}
    [Fintype Index] [Fintype Incoming] [Fintype Outgoing]
    (phased : ProcessPhaseFamily Index)
    (family : ProcessFamily Index Incoming Outgoing)
    (amp : Process Incoming Outgoing → ℂ)
    (normalized : ∑ i, Complex.normSq (amp (family.process i)) = 1) :
    ∑ i, (processPhaseMeasurement phased family amp normalized).probability i = 1 :=
  (processPhaseMeasurement phased family amp normalized).probability_normalized

/-- A phase twist does not change the probability of any process outcome. -/
theorem processMeasurement_probability_phaseTwist
    {Index : Type u} {Incoming : Type v} {Outgoing : Type w}
    [Fintype Index] [Fintype Incoming] [Fintype Outgoing]
    (phased : ProcessPhaseFamily Index)
    (family : ProcessFamily Index Incoming Outgoing)
    (amp : Process Incoming Outgoing → ℂ)
    (normalized : ∑ i, Complex.normSq (amp (family.process i)) = 1)
    (i : Index) :
    (processPhaseMeasurement phased family amp normalized).probability i =
      Complex.normSq (amp (family.process i)) := by
  simp [processPhaseMeasurement, BornMeasurement.probability, phased.unit]

/-- If the amplitude is Lorentz-scalar, phase-twisted process probabilities are frame invariant. -/
theorem processPhaseMeasurement_probability_invariant
    {Index : Type u} {Incoming : Type v} {Outgoing : Type w}
    [Fintype Index] [Fintype Incoming] [Fintype Outgoing]
    (phased : ProcessPhaseFamily Index)
    (family : ProcessFamily Index Incoming Outgoing)
    (amp : Process Incoming Outgoing → ℂ) (lorentz : Transform)
    (scalarAmp : ∀ process, amp (process.transform lorentz) = amp process)
    (normalized : ∑ i, Complex.normSq (amp (family.process i)) = 1)
    (i : Index) :
    (processPhaseMeasurement phased (family.transform lorentz) amp
        (by
          simpa [ProcessFamily.transform, scalarAmp] using normalized)).probability i =
      (processPhaseMeasurement phased family amp normalized).probability i := by
  simp [processPhaseMeasurement, BornMeasurement.probability, ProcessFamily.transform, scalarAmp,
    phased.unit]

/-- If the process amplitude is Lorentz-scalar, each Born probability is frame invariant. -/
theorem processMeasurement_probability_invariant
    (family : ProcessFamily Index Incoming Outgoing)
    (amp : Process Incoming Outgoing → ℂ) (lorentz : Transform)
    (scalarAmp : ∀ process, amp (process.transform lorentz) = amp process)
    (normalized : ∑ i, Complex.normSq (amp (family.process i)) = 1)
    (i : Index) :
    (processMeasurement (family.transform lorentz) amp
        (by
          simpa [ProcessFamily.transform, scalarAmp] using normalized)).probability i =
      (processMeasurement family amp normalized).probability i := by
  simp [processMeasurement, BornMeasurement.probability, ProcessFamily.transform, scalarAmp]

end BornFamily

namespace ChannelTransfer

variable {Index : Type u} [Fintype Index]

/-- A finite family of independent two-channel scattering systems. -/
structure ChannelFamily (Index : Type u) [Fintype Index] where
  channel : Index → TwoChannel

/-- Channel-wise unit phases. -/
structure PhaseFamily (Index : Type u) [Fintype Index] where
  phase : Index → ℂ
  unit : ∀ i, Complex.normSq (phase i) = 1

/-- Apply a phase twist to every channel. -/
noncomputable def phaseTwist {Index : Type u} [Fintype Index]
    (phased : PhaseFamily Index) (family : ChannelFamily Index) : ChannelFamily Index where
  channel := fun i =>
    ⟨phased.phase i * (family.channel i).first, phased.phase i * (family.channel i).second⟩

/-- A phase-shifted two-channel scattering matrix. -/
noncomputable def interferenceScatter (phase : ℂ) (incoming : TwoChannel) : TwoChannel where
  first := (incoming.first + phase * incoming.second) / Scattering.normalizer
  second := (incoming.first - phase * incoming.second) / Scattering.normalizer

/-- Interference with a unit-norm phase preserves total probability. -/
theorem interferenceScatter_probability_conserved (phase : ℂ)
    (unit : Complex.normSq phase = 1) (incoming : TwoChannel) :
    Scattering.totalProbability (interferenceScatter phase incoming) =
      Scattering.totalProbability incoming := by
  unfold interferenceScatter Scattering.totalProbability
  dsimp
  rw [Complex.normSq_div, Complex.normSq_div, Scattering.normalizer_normSq]
  rw [← add_div, Scattering.parallelogram_normSq]
  have hphase : Complex.normSq (phase * incoming.second) = Complex.normSq incoming.second := by
    rw [Complex.normSq_mul, unit, one_mul]
  rw [hphase]
  ring

/-- Total Born probability of the family is the sum of the channel probabilities. -/
noncomputable def familyProbability {Index : Type u} [Fintype Index]
    (family : ChannelFamily Index) : ℝ :=
  ∑ i, Scattering.totalProbability (family.channel i)

/-- A concrete unitary transfer on every channel in the family. -/
noncomputable def familyTransfer {Index : Type u} [Fintype Index] (family : ChannelFamily Index) :
    ChannelFamily Index where
  channel := fun i => Scattering.scatter (family.channel i)

/-- Independent channel transfer preserves the total probability. -/
theorem familyProbability_conserved {Index : Type u} [Fintype Index]
    (family : ChannelFamily Index) :
    familyProbability (familyTransfer family) = familyProbability family := by
  unfold familyProbability familyTransfer
  simp [Scattering.scatter_probability_conserved]

/-- Channel phases do not change the total probability. -/
theorem familyProbability_phaseTwist {Index : Type u} [Fintype Index]
    (phased : PhaseFamily Index) (family : ChannelFamily Index) :
    familyProbability (phaseTwist phased family) = familyProbability family := by
  unfold familyProbability phaseTwist
  simp [Scattering.totalProbability, phased.unit]

/-- If the family is normalized, then the indexed channel measurement is a Born measurement. -/
noncomputable def measurement {Index : Type u} [Fintype Index] (family : ChannelFamily Index)
    (normalized : familyProbability family = 1) : BornMeasurement where
  Outcome := Index × Bool
  finiteOutcome := inferInstance
  amplitude := fun
    | (i, false) => (family.channel i).first
    | (i, true) => (family.channel i).second
  normalized := by
    rw [Fintype.sum_prod_type]
    simpa [familyProbability, Scattering.totalProbability, add_comm, add_left_comm, add_assoc]
      using normalized

theorem measurement_probability_sum {Index : Type u} [Fintype Index]
    (family : ChannelFamily Index)
    (normalized : familyProbability family = 1) :
    ∑ outcome, (measurement family normalized).probability outcome = 1 :=
  (measurement family normalized).probability_normalized

theorem transferred_measurement_probability_sum {Index : Type u} [Fintype Index]
    (family : ChannelFamily Index)
    (normalized : familyProbability family = 1) :
    ∑ outcome, (measurement (familyTransfer family)
        (by simpa [familyProbability_conserved] using normalized)).probability outcome = 1 :=
  (measurement (familyTransfer family)
      (by simpa [familyProbability_conserved] using normalized)).probability_normalized

/-- A phase twist on the channels leaves the measurement normalization intact. -/
theorem phaseTwist_measurement_probability_sum {Index : Type u} [Fintype Index]
    (phased : PhaseFamily Index) (family : ChannelFamily Index)
    (normalized : familyProbability family = 1) :
    ∑ outcome, (measurement (phaseTwist phased family)
        (by simpa [familyProbability_phaseTwist] using normalized)).probability outcome = 1 :=
  (measurement (phaseTwist phased family)
      (by simpa [familyProbability_phaseTwist] using normalized)).probability_normalized

/-- A phase-interfering beam splitter preserves total probability. -/
theorem interferenceMeasurement_probability_sum
    (phase : ℂ) (unit : Complex.normSq phase = 1) (incoming : TwoChannel)
    (normalized : Scattering.totalProbability incoming = 1) :
    ∑ outcome, (Scattering.outgoingMeasurement (interferenceScatter phase incoming)
        (by simpa [interferenceScatter_probability_conserved phase unit incoming] using
          normalized)).probability outcome = 1 :=
  (Scattering.outgoingMeasurement (interferenceScatter phase incoming)
      (by simpa [interferenceScatter_probability_conserved phase unit incoming] using
        normalized)).probability_normalized

end ChannelTransfer

end PhysicsModel.ManyBodyScattering
