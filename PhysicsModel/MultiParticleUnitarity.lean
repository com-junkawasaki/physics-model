import PhysicsModel.LorentzScattering

/-! # Multiparticle unitarity by independent composition

The checked two-channel Hadamard scattering matrix is exactly unitary.  This
module packages a finite multiparticle extension: independent subsystems remain
normalized after scattering, and the product probability is preserved.
-/

namespace PhysicsModel.MultiParticleUnitarity

open PhysicsModel.Scattering

/-- Two independent two-channel scattering subsystems. -/
structure TwoParticleState where
  first : TwoChannel
  second : TwoChannel

/-- The total Born probability of an independent two-particle state. -/
noncomputable def totalProbability (state : TwoParticleState) : ℝ :=
  PhysicsModel.Scattering.totalProbability state.first *
    PhysicsModel.Scattering.totalProbability state.second

/-- Apply the checked unitary scattering to each particle independently. -/
noncomputable def scatter (state : TwoParticleState) : TwoParticleState where
  first := PhysicsModel.Scattering.scatter state.first
  second := PhysicsModel.Scattering.scatter state.second

/-- Independent multiparticle scattering preserves total probability exactly. -/
theorem scatter_probability_conserved (state : TwoParticleState) :
    totalProbability (scatter state) = totalProbability state := by
  unfold totalProbability scatter
  rw [PhysicsModel.Scattering.scatter_probability_conserved,
    PhysicsModel.Scattering.scatter_probability_conserved]

/-- If each particle subsystem starts normalized, the product state stays normalized. -/
theorem scatter_normalized (state : TwoParticleState)
    (first_normalized : PhysicsModel.Scattering.totalProbability state.first = 1)
    (second_normalized : PhysicsModel.Scattering.totalProbability state.second = 1) :
    totalProbability (scatter state) = 1 := by
  rw [scatter_probability_conserved, totalProbability, first_normalized, second_normalized]
  ring

end PhysicsModel.MultiParticleUnitarity
