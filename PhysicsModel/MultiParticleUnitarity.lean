import PhysicsModel.LorentzScattering
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Multiparticle unitarity by independent composition

The checked two-channel Hadamard scattering matrix is exactly unitary.  This
module packages a finite multiparticle extension: independent subsystems remain
normalized after scattering, and the product probability is preserved.
-/

namespace PhysicsModel.MultiParticleUnitarity

open scoped BigOperators
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

/-- A finite family of independent two-channel scattering subsystems. -/
structure FiniteParticleState (Particle : Type) [Fintype Particle] where
  state : Particle → TwoChannel

namespace FiniteParticleState

variable {Particle : Type} [Fintype Particle]

/-- The total Born probability is the product of the subsystem probabilities. -/
noncomputable def totalProbability (state : FiniteParticleState Particle) : ℝ :=
  ∏ particle, PhysicsModel.Scattering.totalProbability (state.state particle)

/-- Apply the checked unitary scattering to every subsystem independently. -/
noncomputable def scatter (state : FiniteParticleState Particle) : FiniteParticleState Particle where
  state := fun particle => PhysicsModel.Scattering.scatter (state.state particle)

/-- Independent scattering preserves the total probability of every finite family. -/
theorem scatter_probability_conserved (state : FiniteParticleState Particle) :
    totalProbability (scatter state) = totalProbability state := by
  unfold totalProbability scatter
  refine Finset.prod_congr rfl ?_
  intro particle hp
  exact PhysicsModel.Scattering.scatter_probability_conserved (state.state particle)

/-- If every subsystem starts normalized, the finite family stays normalized. -/
theorem scatter_normalized (state : FiniteParticleState Particle)
    (normalized : ∀ particle, PhysicsModel.Scattering.totalProbability (state.state particle) = 1) :
    totalProbability (scatter state) = 1 := by
  rw [scatter_probability_conserved]
  unfold totalProbability
  simp [normalized]

end FiniteParticleState

end PhysicsModel.MultiParticleUnitarity
