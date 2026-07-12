import PhysicsModel.Born
import PhysicsModel.Resonance
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

/-! # Lorentz mass shells and unitary two-channel scattering

This module checks two low-energy consistency conditions without postulating
their conclusions: algebraic Lorentz boosts preserve the mass-shell quadratic
form, and the concrete two-channel Hadamard scattering matrix preserves total
Born probability.
-/

namespace PhysicsModel

namespace Lorentz

/-- Energy and one spatial momentum component. -/
structure Momentum where
  energy : ℝ
  momentum : ℝ

/-- Algebraic boost parameters.  `γ²(1-β²)=1` is the defining Lorentz relation. -/
structure Boost where
  beta : ℝ
  gamma : ℝ
  lorentzRelation : gamma ^ 2 * (1 - beta ^ 2) = 1

def massSquared (p : Momentum) : ℝ := p.energy ^ 2 - p.momentum ^ 2

def Boost.act (boost : Boost) (p : Momentum) : Momentum where
  energy := boost.gamma * (p.energy - boost.beta * p.momentum)
  momentum := boost.gamma * (p.momentum - boost.beta * p.energy)

/-- The Minkowski quadratic form is exactly invariant under every certified boost. -/
theorem massSquared_invariant (boost : Boost) (p : Momentum) :
    massSquared (boost.act p) = massSquared p := by
  unfold massSquared Boost.act
  dsimp
  calc
    (boost.gamma * (p.energy - boost.beta * p.momentum)) ^ 2 -
        (boost.gamma * (p.momentum - boost.beta * p.energy)) ^ 2 =
      (boost.gamma ^ 2 * (1 - boost.beta ^ 2)) *
        (p.energy ^ 2 - p.momentum ^ 2) := by ring
    _ = p.energy ^ 2 - p.momentum ^ 2 := by rw [boost.lorentzRelation, one_mul]

theorem mass_shell_preserved (boost : Boost) (p : Momentum) (mass : ℝ)
    (onShell : massSquared p = mass ^ 2) :
    massSquared (boost.act p) = mass ^ 2 := by
  rw [massSquared_invariant, onShell]

/-- Resonance pole mass labels are frame independent when the real momentum is
on the corresponding mass shell. -/
theorem resonance_mass_shell_preserved (boost : Boost) (p : Momentum)
    (mode : Mode) (onShell : massSquared p = mode.mass ^ 2) :
    massSquared (boost.act p) = mode.mass ^ 2 :=
  mass_shell_preserved boost p mode.mass onShell

end Lorentz

namespace Scattering

/-- Two incoming or outgoing complex channel amplitudes. -/
structure TwoChannel where
  first : ℂ
  second : ℂ

noncomputable def normalizer : ℂ := (Real.sqrt 2 : ℝ)

theorem normalizer_normSq : Complex.normSq normalizer = 2 := by
  norm_num [normalizer, Complex.normSq, Real.sq_sqrt]

/-- A balanced, nontrivial two-channel scattering matrix. -/
noncomputable def scatter (incoming : TwoChannel) : TwoChannel where
  first := (incoming.first + incoming.second) / normalizer
  second := (incoming.first - incoming.second) / normalizer

noncomputable def totalProbability (state : TwoChannel) : ℝ :=
  Complex.normSq state.first + Complex.normSq state.second

theorem parallelogram_normSq (a b : ℂ) :
    Complex.normSq (a + b) + Complex.normSq (a - b) =
      2 * (Complex.normSq a + Complex.normSq b) := by
  rw [Complex.normSq_add, Complex.normSq_sub]
  ring

/-- Concrete S-matrix unitarity: total Born probability is conserved. -/
theorem scatter_probability_conserved (incoming : TwoChannel) :
    totalProbability (scatter incoming) = totalProbability incoming := by
  unfold totalProbability scatter
  dsimp
  rw [Complex.normSq_div, Complex.normSq_div, normalizer_normSq]
  rw [← add_div, parallelogram_normSq]
  ring

/-- A normalized incoming state therefore gives a normalized outgoing state. -/
theorem scatter_normalized (incoming : TwoChannel)
    (normalized : totalProbability incoming = 1) :
    totalProbability (scatter incoming) = 1 := by
  rw [scatter_probability_conserved, normalized]

/-- The outgoing ports form a concrete certified Born measurement whenever the
incoming two-channel state is normalized. -/
noncomputable def outgoingMeasurement (incoming : TwoChannel)
    (normalized : totalProbability incoming = 1) : BornMeasurement where
  Outcome := Bool
  finiteOutcome := inferInstance
  amplitude
    | false => (scatter incoming).first
    | true => (scatter incoming).second
  normalized := by
    rw [Fintype.sum_bool]
    simpa [totalProbability, add_comm] using scatter_normalized incoming normalized

theorem outgoing_probabilities_sum_to_one (incoming : TwoChannel)
    (normalized : totalProbability incoming = 1) :
    ∑ outcome, (outgoingMeasurement incoming normalized).probability outcome = 1 :=
  (outgoingMeasurement incoming normalized).probability_normalized

end Scattering
end PhysicsModel
