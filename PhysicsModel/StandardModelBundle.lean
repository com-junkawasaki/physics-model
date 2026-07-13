import PhysicsModel.Chirality
import PhysicsModel.ElectroweakBreaking
import PhysicsModel.ElectroweakCharges
import PhysicsModel.StandardModelAnomaly
import PhysicsModel.StandardModelRunning
import PhysicsModel.SpecialUnitary

/-! # Bundled concrete Standard Model proofs

This module packages the checked Standard Model consequences into one witness.
It does not claim a microscopic derivation; it only records that the current
local proof stack is mutually consistent.
-/

namespace PhysicsModel.StandardModelBundle

/-- A compact bundle of the currently checked Standard Model consequences. -/
structure ProofBundle : Prop where
  multipletDimensions :
    (PhysicsModel.Electroweak.leftQuark.colorDimension,
      PhysicsModel.Electroweak.leftQuark.weakDimension) = (3, 2) ∧
    (PhysicsModel.Electroweak.rightUp.colorDimension,
      PhysicsModel.Electroweak.rightUp.weakDimension) = (3, 1) ∧
    (PhysicsModel.Electroweak.leftLepton.colorDimension,
      PhysicsModel.Electroweak.leftLepton.weakDimension) = (1, 2) ∧
    (PhysicsModel.Electroweak.higgs.colorDimension,
      PhysicsModel.Electroweak.higgs.weakDimension) = (1, 2)
  yukawaHyperchargeRules :
    -PhysicsModel.Electroweak.leftQuark.hypercharge + PhysicsModel.Electroweak.higgs.hypercharge +
      PhysicsModel.Electroweak.rightDown.hypercharge = 0 ∧
    -PhysicsModel.Electroweak.leftQuark.hypercharge +
      PhysicsModel.Electroweak.conjugateHiggs.hypercharge +
      PhysicsModel.Electroweak.rightUp.hypercharge = 0 ∧
    -PhysicsModel.Electroweak.leftLepton.hypercharge + PhysicsModel.Electroweak.higgs.hypercharge +
      PhysicsModel.Electroweak.rightElectron.hypercharge = 0
  anomalyCancellation :
    PhysicsModel.StandardModelAnomaly.gravitational = 0 ∧
    PhysicsModel.StandardModelAnomaly.cubicU1 = 0 ∧
    PhysicsModel.StandardModelAnomaly.su2SquaredU1 = 0 ∧
    PhysicsModel.StandardModelAnomaly.su3SquaredU1 = 0
  electroweakBreaking :
    PhysicsModel.ElectroweakBreaking.electromagneticGenerator (-1 / 2)
      PhysicsModel.Electroweak.higgs.hypercharge = 0 ∧
    PhysicsModel.ElectroweakBreaking.electromagneticGenerator (1 / 2)
      PhysicsModel.Electroweak.higgs.hypercharge = 1 ∧
    PhysicsModel.ElectroweakBreaking.neutralMassOperator 1 1 1
      (PhysicsModel.ElectroweakBreaking.photonDirection 1 1) = ⟨0, 0⟩
  rgPattern :
    0 < PhysicsModel.StandardModelRunning.betaCoefficient
        PhysicsModel.StandardModelRunning.su3BetaNumerator ∧
    0 < PhysicsModel.StandardModelRunning.betaCoefficient
        PhysicsModel.StandardModelRunning.su2BetaNumerator ∧
    PhysicsModel.StandardModelRunning.betaCoefficient
        PhysicsModel.StandardModelRunning.u1BetaNumerator < 0
  rgCoefficients :
    PhysicsModel.StandardModelRunning.betaCoefficient
      PhysicsModel.StandardModelRunning.su3BetaNumerator = 7 / (8 * Real.pi ^ 2) ∧
    PhysicsModel.StandardModelRunning.betaCoefficient
      PhysicsModel.StandardModelRunning.su2BetaNumerator = (19 / 6) / (8 * Real.pi ^ 2) ∧
    PhysicsModel.StandardModelRunning.betaCoefficient
      PhysicsModel.StandardModelRunning.u1BetaNumerator = (-41 / 6) / (8 * Real.pi ^ 2)

/-- The local proof stack already bundles the key Standard Model checks. -/
theorem concrete_standard_model_proofs : ProofBundle := by
  refine
    { multipletDimensions := PhysicsModel.Electroweak.multiplet_dimensions
      yukawaHyperchargeRules := PhysicsModel.Electroweak.all_yukawa_hypercharges_invariant
      anomalyCancellation := PhysicsModel.StandardModelAnomaly.all_local_hypercharge_anomalies_cancel
      electroweakBreaking := ?_
      rgPattern := PhysicsModel.StandardModelRunning.standardModel_one_loop_rg_pattern
      rgCoefficients := PhysicsModel.StandardModelRunning.standardModel_one_loop_coefficients
    }
  · constructor
    · exact PhysicsModel.ElectroweakBreaking.higgs_vacuum_unbroken
    · constructor
      · exact PhysicsModel.ElectroweakBreaking.upper_higgs_charge
      · simpa using PhysicsModel.ElectroweakBreaking.photon_massless 1 1 1

/-- The checked multiplet dimensions are available as a direct theorem. -/
theorem checked_multiplet_dimensions :
    (PhysicsModel.Electroweak.leftQuark.colorDimension,
      PhysicsModel.Electroweak.leftQuark.weakDimension) = (3, 2) ∧
    (PhysicsModel.Electroweak.rightUp.colorDimension,
      PhysicsModel.Electroweak.rightUp.weakDimension) = (3, 1) ∧
    (PhysicsModel.Electroweak.leftLepton.colorDimension,
      PhysicsModel.Electroweak.leftLepton.weakDimension) = (1, 2) ∧
    (PhysicsModel.Electroweak.higgs.colorDimension,
      PhysicsModel.Electroweak.higgs.weakDimension) = (1, 2) :=
  concrete_standard_model_proofs.multipletDimensions

/-- The checked Yukawa selection rules are available as a direct theorem. -/
theorem checked_yukawa_rules :
    -PhysicsModel.Electroweak.leftQuark.hypercharge + PhysicsModel.Electroweak.higgs.hypercharge +
      PhysicsModel.Electroweak.rightDown.hypercharge = 0 ∧
    -PhysicsModel.Electroweak.leftQuark.hypercharge +
      PhysicsModel.Electroweak.conjugateHiggs.hypercharge +
      PhysicsModel.Electroweak.rightUp.hypercharge = 0 ∧
    -PhysicsModel.Electroweak.leftLepton.hypercharge + PhysicsModel.Electroweak.higgs.hypercharge +
      PhysicsModel.Electroweak.rightElectron.hypercharge = 0 :=
  concrete_standard_model_proofs.yukawaHyperchargeRules

/-- The checked anomaly cancellation is available as a direct theorem. -/
theorem checked_anomaly_cancellation :
    PhysicsModel.StandardModelAnomaly.gravitational = 0 ∧
    PhysicsModel.StandardModelAnomaly.cubicU1 = 0 ∧
    PhysicsModel.StandardModelAnomaly.su2SquaredU1 = 0 ∧
    PhysicsModel.StandardModelAnomaly.su3SquaredU1 = 0 :=
  concrete_standard_model_proofs.anomalyCancellation

/-- The checked electroweak-breaking relations are available as a direct theorem. -/
theorem checked_electroweak_breaking :
    PhysicsModel.ElectroweakBreaking.electromagneticGenerator (-1 / 2)
      PhysicsModel.Electroweak.higgs.hypercharge = 0 ∧
    PhysicsModel.ElectroweakBreaking.electromagneticGenerator (1 / 2)
      PhysicsModel.Electroweak.higgs.hypercharge = 1 ∧
    PhysicsModel.ElectroweakBreaking.neutralMassOperator 1 1 1
      (PhysicsModel.ElectroweakBreaking.photonDirection 1 1) = ⟨0, 0⟩ :=
  concrete_standard_model_proofs.electroweakBreaking

/-- The checked RG pattern is available as a direct theorem. -/
theorem checked_rg_pattern :
    0 < PhysicsModel.StandardModelRunning.betaCoefficient
        PhysicsModel.StandardModelRunning.su3BetaNumerator ∧
    0 < PhysicsModel.StandardModelRunning.betaCoefficient
        PhysicsModel.StandardModelRunning.su2BetaNumerator ∧
    PhysicsModel.StandardModelRunning.betaCoefficient
        PhysicsModel.StandardModelRunning.u1BetaNumerator < 0 :=
  concrete_standard_model_proofs.rgPattern

/-- The checked RG coefficients are available as a direct theorem. -/
theorem checked_rg_coefficients :
    PhysicsModel.StandardModelRunning.betaCoefficient
      PhysicsModel.StandardModelRunning.su3BetaNumerator = 7 / (8 * Real.pi ^ 2) ∧
    PhysicsModel.StandardModelRunning.betaCoefficient
      PhysicsModel.StandardModelRunning.su2BetaNumerator = (19 / 6) / (8 * Real.pi ^ 2) ∧
    PhysicsModel.StandardModelRunning.betaCoefficient
      PhysicsModel.StandardModelRunning.u1BetaNumerator = (-41 / 6) / (8 * Real.pi ^ 2) :=
  concrete_standard_model_proofs.rgCoefficients

end PhysicsModel.StandardModelBundle
