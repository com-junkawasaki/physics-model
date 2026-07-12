import PhysicsModel.StandardModelAnomaly
import Mathlib.Data.Fin.Basic

/-! # Concrete Standard Model representation dimensions and electroweak charges

The nonabelian groups are represented here through their fundamental
multiplicities (three colors and weak doublets); matrix group actions remain a
later layer.  Hypercharge, electric charge, Higgs neutrality, and all three
Yukawa hypercharge selection rules are exact rational theorems.
-/

namespace PhysicsModel.Electroweak

abbrev Color := Fin 3
abbrev WeakComponent := Fin 2
abbrev Generation := Fin 3

theorem three_colors : Fintype.card Color = 3 := by simp
theorem weak_doublet_has_two_components : Fintype.card WeakComponent = 2 := by simp
theorem three_generations : Fintype.card Generation = 3 := by simp

/-- Representation dimensions and weak hypercharge. -/
structure QuantumNumbers where
  colorDimension : ℕ
  weakDimension : ℕ
  hypercharge : ℚ
  deriving DecidableEq, Repr

def leftQuark : QuantumNumbers := ⟨3, 2, 1 / 6⟩
def rightUp : QuantumNumbers := ⟨3, 1, 2 / 3⟩
def rightDown : QuantumNumbers := ⟨3, 1, -1 / 3⟩
def leftLepton : QuantumNumbers := ⟨1, 2, -1 / 2⟩
def rightElectron : QuantumNumbers := ⟨1, 1, -1⟩
def higgs : QuantumNumbers := ⟨1, 2, 1 / 2⟩
def conjugateHiggs : QuantumNumbers := ⟨1, 2, -1 / 2⟩

def electricCharge (weakIsospin hypercharge : ℚ) : ℚ :=
  weakIsospin + hypercharge

theorem up_quark_charge : electricCharge (1 / 2) leftQuark.hypercharge = 2 / 3 := by
  norm_num [electricCharge, leftQuark]

theorem down_quark_charge : electricCharge (-1 / 2) leftQuark.hypercharge = -1 / 3 := by
  norm_num [electricCharge, leftQuark]

theorem neutrino_charge : electricCharge (1 / 2) leftLepton.hypercharge = 0 := by
  norm_num [electricCharge, leftLepton]

theorem electron_charge : electricCharge (-1 / 2) leftLepton.hypercharge = -1 := by
  norm_num [electricCharge, leftLepton]

/-- The lower Higgs component acquiring a VEV is electrically neutral. -/
theorem higgs_vacuum_neutral : electricCharge (-1 / 2) higgs.hypercharge = 0 := by
  norm_num [electricCharge, higgs]

/-- The orthogonal upper Higgs component has unit electric charge. -/
theorem charged_higgs_component : electricCharge (1 / 2) higgs.hypercharge = 1 := by
  norm_num [electricCharge, higgs]

/-- `Q̄_L H d_R` is neutral under U(1) hypercharge. -/
theorem down_yukawa_hypercharge_invariant :
    -leftQuark.hypercharge + higgs.hypercharge + rightDown.hypercharge = 0 := by
  norm_num [leftQuark, higgs, rightDown]

/-- `Q̄_L H̃ u_R` is neutral under U(1) hypercharge. -/
theorem up_yukawa_hypercharge_invariant :
    -leftQuark.hypercharge + conjugateHiggs.hypercharge + rightUp.hypercharge = 0 := by
  norm_num [leftQuark, conjugateHiggs, rightUp]

/-- `L̄_L H e_R` is neutral under U(1) hypercharge. -/
theorem lepton_yukawa_hypercharge_invariant :
    -leftLepton.hypercharge + higgs.hypercharge + rightElectron.hypercharge = 0 := by
  norm_num [leftLepton, higgs, rightElectron]

theorem all_yukawa_hypercharges_invariant :
    -leftQuark.hypercharge + higgs.hypercharge + rightDown.hypercharge = 0 ∧
    -leftQuark.hypercharge + conjugateHiggs.hypercharge + rightUp.hypercharge = 0 ∧
    -leftLepton.hypercharge + higgs.hypercharge + rightElectron.hypercharge = 0 :=
  ⟨down_yukawa_hypercharge_invariant, up_yukawa_hypercharge_invariant,
    lepton_yukawa_hypercharge_invariant⟩

/-- The concrete multiplet dimensions match the Standard Model assignments. -/
theorem multiplet_dimensions :
    (leftQuark.colorDimension, leftQuark.weakDimension) = (3, 2) ∧
    (rightUp.colorDimension, rightUp.weakDimension) = (3, 1) ∧
    (leftLepton.colorDimension, leftLepton.weakDimension) = (1, 2) ∧
    (higgs.colorDimension, higgs.weakDimension) = (1, 2) := by
  decide

end PhysicsModel.Electroweak
