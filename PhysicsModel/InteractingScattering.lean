import PhysicsModel.Born
import PhysicsModel.RelativisticScattering
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Lorentz-covariant interacting scattering families

This module packages a finite family of scattering processes with amplitudes
that depend only on Lorentz invariants.  A common frame change leaves the full
Born-weight distribution unchanged.
-/

namespace PhysicsModel.InteractingScattering

open scoped BigOperators
open PhysicsModel.RelativisticScattering
open PhysicsModel.GeneralLorentz4

universe u

/-- A finite family of `2 → 2` scattering events. -/
structure ProcessFamily (Index : Type u) [Fintype Index] where
  event : Index → TwoToTwo

namespace ProcessFamily

variable {Index : Type u} [Fintype Index]

/-- A Lorentz-scalar amplitude assigned to each event in the family. -/
def amplitude (family : ProcessFamily Index) (amp : TwoToTwo → ℂ) (i : Index) : ℂ :=
  amp (family.event i)

/-- The total Born weight of a finite scattering family. -/
noncomputable def totalWeight (family : ProcessFamily Index) (amp : TwoToTwo → ℂ) : ℝ :=
  ∑ i, Complex.normSq (amplitude family amp i)

/-- A common Lorentz frame change acts pointwise on the whole family. -/
def transform (family : ProcessFamily Index) (lorentz : Transform) : ProcessFamily Index where
  event := fun i => (family.event i).transform lorentz

/-- Relabel a scattering family by an equivalence of index types. -/
def relabel {J : Type u} [Fintype J] (family : ProcessFamily Index) (e : Index ≃ J) :
    ProcessFamily J where
  event := fun j => family.event (e.symm j)

/-- Combine two scattering families into a disjoint union family. -/
def disjointSum {J : Type u} [Fintype J] (family : ProcessFamily Index) (other : ProcessFamily J) :
    ProcessFamily (Index ⊕ J) where
  event := Sum.elim family.event other.event

/-- Lorentz transform commutes with relabeling. -/
theorem transform_relabel {J : Type u} [Fintype J] (family : ProcessFamily Index)
    (e : Index ≃ J) (lorentz : Transform) :
    relabel (transform family lorentz) e = transform (relabel family e) lorentz := by
  rfl

/-- If the amplitude depends only on `s,t,u`, the total Born weight is frame invariant. -/
theorem totalWeight_invariant (family : ProcessFamily Index) (amp : TwoToTwo → ℂ)
    (lorentz : Transform)
    (scalarAmp : ∀ event lorentz, amp (event.transform lorentz) = amp event) :
    totalWeight (family.transform lorentz) amp = totalWeight family amp := by
  unfold totalWeight amplitude transform
  simp [scalarAmp]

/-- Relabeling a family does not change its total Born weight. -/
theorem totalWeight_relabel {J : Type u} [Fintype J] (family : ProcessFamily Index)
    (amp : TwoToTwo → ℂ) (e : Index ≃ J) :
    totalWeight (family.relabel e) amp = totalWeight family amp := by
  unfold totalWeight amplitude relabel
  simpa using
    (Fintype.sum_equiv e.symm
      (fun j : J => Complex.normSq (amp (family.event (e.symm j))))
      (fun i : Index => Complex.normSq (amp (family.event i)))
      (by intro i; rfl))

/-- The disjoint union family has total Born weight equal to the sum of parts. -/
theorem totalWeight_disjointSum {J : Type u} [Fintype J]
    (family : ProcessFamily Index) (other : ProcessFamily J) (amp : TwoToTwo → ℂ) :
    totalWeight (family.disjointSum other) amp =
      totalWeight family amp + totalWeight other amp := by
  unfold totalWeight amplitude disjointSum
  simp [Fintype.sum_sum_type]

/-- Channel-wise unit phases for a finite interacting scattering family. -/
structure PhaseFamily (Index : Type u) [Fintype Index] where
  phase : Index → ℂ
  unit : ∀ i, Complex.normSq (phase i) = 1

/-- A phase-twisted Born measurement on an interacting scattering family. -/
noncomputable def phaseTwistedMeasurement (family : ProcessFamily Index)
    (phased : PhaseFamily Index) (amp : TwoToTwo → ℂ)
    (normalized : totalWeight family amp = 1) : BornMeasurement where
  Outcome := Index
  finiteOutcome := inferInstance
  amplitude := fun i => phased.phase i * amp (family.event i)
  normalized := by
    simpa [totalWeight, Complex.normSq_mul, phased.unit] using normalized

/-- Phase twists preserve the total Born weight of an interacting scattering family. -/
theorem phaseTwistedMeasurement_probability_sum (family : ProcessFamily Index)
    (phased : PhaseFamily Index) (amp : TwoToTwo → ℂ)
    (normalized : totalWeight family amp = 1) :
    ∑ i, (phaseTwistedMeasurement family phased amp normalized).probability i = 1 :=
  (phaseTwistedMeasurement family phased amp normalized).probability_normalized

/-- A phase twist does not change any individual Born probability. -/
theorem phaseTwistedMeasurement_probability (family : ProcessFamily Index)
    (phased : PhaseFamily Index) (amp : TwoToTwo → ℂ)
    (normalized : totalWeight family amp = 1) (i : Index) :
    (phaseTwistedMeasurement family phased amp normalized).probability i =
      Complex.normSq (amp (family.event i)) := by
  simp [phaseTwistedMeasurement, BornMeasurement.probability, phased.unit]

/-- A finite set of invariant scattering channels keeps its total Born weight unchanged. -/
theorem totalWeight_invariant_of_s_t_u (family : ProcessFamily Index)
    (amp : ℝ → ℝ → ℝ → ℂ) (lorentz : Transform) :
    totalWeight (family.transform lorentz)
      (fun event => amp event.s event.t event.u) =
      totalWeight family (fun event => amp event.s event.t event.u) := by
  refine totalWeight_invariant (family := family) (amp := fun event => amp event.s event.t event.u)
    (lorentz := lorentz) ?_
  intro event lorentz'
  simpa using TwoToTwo.invariantAmplitude amp event lorentz'

/-- If the amplitude depends only on `s,t,u`, phase-twisted probabilities are Lorentz invariant. -/
theorem phaseTwistedMeasurement_probability_invariant_of_s_t_u (family : ProcessFamily Index)
    (phased : PhaseFamily Index) (amp : ℝ → ℝ → ℝ → ℂ) (lorentz : Transform) (i : Index)
    (normalized : totalWeight family (fun event => amp event.s event.t event.u) = 1) :
    (phaseTwistedMeasurement (family.transform lorentz) phased
        (fun event => amp event.s event.t event.u)
        (by
          simpa [totalWeight_invariant_of_s_t_u (family := family) (amp := amp)
            (lorentz := lorentz)] using normalized)).probability i =
      (phaseTwistedMeasurement family phased
        (fun event => amp event.s event.t event.u) normalized).probability i := by
  simp [phaseTwistedMeasurement, BornMeasurement.probability, transform,
    phased.unit, TwoToTwo.invariantAmplitude]

/-- The entire phase-twisted Born distribution is unchanged by a common Lorentz frame. -/
theorem phaseTwistedMeasurement_distribution_invariant_of_s_t_u (family : ProcessFamily Index)
    (phased : PhaseFamily Index) (amp : ℝ → ℝ → ℝ → ℂ) (lorentz : Transform)
    (normalized : totalWeight family (fun event => amp event.s event.t event.u) = 1) :
    ∀ i, (phaseTwistedMeasurement (family.transform lorentz) phased
        (fun event => amp event.s event.t event.u)
        (by
          simpa [totalWeight_invariant_of_s_t_u (family := family) (amp := amp)
            (lorentz := lorentz)] using normalized)).probability i =
      (phaseTwistedMeasurement family phased
        (fun event => amp event.s event.t event.u) normalized).probability i := by
  intro i
  exact phaseTwistedMeasurement_probability_invariant_of_s_t_u family phased amp lorentz i
    normalized

/-- A finite family of scattering channels can be regarded as a Born measurement. -/
noncomputable def measurement (family : ProcessFamily Index) (amp : TwoToTwo → ℂ)
    (normalized : totalWeight family amp = 1) : BornMeasurement where
  Outcome := Index
  finiteOutcome := inferInstance
  amplitude := fun i => amp (family.event i)
  normalized := normalized

/-- The Born probability of each channel is invariant under a common Lorentz frame. -/
theorem probability_invariant_of_s_t_u (family : ProcessFamily Index)
    (amp : ℝ → ℝ → ℝ → ℂ) (lorentz : Transform) (i : Index)
    (normalized : totalWeight family (fun event => amp event.s event.t event.u) = 1) :
    (measurement (family.transform lorentz) (fun event => amp event.s event.t event.u)
        (by
          simpa [totalWeight_invariant_of_s_t_u (family := family) (amp := amp)
            (lorentz := lorentz)] using normalized)).probability i =
    (measurement family (fun event => amp event.s event.t event.u) normalized).probability i := by
  simp [measurement, BornMeasurement.probability, transform,
    TwoToTwo.invariantAmplitude]

/-- The entire finite Born distribution is unchanged by a common Lorentz frame. -/
theorem measurement_distribution_invariant_of_s_t_u (family : ProcessFamily Index)
    (amp : ℝ → ℝ → ℝ → ℂ) (lorentz : Transform)
    (normalized : totalWeight family (fun event => amp event.s event.t event.u) = 1) :
    ∀ i, (measurement (family.transform lorentz) (fun event => amp event.s event.t event.u)
        (by
          simpa [totalWeight_invariant_of_s_t_u (family := family) (amp := amp)
            (lorentz := lorentz)] using normalized)).probability i =
      (measurement family (fun event => amp event.s event.t event.u) normalized).probability i := by
  intro i
  exact probability_invariant_of_s_t_u family amp lorentz i normalized

/-- A normalized invariant family gives a concrete Born measurement. -/
theorem measurement_normalized_of_s_t_u (family : ProcessFamily Index)
    (amp : ℝ → ℝ → ℝ → ℂ)
    (normalized : totalWeight family (fun event => amp event.s event.t event.u) = 1) :
    ∑ i, (measurement family (fun event => amp event.s event.t event.u) normalized).probability i = 1 :=
  (measurement family (fun event => amp event.s event.t event.u) normalized).probability_normalized

/-- Relabeling preserves the probability assigned to the corresponding event. -/
theorem measurement_relabel_probability {J : Type u} [Fintype J]
    (family : ProcessFamily Index) (amp : TwoToTwo → ℂ) (e : Index ≃ J)
    (normalized : totalWeight family amp = 1) (j : J) :
    let m : BornMeasurement :=
      measurement (relabel family e) amp
        (by
          simpa [totalWeight_relabel (family := family) (amp := amp) e] using normalized)
    m.probability j =
      (measurement family amp normalized).probability (e.symm j) := by
  dsimp
  simp [measurement, relabel, BornMeasurement.probability,
    totalWeight_relabel (family := family) (amp := amp) e]

/-- The disjoint union family preserves the left-hand Born probabilities pointwise. -/
theorem measurement_disjointSum_inl {J : Type u} [Fintype J]
    (family : ProcessFamily Index) (other : ProcessFamily J) (amp : TwoToTwo → ℂ)
    (normalized : totalWeight family amp + totalWeight other amp = 1) (i : Index) :
    let m : BornMeasurement :=
      measurement (disjointSum family other) amp
        (by simpa [totalWeight_disjointSum] using normalized)
    m.probability (Sum.inl i) =
      Complex.normSq (amp (family.event i)) := by
  dsimp
  simp [measurement, disjointSum, BornMeasurement.probability,
    totalWeight_disjointSum, normalized]

/-- The disjoint union family preserves the right-hand Born probabilities pointwise. -/
theorem measurement_disjointSum_inr {J : Type u} [Fintype J]
    (family : ProcessFamily Index) (other : ProcessFamily J) (amp : TwoToTwo → ℂ)
    (normalized : totalWeight family amp + totalWeight other amp = 1) (j : J) :
    let m : BornMeasurement :=
      measurement (disjointSum family other) amp
        (by simpa [totalWeight_disjointSum] using normalized)
    m.probability (Sum.inr j) =
      Complex.normSq (amp (other.event j)) := by
  dsimp
  simp [measurement, disjointSum, BornMeasurement.probability,
    totalWeight_disjointSum, normalized]

end ProcessFamily

end PhysicsModel.InteractingScattering
