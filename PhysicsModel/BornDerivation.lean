import PhysicsModel.Born
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp

/-! # Born weights from symmetric fine branching and additive coarse graining

This module isolates a finite envariance-style derivation.  Permutation symmetry
forces equal fine branches to carry equal probability; normalization fixes each
weight to `1/n`; finite additivity then gives `m/n` for a coarse event.  The same
rational weight is exactly the squared norm of its coarse amplitude.
-/

namespace PhysicsModel.BornDerivation

open scoped BigOperators

/-- A normalized finite experiment whose fine branches are physically equivalent. -/
structure SymmetricBranching (n : ℕ) [NeZero n] where
  probability : Fin n → ℝ
  probability_nonnegative : ∀ branch, 0 ≤ probability branch
  permutationSymmetry : ∀ first second, probability first = probability second
  normalized : ∑ branch, probability branch = 1

namespace SymmetricBranching

variable {n : ℕ} [NeZero n]

/-- Symmetry and normalization uniquely fix every fine-branch probability. -/
theorem probability_eq_inverse_card (experiment : SymmetricBranching n) (branch : Fin n) :
    experiment.probability branch = 1 / (n : ℝ) := by
  have hsum : ∑ other, experiment.probability other =
      (n : ℝ) * experiment.probability branch := by
    calc
      ∑ other, experiment.probability other = ∑ _other : Fin n, experiment.probability branch := by
        apply Finset.sum_congr rfl
        intro other _
        exact experiment.permutationSymmetry other branch
      _ = (n : ℝ) * experiment.probability branch := by simp
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  apply (eq_div_iff hn).2
  rw [mul_comm, ← hsum, experiment.normalized]

/-- Additive probability of a coarse event represented by a set of fine branches. -/
noncomputable def eventProbability (experiment : SymmetricBranching n)
    (event : Finset (Fin n)) : ℝ :=
  ∑ branch ∈ event, experiment.probability branch

/-- A coarse event containing `m` of `n` symmetric branches has probability `m/n`. -/
theorem eventProbability_eq_card_div (experiment : SymmetricBranching n)
    (event : Finset (Fin n)) :
    experiment.eventProbability event = (event.card : ℝ) / (n : ℝ) := by
  unfold eventProbability
  simp_rw [experiment.probability_eq_inverse_card]
  simp [div_eq_mul_inv]

theorem eventProbability_nonnegative (experiment : SymmetricBranching n)
    (event : Finset (Fin n)) : 0 ≤ experiment.eventProbability event := by
  unfold eventProbability
  exact Finset.sum_nonneg fun branch _ => experiment.probability_nonnegative branch

theorem eventProbability_le_one (experiment : SymmetricBranching n)
    (event : Finset (Fin n)) : experiment.eventProbability event ≤ 1 := by
  rw [experiment.eventProbability_eq_card_div]
  have hcard : event.card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ event)
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  apply (div_le_one hn).2
  exact_mod_cast hcard

/-- Canonical nonnegative coarse amplitude selected by the rational branch weight. -/
noncomputable def eventAmplitude (experiment : SymmetricBranching n)
    (event : Finset (Fin n)) : ℂ :=
  (Real.sqrt (experiment.eventProbability event) : ℝ)

/-- Finite symmetric branching yields the Born rule exactly for every coarse event. -/
theorem born_rule_for_event (experiment : SymmetricBranching n)
    (event : Finset (Fin n)) :
    Complex.normSq (experiment.eventAmplitude event) =
      experiment.eventProbability event := by
  unfold eventAmplitude
  rw [Complex.normSq_ofReal,
    Real.mul_self_sqrt (experiment.eventProbability_nonnegative event)]

/-- Hence the squared amplitude is explicitly the rational multiplicity `m/n`. -/
theorem born_weight_eq_card_div (experiment : SymmetricBranching n)
    (event : Finset (Fin n)) :
    Complex.normSq (experiment.eventAmplitude event) = (event.card : ℝ) / (n : ℝ) := by
  rw [experiment.born_rule_for_event, experiment.eventProbability_eq_card_div]

/-- Complementary coarse events retain exact normalization. -/
theorem event_complement_normalized (experiment : SymmetricBranching n)
    (event : Finset (Fin n)) :
    experiment.eventProbability event + experiment.eventProbability eventᶜ = 1 := by
  rw [experiment.eventProbability_eq_card_div,
    experiment.eventProbability_eq_card_div]
  have hcard : event.card + eventᶜ.card = n := by
    simpa only [Fintype.card_fin] using Finset.card_add_card_compl event
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  rw [← add_div, ← Nat.cast_add, hcard]
  exact div_self hn

end SymmetricBranching

end PhysicsModel.BornDerivation
