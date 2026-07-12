import Mathlib.Data.Finsupp.Basic

/-! # Background-free kinematics

This module formalizes the proposed ontology, not an experimentally established
theory of quantum gravity.  No spacetime coordinate occurs in the primitive
data.  Physical states are selected by a constraint.
-/

namespace PhysicsModel

universe u v w

/-- Primitive data of a background-free relational model. -/
structure Model where
  State : Type u
  Observable : Type v
  Value : Type w
  whole : State
  constraint : State → Prop
  admissible : constraint whole
  predicts : State → Observable → Value → Prop

/-- A physical fact is explicitly a prediction of an admissible state. -/
structure Fact (model : Model) where
  state : model.State
  admissible : model.constraint state
  observable : model.Observable
  value : model.Value
  holds : model.predicts state observable value

theorem whole_is_physical (model : Model) : model.constraint model.whole :=
  model.admissible

/-- The analogue of `C |Ψ⟩ = 0`: zeroes of a constraint operator are physical. -/
def KernelConstraint {State K : Type*} [Zero K] (C : State → K) : State → Prop :=
  fun ψ => C ψ = 0

@[simp] theorem kernelConstraint_iff {State K : Type*} [Zero K]
    (C : State → K) (ψ : State) : KernelConstraint C ψ ↔ C ψ = 0 := Iff.rfl

end PhysicsModel
