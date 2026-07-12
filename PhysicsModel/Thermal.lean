import RelationalTime
import Mathlib.Data.Real.Basic

/-! # State-dependent thermal orientation -/

namespace PhysicsModel

universe u

/-- Entropy decorates relational events; monotonicity supplies an arrow. -/
structure ThermalArrow (system : RelationalTime.EventSystem) where
  entropy : system.Event → ℝ
  increases : ∀ {a b}, system.step a b → entropy a < entropy b

namespace ThermalArrow

theorem increases_before {system : RelationalTime.EventSystem}
    (arrow : ThermalArrow system) {a b : system.Event}
    (h : system.before a b) : arrow.entropy a < arrow.entropy b := by
  induction h with
  | single h => exact arrow.increases h
  | tail _ h ih => exact lt_trans ih (arrow.increases h)

theorem causal {system : RelationalTime.EventSystem} (arrow : ThermalArrow system) :
    system.IsCausal := by
  intro event h
  exact (lt_irrefl _) (arrow.increases_before h)

/-- A strictly entropy-compatible clock and the thermal arrow induce the same orientation. -/
theorem agrees_with_clock {system : RelationalTime.EventSystem}
    (arrow : ThermalArrow system) (clock : RelationalTime.Clock system)
    {a b : system.Event} (h : system.before a b) :
    arrow.entropy a < arrow.entropy b ∧ clock.tick a < clock.tick b :=
  ⟨arrow.increases_before h, clock.before_advances h⟩

end ThermalArrow
end PhysicsModel
