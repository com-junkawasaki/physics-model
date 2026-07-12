import PhysicsModel.Core

/-! # Space from relational adjacency and coarse graining -/

namespace PhysicsModel

universe u v w

/-- A labelled relation graph; vertices are not embedded in a background space. -/
structure QuantumGeometry where
  Node : Type u
  Label : Type v
  adjacent : Node → Node → Prop
  label : Node → Node → Label
  symmetric : ∀ {a b}, adjacent a b → adjacent b a

/-- A coarse geometry is whatever macroscopic description a coarse-graining map returns. -/
structure CoarseGraining (geometry : QuantumGeometry) where
  MacroscopicGeometry : Type w
  coarse : geometry.Node → MacroscopicGeometry
  indistinguishable : geometry.Node → geometry.Node → Prop
  sound : ∀ {a b}, indistinguishable a b → coarse a = coarse b

theorem coarse_geometry_well_defined {geometry : QuantumGeometry}
    (cg : CoarseGraining geometry) {a b : geometry.Node}
    (h : cg.indistinguishable a b) : cg.coarse a = cg.coarse b := cg.sound h

end PhysicsModel
