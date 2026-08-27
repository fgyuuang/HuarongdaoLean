import Huarongdao.CorridorCompression

namespace Huarongdao

/-!
The maintained classic state-space tower.

Every level is the same formal object, `StateSpace.Task`; later levels do not
replace or mutate earlier ones.  Quotient levels inherit semantics through
canonical homomorphisms and bisimulation lifting, while corridor compression
retains proof-carrying expansions of every weighted macro edge.
-/
namespace ClassicStateSpaceKernel

/-- Legal labelled boards and exact piece-labelled moves. -/
def concrete : StateSpace.Task ValidClassicState Action :=
  validClassicTask

/-- Equal-shaped labels identified, with one quotient edge per concrete move. -/
def shape : StateSpace.Task ShapeState Unit :=
  shapeGraphTask

/-- Equal-shape states additionally identified under horizontal reflection. -/
def mirror : StateSpace.Task MirrorShapeState Unit :=
  mirrorShapeTask

/-- Mirror states with forced non-branching corridors represented as weighted macros. -/
def corridor : StateSpace.Task CorridorState Nat :=
  corridorTask

/-- Canonical projection from concrete labelled states to equal-shape classes. -/
def concreteToShape : StateSpace.Task.Hom concrete shape :=
  shapeObservation.projectionHom

/-- Canonical projection from equal-shape classes to horizontal-mirror classes. -/
def shapeToMirror : StateSpace.Task.Hom shape mirror :=
  mirrorShapeObservation.projectionHom

/-- The composed two-stage quotient projection. -/
def concreteToMirror : StateSpace.Task.Hom concrete mirror :=
  shapeToMirror.comp concreteToShape

/-- Concrete walks project through both exact quotient layers without changing length. -/
theorem concreteWalk_projectsToMirror
    (walk : concrete.Walk source target) :
    (concreteToMirror.mapWalk walk).length = walk.length :=
  concreteToMirror.mapWalk_length walk

/--
Every weighted corridor walk expands through both quotient layers to a
concrete valid-state walk whose primitive length is the sum of macro weights.
-/
theorem corridorWalk_liftsToConcrete
    (walk : corridor.Walk source target)
    (sourceRepresentative : ValidClassicState)
    (source_eq :
      MirrorShapeState.ofState sourceRepresentative = source.1) :
    ∃ targetRepresentative,
      ∃ concreteWalk : concrete.Walk
          sourceRepresentative targetRepresentative,
        concreteWalk.length = walk.actions.sum ∧
        MirrorShapeState.ofState targetRepresentative = target.1 :=
  corridorWalk_liftToConcreteWithCost walk sourceRepresentative source_eq

/-- Goal predicates agree at the concrete representative and mirror quotient. -/
theorem mirrorGoal_ofState_iff (state : ValidClassicState) :
    mirror.goal (MirrorShapeState.ofState state) ↔
      concrete.goal state :=
  Iff.rfl

/-- Goal predicates agree between a corridor anchor and its mirror node. -/
theorem corridorGoal_iff_mirror (state : CorridorState) :
    corridor.goal state ↔ mirror.goal state.1 :=
  Iff.rfl

end ClassicStateSpaceKernel

end Huarongdao
