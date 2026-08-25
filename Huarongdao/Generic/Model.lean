import Huarongdao.Model

namespace SlidingPuzzle

open Huarongdao (Pos Shape Direction translated)

/-- A state stores the top-left position of every numbered rectangular block. -/
structure State where
  positions : Array Pos
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

/-- Goals may constrain all blocks or only selected blocks. -/
structure Goal where
  positions : Array (Option Pos)
  deriving Repr, DecidableEq, BEq

/-- Require every numbered block to match one complete target state. -/
def Goal.complete (target : State) : Goal :=
  ⟨target.positions.map some⟩

/-- Position constraints for only selected blocks; unspecified entries are none. -/
def Goal.partial (positions : Array (Option Pos)) : Goal := ⟨positions⟩

/-- Complete description of one finite rectangular sliding-block puzzle. -/
structure PuzzleSpec where
  width : Nat
  height : Nat
  shapes : Array Shape
  initial : State
  goal : Goal
  deriving Repr, DecidableEq

structure Action where
  block : Nat
  direction : Direction
  deriving Repr, DecidableEq, BEq

def blockIds (spec : PuzzleSpec) : List Nat := List.range spec.shapes.size

def State.pos (state : State) (block : Nat) : Pos :=
  state.positions.getD block ⟨0, 0⟩

def PuzzleSpec.shape (spec : PuzzleSpec) (block : Nat) : Shape :=
  spec.shapes.getD block ⟨0, 0⟩

def occupiedCells (spec : PuzzleSpec) (state : State) (block : Nat) : List Pos :=
  let origin := state.pos block
  let shape := spec.shape block
  (List.range shape.height).flatMap fun dy =>
    (List.range shape.width).map fun dx => ⟨origin.x + dx, origin.y + dy⟩

def dimensionsValid (spec : PuzzleSpec) : Bool :=
  0 < spec.width && 0 < spec.height &&
  spec.shapes.size > 0 &&
  spec.shapes.all fun shape => 0 < shape.width && 0 < shape.height

def inBounds (spec : PuzzleSpec) (state : State) : Bool :=
  state.positions.size = spec.shapes.size && (blockIds spec).all fun block =>
    let position := state.pos block
    let shape := spec.shape block
    position.x + shape.width ≤ spec.width && position.y + shape.height ≤ spec.height

def noOverlap (spec : PuzzleSpec) (state : State) : Bool :=
  (blockIds spec).all fun left => (blockIds spec).all fun right =>
    left == right || (occupiedCells spec state left).all fun a =>
      (occupiedCells spec state right).all fun b => a != b

def valid (spec : PuzzleSpec) (state : State) : Bool :=
  dimensionsValid spec && inBounds spec state && noOverlap spec state

def ValidState (spec : PuzzleSpec) (state : State) : Prop := valid spec state = true

def goalDefined (spec : PuzzleSpec) : Bool :=
  spec.goal.positions.any Option.isSome

def goalWellFormed (spec : PuzzleSpec) : Bool :=
  spec.goal.positions.size = spec.shapes.size && goalDefined spec &&
  (blockIds spec).all fun block =>
    match spec.goal.positions.getD block none with
    | none => true
    | some position =>
        let shape := spec.shape block
        position.x + shape.width ≤ spec.width && position.y + shape.height ≤ spec.height

def wellFormed (spec : PuzzleSpec) : Bool :=
  valid spec spec.initial && goalWellFormed spec

def goalMatches (spec : PuzzleSpec) (state : State) : Bool :=
  valid spec state && (blockIds spec).all fun block =>
    match spec.goal.positions.getD block none with
    | none => true
    | some expected => state.pos block == expected

def moveUnchecked (spec : PuzzleSpec) (state : State)
    (block : Nat) (direction : Direction) : Option State := do
  if block < spec.shapes.size then
    let next ← translated (state.pos block) direction
    return ⟨state.positions.setIfInBounds block next⟩
  else none

def tryMove (spec : PuzzleSpec) (state : State)
    (block : Nat) (direction : Direction) : Option State := do
  let next ← moveUnchecked spec state block direction
  if valid spec next then some next else none

def legalMoves (spec : PuzzleSpec) (state : State) : List (Action × State) :=
  (blockIds spec).flatMap fun block => Huarongdao.Direction.all.filterMap fun direction =>
    (tryMove spec state block direction).map fun next => (⟨block, direction⟩, next)

def runMoves (spec : PuzzleSpec) : State → List Action → Option State
  | state, [] => some state
  | state, action :: rest => do
      let next ← tryMove spec state action.block action.direction
      runMoves spec next rest

def posCode (width : Nat) (position : Pos) : Nat := position.y * width + position.x

def State.key (spec : PuzzleSpec) (state : State) : String :=
  String.intercalate "," <| state.positions.toList.map fun position =>
    toString (posCode spec.width position)

theorem tryMove_preserves_validity {spec : PuzzleSpec} {state next : State}
    {block : Nat} {direction : Direction}
    (move : tryMove spec state block direction = some next) : ValidState spec next := by
  unfold tryMove at move
  cases hm : moveUnchecked spec state block direction with
  | none => simp [hm] at move
  | some candidate =>
      cases hv : valid spec candidate with
      | false => simp [hm, hv] at move
      | true =>
          simp [hm, hv] at move
          subst next
          exact hv

end SlidingPuzzle
