import Huarongdao.StateSpaceConnectivity
import Huarongdao.Search
import Std.Data.HashSet
import Std.Tactic

namespace Huarongdao
namespace ClassicFullSpace

open StateSpace
open ClassicStateSpaceKernel

/--
Two equal-shape states are continuously equivalent when a finite sequence of
legal primitive slides connects them. This is the reachability relation of
the maintained equal-shape task.
-/
def ContinuousEquivalent (source target : ShapeState) : Prop :=
  shape.Reachable source target

theorem continuousEquivalent_equivalence :
    Equivalence ContinuousEquivalent := by
  constructor
  · exact shape.reachable_refl
  · exact shapeReversible.reachable_symm
  · exact Task.reachable_trans

/-- The abstract type of continuous equivalence classes in the shape layer. -/
abbrev ContinuousClass :=
  shape.Component shapeReversible

/-- Project an equal-shape state to its continuous equivalence class. -/
def continuousClassOf (state : ShapeState) : ContinuousClass :=
  shape.componentOf shapeReversible state

@[simp] theorem continuousClassOf_eq_iff
    {source target : ShapeState} :
    continuousClassOf source = continuousClassOf target ↔
      ContinuousEquivalent source target :=
  Task.componentOf_eq_iff_reachable

/-- Top-left anchors for a rectangle with the given number of legal columns
    and rows. -/
def anchors (columns rows : Nat) : List Pos :=
  (List.range rows).flatMap fun y =>
    (List.range columns).map fun x => ⟨x, y⟩

def boardCells : List Pos :=
  anchors 4 5

def caoAnchors : List Pos :=
  anchors 3 4

def guanAnchors : List Pos :=
  anchors 3 5

def verticalAnchors : List Pos :=
  anchors 4 4

/-- Cells occupied by a rectangle whose top-left anchor and shape are known. -/
def rectangleCells (anchor : Pos) (shape : Shape) : List Pos :=
  (List.range shape.height).flatMap fun dy =>
    (List.range shape.width).map fun dx =>
      ⟨anchor.x + dx, anchor.y + dy⟩

/--
Build the fixed labelled representative of one equal-shape placement.
Vertical anchors and soldier anchors are stored in ascending board order.
-/
def representativeState
    (cao guan : Pos) (vertical soldiers : List Pos) : State :=
  State.ofFn fun piece =>
    match piece with
    | .caoCao => cao
    | .guanYu => guan
    | .zhangFei => vertical.getD 0 ⟨0, 0⟩
    | .zhaoYun => vertical.getD 1 ⟨0, 0⟩
    | .maChao => vertical.getD 2 ⟨0, 0⟩
    | .huangZhong => vertical.getD 3 ⟨0, 0⟩
    | .soldier1 => soldiers.getD 0 ⟨0, 0⟩
    | .soldier2 => soldiers.getD 1 ⟨0, 0⟩
    | .soldier3 => soldiers.getD 2 ⟨0, 0⟩
    | .soldier4 => soldiers.getD 3 ⟨0, 0⟩

/--
Constructively enumerate candidate geometric placements of the classic shape
multiset. The separate `EnumerationComplete` proposition states the remaining
mathematical obligation that this generator covers every valid shape state.
-/
def allShapeStatesList : List State :=
  caoAnchors.flatMap fun cao =>
    guanAnchors.flatMap fun guan =>
      (verticalAnchors.sublistsLen 4).flatMap fun vertical =>
        let occupied :=
          rectangleCells cao ⟨2, 2⟩ ++
          rectangleCells guan ⟨2, 1⟩ ++
          vertical.flatMap fun anchor =>
            rectangleCells anchor ⟨1, 2⟩
        if occupied.Nodup then
          let free :=
            boardCells.filter fun cell => cell ∉ occupied
          (free.sublistsLen 4).map fun soldiers =>
            representativeState cao guan vertical soldiers
        else
          []

/-- Deterministically ordered executable presentation of the full shape space. -/
def allShapeStates : Array State :=
  allShapeStatesList.toArray

/--
The generator-completeness statement needed to identify the executable array
with the entire mathematical space of valid equal-shape placements.
-/
def EnumerationComplete : Prop :=
  ∀ source : ValidClassicState,
    ∃ representative ∈ allShapeStatesList,
      SameShape source.1 representative

set_option maxRecDepth 100000 in
theorem enumerationComplete_quotient_cover
    (allValid : ∀ index : Fin allShapeStates.size,
      ValidState allShapeStates[index])
    (complete : EnumerationComplete) :
    ∀ node : ShapeState,
      ∃ index : Fin allShapeStates.size,
        ShapeState.ofState ⟨allShapeStates[index], allValid index⟩ = node := by
  intro node
  refine Quotient.inductionOn node ?_
  intro source
  rcases complete source with ⟨representative, member, sameShape⟩
  have memberArray : representative ∈ allShapeStates.toList := by
    simpa [allShapeStates] using member
  obtain ⟨index, bound, indexed⟩ :=
    List.getElem_of_mem memberArray
  let indexFin : Fin allShapeStates.size :=
    ⟨index, by simpa using bound⟩
  have stateEq : allShapeStates[indexFin] = representative := by
    change allShapeStates[index] = representative
    exact (Array.getElem_toList bound).symm.trans indexed
  refine ⟨indexFin, ?_⟩
  apply ShapeState.ofState_eq
  have arraySame :
      SameShape allShapeStates[indexFin] representative := by
    rw [stateEq]
    exact sameShape_refl _
  exact sameShape_trans arraySame (sameShape_symm sameShape)

/-- Executable uniqueness check for equal-shape keys. -/
def uniqueKeysList : Std.HashSet String → List State → Bool
  | _, [] => true
  | known, state :: states =>
      if known.contains state.key then
        false
      else
        uniqueKeysList (known.insert state.key) states

def uniqueKeys (states : Array State) : Bool :=
  uniqueKeysList {} states.toList

/-- Collision-free base-20 code for valid classic equal-shape states. -/
def placementCode (state : State) : Nat :=
  let codes :=
    [(state.pos .caoCao).code, (state.pos .guanYu).code] ++
    ((verticalPositions state).map Pos.code).mergeSort ++
    ((soldierPositions state).map Pos.code).mergeSort
  codes.foldl (fun encoded code => encoded * 20 + code) 0

/-- Index every canonical placement by its compact equal-shape code. -/
def placementIndex (states : Array State) :
    Std.HashMap Nat Nat := Id.run do
  let mut index : Std.HashMap Nat Nat := {}
  for stateId in List.range states.size do
    index := index.insert
      (placementCode (states.getD stateId classic)) stateId
  return index

/--
Compact occupancy table for a valid classic board.  Entry `i` is the index of
the piece occupying board cell `i`; `Piece.all.length` denotes an empty cell.
-/
def occupancyTable (state : State) : Array Nat := Id.run do
  let empty := Piece.all.length
  let mut occupancy := Array.replicate boardCells.length empty
  for piece in Piece.all do
    for cell in occupiedCells state piece do
      occupancy := occupancy.set! cell.code piece.index
  return occupancy

/--
Fast local legality test for a one-cell slide from an already valid state.
Only the moved rectangle can create a new boundary violation or overlap, so
the other nine rectangles do not need to be revalidated.
-/
def locallyLegalMove
    (state : State) (occupancy : Array Nat)
    (piece : Piece) (direction : Direction) : Option State := do
  let target ← translated (state.pos piece) direction
  let shape := piece.shape
  if target.x + shape.width ≤ 4 && target.y + shape.height ≤ 5 then
    let cells := rectangleCells target shape
    let empty := Piece.all.length
    if cells.all fun cell =>
        let occupant := occupancy.getD cell.code empty
        occupant == empty || occupant == piece.index then
      moveUnchecked state piece direction
    else
      none
  else
    none

/-- Finite summary of one continuous equivalence class. -/
structure ComponentSummary where
  representative : State
  stateCount : Nat
  directedEdgeCount : Nat
  containsClassic : Bool
  deriving Repr

/-- Raw result of the single-pass component traversal. -/
structure ComponentRun where
  summaries : Array ComponentSummary
  closed : Bool
  /-- Component identifier assigned to every input-state index. -/
  componentOf : Array Nat
  /-- Root input-state index for every component identifier. -/
  roots : Array Nat
  /-- DFS predecessor. Roots have no predecessor. -/
  parent : Array (Option Nat)
  /-- Strictly increasing discovery number used to certify parent acyclicity. -/
  discovery : Array Nat

/--
Partition the full placement enumeration into legal-slide components.

The representative is the first state of the component in `allShapeStates`.
Since that array has a fixed constructive order, every class receives a
deterministic canonical initial representative.
-/
def componentSummariesOf
    (states : Array State) : ComponentRun := Id.run do
  let index := placementIndex states
  let classicCode := placementCode classic
  let mut seen := Array.replicate states.size false
  let mut summaries : Array ComponentSummary := #[]
  let mut componentOf := Array.replicate states.size states.size
  let mut roots : Array Nat := #[]
  let mut parent : Array (Option Nat) := Array.replicate states.size none
  let mut discovery := Array.replicate states.size states.size
  let mut discoveryCursor := 0
  let mut closed := true
  for candidateId in List.range states.size do
    if !(seen.getD candidateId true) then
      let candidate := states.getD candidateId classic
      let componentId := summaries.size
      let mut stack : Array Nat := #[candidateId]
      let mut stateCount := 0
      let mut directedEdgeCount := 0
      let mut containsClassic := false
      seen := seen.set! candidateId true
      componentOf := componentOf.set! candidateId componentId
      discovery := discovery.set! candidateId discoveryCursor
      discoveryCursor := discoveryCursor + 1
      roots := roots.push candidateId
      while 0 < stack.size do
        let currentId :=
          stack.getD (stack.size - 1) candidateId
        stack := stack.pop
        let current := states.getD currentId classic
        let occupancy := occupancyTable current
        stateCount := stateCount + 1
        if placementCode current = classicCode then
          containsClassic := true
        for piece in Piece.all do
          for direction in Direction.all do
            match locallyLegalMove current occupancy piece direction with
            | none => pure ()
            | some target =>
                directedEdgeCount := directedEdgeCount + 1
                match index.get? (placementCode target) with
                | none =>
                    closed := false
                | some targetId =>
                    if !(seen.getD targetId true) then
                      seen := seen.set! targetId true
                      componentOf := componentOf.set! targetId componentId
                      parent := parent.set! targetId (some currentId)
                      discovery := discovery.set! targetId discoveryCursor
                      discoveryCursor := discoveryCursor + 1
                      stack := stack.push targetId
      summaries := summaries.push {
        representative := candidate
        stateCount := stateCount
        directedEdgeCount := directedEdgeCount
        containsClassic := containsClassic
      }
  return {
    summaries := summaries
    closed := closed
    componentOf := componentOf
    roots := roots
    parent := parent
    discovery := discovery
  }

/-- The deterministic DFS run used by the full-space semantic certificates.
Keeping this definition in the data module lets independent certificate
modules reuse the same computation without importing cardinality theorems. -/
def fullSpaceRun : ComponentRun :=
  componentSummariesOf allShapeStates

def componentSummaries : Array ComponentSummary :=
  (componentSummariesOf allShapeStates).summaries

def componentRepresentatives : Array State :=
  componentSummaries.map (·.representative)

def componentSizes : Array Nat :=
  componentSummaries.map (·.stateCount)

def coveredStateCount : Nat :=
  componentSizes.foldl (· + ·) 0

def classicComponentIndex? : Option Nat :=
  componentSummaries.findIdx? (·.containsClassic)

def classicComponentSize : Nat :=
  match classicComponentIndex? with
  | none => 0
  | some index =>
      (componentSummaries.getD index
        ⟨classic, 0, 0, false⟩).stateCount

/-- Shared result of the expensive full-space computation. -/
structure Analysis where
  stateCount : Nat
  allValid : Bool
  keysUnique : Bool
  summaries : Array ComponentSummary
  coveredCount : Nat
  classicSize : Nat
  closed : Bool

def analyze : Analysis :=
  let states := allShapeStates
  let run := componentSummariesOf states
  let summaries := run.summaries
  let covered :=
    summaries.foldl (fun total summary =>
      total + summary.stateCount) 0
  let classicSummary :=
    summaries.find? (·.containsClassic)
  {
    stateCount := states.size
    allValid := states.all valid
    keysUnique := uniqueKeys states
    summaries := summaries
    coveredCount := covered
    classicSize :=
      match classicSummary with
      | none => 0
      | some summary => summary.stateCount
    closed := run.closed
  }

/-- Numerical and executable integrity claims checked in one native run. -/
def fullSpaceClaims : Prop :=
  let result := analyze
  result.stateCount = 65880 ∧
  result.allValid = true ∧
  result.keysUnique = true ∧
  result.closed = true ∧
  result.summaries.size = 898 ∧
  result.coveredCount = 65880 ∧
  result.classicSize = 25955

instance fullSpaceClaimsDecidable : Decidable fullSpaceClaims := by
  unfold fullSpaceClaims
  infer_instance

def checkFullSpace : Bool :=
  decide fullSpaceClaims

end ClassicFullSpace
end Huarongdao
