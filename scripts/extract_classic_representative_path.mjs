import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { fileURLToPath } from 'node:url';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const graphPath = path.join(root, 'frontend', 'graph.json');
const fullSpacePath = path.join(root, 'frontend', 'full-shape-components.json');
const graphSource = fs.readFileSync(graphPath, 'utf8');
const fullSpaceSource = fs.readFileSync(fullSpacePath, 'utf8');
const graph = JSON.parse(graphSource);
const fullSpace = JSON.parse(fullSpaceSource);

function sha256(source) {
  return crypto.createHash('sha256').update(source, 'utf8').digest('hex');
}

const generatorVersion = 2;
const graphSha256 = sha256(graphSource);
const fullSpaceSha256 = sha256(fullSpaceSource);

const classicId = fullSpace.meta.classicComponentId;
const representative = fullSpace.components.find(component => component.id === classicId);
if (!representative) throw new Error(`Missing component ${classicId}`);

const target = graph.states.find(state => state.key === representative.key);
if (!target) throw new Error(`Representative key ${representative.key} is absent from graph.json`);

const statesById = new Map(graph.states.map(state => [state.id, state]));
const incoming = new Map();
for (const edge of graph.edges) {
  const source = statesById.get(edge.source);
  const destination = statesById.get(edge.target);
  if (!source || !destination || destination.distance !== source.distance + 1) continue;
  if (!incoming.has(edge.target)) incoming.set(edge.target, edge);
}

const quotientRoute = [];
for (let current = target.id; current !== graph.meta.initial;) {
  const edge = incoming.get(current);
  if (!edge) throw new Error(`No BFS predecessor for node ${current}`);
  quotientRoute.push(edge);
  current = edge.source;
}
quotientRoute.reverse();

const shapes = [
  [2, 2],
  [2, 1],
  [1, 2],
  [1, 2],
  [1, 2],
  [1, 2],
  [1, 1],
  [1, 1],
  [1, 1],
  [1, 1]
];
const directions = [
  ['up', 0, -1],
  ['down', 0, 1],
  ['left', -1, 0],
  ['right', 1, 0]
];

function placementCode([x, y]) {
  return y * 4 + x;
}

function shapeKey(positions) {
  const vertical = positions.slice(2, 6).map(placementCode).sort((a, b) => a - b);
  const soldiers = positions.slice(6, 10).map(placementCode).sort((a, b) => a - b);
  return [
    placementCode(positions[0]),
    placementCode(positions[1]),
    vertical.join(','),
    soldiers.join(',')
  ].join(';');
}

function move(positions, piece, dx, dy) {
  const next = positions.map(position => [...position]);
  next[piece] = [next[piece][0] + dx, next[piece][1] + dy];
  const occupied = new Set();
  for (let index = 0; index < next.length; index += 1) {
    const [x, y] = next[index];
    const [width, height] = shapes[index];
    if (x < 0 || y < 0 || x + width > 4 || y + height > 5) return null;
    for (let cellY = y; cellY < y + height; cellY += 1) {
      for (let cellX = x; cellX < x + width; cellX += 1) {
        const cell = `${cellX},${cellY}`;
        if (occupied.has(cell)) return null;
        occupied.add(cell);
      }
    }
  }
  return next;
}

let concrete = fullSpace.meta.classicPositions.map(position => [...position]);
const concreteActions = [];
for (const edge of quotientRoute) {
  const desiredKey = statesById.get(edge.target).key;
  let lifted = null;
  for (let piece = 0; piece < shapes.length && !lifted; piece += 1) {
    for (const [direction, dx, dy] of directions) {
      const next = move(concrete, piece, dx, dy);
      if (next && shapeKey(next) === desiredKey) {
        lifted = { piece, direction, positions: next };
        break;
      }
    }
  }
  if (!lifted) throw new Error(`Cannot lift quotient edge ${edge.source} -> ${edge.target}`);
  concreteActions.push({ piece: lifted.piece, direction: lifted.direction });
  concrete = lifted.positions;
}

if (shapeKey(concrete) !== representative.key) {
  throw new Error('Lifted concrete endpoint does not match the representative shape');
}

const certificate = {
  generatorVersion,
  graphSha256,
  fullSpaceSha256,
  source: 'classic',
  componentId: classicId,
  representativeKey: representative.key,
  quotientTargetId: target.id,
  pathLength: concreteActions.length,
  actions: concreteActions,
  targetPositions: concrete,
  representativePositions: representative.positions
};

const output = path.join(root, 'frontend', 'classic-representative-path.json');
fs.writeFileSync(output, `${JSON.stringify(certificate, null, 2)}\n`, 'utf8');

const pieceNames = [
  'caoCao',
  'guanYu',
  'zhangFei',
  'zhaoYun',
  'maChao',
  'huangZhong',
  'soldier1',
  'soldier2',
  'soldier3',
  'soldier4'
];

function leanState(name, positions) {
  const values = positions.map(([x, y]) => `⟨${x}, ${y}⟩`).join(', ');
  return `def ${name} : State := ⟨#[${values}]⟩`;
}

const leanActions = concreteActions
  .map(action => `  ⟨.${pieceNames[action.piece]}, .${action.direction}⟩`)
  .join(',\n');

const lean = `import Huarongdao.Quotient

namespace Huarongdao
namespace ClassicRepresentativeCertificate

/-!
Generated by scripts/extract_classic_representative_path.mjs.

- generator version: ${generatorVersion}
- graph SHA-256: ${graphSha256}
- full-space SHA-256: ${fullSpaceSha256}
- component id: ${classicId}
- quotient target node: ${target.id}
- representative key: ${representative.key}
-/

${leanState('classicComponentRepresentativeState', representative.positions)}

${leanState('classicRepresentativeLiftedTarget', concrete)}

def classicRepresentativeActions : List Action := [
${leanActions}
]

def certificateClaims : Prop :=
  classicRepresentativeActions.length = ${concreteActions.length} ∧
  runMoves classic classicRepresentativeActions =
    some classicRepresentativeLiftedTarget ∧
  SameShape classicRepresentativeLiftedTarget
    classicComponentRepresentativeState ∧
  ValidState classicComponentRepresentativeState

instance certificateClaimsDecidable : Decidable certificateClaims := by
  unfold certificateClaims
  letI : Decidable (ValidState classicComponentRepresentativeState) := by
    unfold ValidState
    infer_instance
  infer_instance

theorem certificate_checked : certificateClaims := by
  set_option maxRecDepth 100000 in
  native_decide

theorem classicRepresentativeActions_length :
    classicRepresentativeActions.length = ${concreteActions.length} :=
  certificate_checked.1

theorem classicRepresentative_run_checked :
    runMoves classic classicRepresentativeActions =
      some classicRepresentativeLiftedTarget :=
  certificate_checked.2.1

theorem classicRepresentative_shape_checked :
    SameShape classicRepresentativeLiftedTarget
      classicComponentRepresentativeState :=
  certificate_checked.2.2.1

theorem classicComponentRepresentative_valid :
    ValidState classicComponentRepresentativeState :=
  certificate_checked.2.2.2

def classicComponentRepresentativeShapeState : ShapeState :=
  ShapeState.ofState
    ⟨classicComponentRepresentativeState,
      classicComponentRepresentative_valid⟩

/-- The displayed DFS representative of component #${classicId} is reachable
from the traditional layout by ${concreteActions.length} legal single-cell slides. -/
private def validWalkOfPath
    (path : Path source target) (sourceValid : ValidState source) :
    validClassicTask.Walk
      ⟨source, sourceValid⟩
      ⟨target, path.target_valid sourceValid⟩ :=
  match path with
  | .nil _ => .nil _
  | .cons action executed tail =>
      let middleValid := tryMove_preserves_validity executed
      let middle : ValidClassicState := ⟨_, middleValid⟩
      have first :
          validClassicTask.step ⟨source, sourceValid⟩ action middle :=
        executed
      .cons action first (validWalkOfPath tail middleValid)

noncomputable def classicRepresentative_shapeWalk :
    shapeObservation.quotientTask.Walk
      (ShapeState.ofState ⟨classic, classic_valid⟩)
      classicComponentRepresentativeShapeState := by
  let path : Path classic classicRepresentativeLiftedTarget :=
    Path.ofRunMoves classicRepresentative_run_checked
  let concreteWalk := validWalkOfPath path classic_valid
  let quotientWalk :=
    StateSpace.Observation.QuotientWalk.ofWalk
      (observation := shapeObservation) concreteWalk
  have targetEq :
      ShapeState.ofState
          ⟨classicRepresentativeLiftedTarget,
            path.target_valid classic_valid⟩ =
        classicComponentRepresentativeShapeState := by
    apply ShapeState.ofState_eq
    exact classicRepresentative_shape_checked
  rw [← targetEq]
  exact quotientWalk.toTaskWalk

theorem classicRepresentative_shapeReachable :
    ShapeReachable
      (ShapeState.ofState ⟨classic, classic_valid⟩)
      classicComponentRepresentativeShapeState := by
  let path : Path classic classicRepresentativeLiftedTarget :=
    Path.ofRunMoves classicRepresentative_run_checked
  have projected := path.toShapeReachable classic_valid
  have targetEq :
      ShapeState.ofState
          ⟨classicRepresentativeLiftedTarget,
            path.target_valid classic_valid⟩ =
        classicComponentRepresentativeShapeState := by
    apply ShapeState.ofState_eq
    exact classicRepresentative_shape_checked
  rw [targetEq] at projected
  exact projected

end ClassicRepresentativeCertificate
end Huarongdao
`;

const leanOutput = path.join(
  root,
  'Huarongdao',
  'ClassicRepresentativeCertificate.lean'
);
fs.writeFileSync(leanOutput, lean, 'utf8');
console.log(`Wrote ${concreteActions.length} lifted moves to ${output}`);
console.log(`Wrote minimal Lean certificate to ${leanOutput}`);
