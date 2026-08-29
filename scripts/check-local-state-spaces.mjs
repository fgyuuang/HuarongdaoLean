import fs from 'node:fs';

function read(name) {
  return JSON.parse(fs.readFileSync(new URL(`../frontend/${name}`, import.meta.url), 'utf8'));
}

function assert(condition, message) {
  if (!condition) throw new Error(message);
}

function checkGraph(name, graph, layout) {
  assert(graph.meta.stateCount === graph.states.length, `${name}: state count mismatch`);
  assert(graph.meta.edgeCount === graph.edges.length, `${name}: edge count mismatch`);
  assert(layout.coordinates.length === graph.states.length, `${name}: layout count mismatch`);
  assert(graph.states.every((state, id) => state.id === id), `${name}: state ids are not dense`);
  assert(graph.edges.every(edge =>
    Number.isInteger(edge.source) && Number.isInteger(edge.target) &&
    edge.source >= 0 && edge.source < graph.states.length &&
    edge.target >= 0 && edge.target < graph.states.length
  ), `${name}: edge endpoint out of range`);
}

function caoPositionKey(state, mirrorInvariant) {
  const [x, y] = state.positions[0];
  return `${mirrorInvariant ? Math.min(x, 2 - x) : x},${y}`;
}

function checkCaoProjection(name, graph, mirrorInvariant, expectedGroupCount) {
  const keys = graph.states.map(state => caoPositionKey(state, mirrorInvariant));
  assert(new Set(keys).size === expectedGroupCount,
    `${name}: unexpected Cao Cao position-group count`);
  for (const [id, edge] of graph.edges.entries()) {
    if (keys[edge.source] === keys[edge.target]) continue;
    const steps = edge.steps?.length ? edge.steps : [edge];
    assert(steps.some(step => step.piece === 0),
      `${name}: edge #${id} changes Cao Cao group without moving Cao Cao`);
  }
}

function checkExactCaoClassAdjacency(graph) {
  const keys = graph.states.map(state => caoPositionKey(state, false));
  const positionKeys = [...new Set(keys)];
  const neighbors = new Set();
  for (const left of positionKeys) {
    const [lx, ly] = left.split(',').map(Number);
    for (const right of positionKeys) {
      const [rx, ry] = right.split(',').map(Number);
      if (Math.abs(lx - rx) + Math.abs(ly - ry) !== 1) continue;
      neighbors.add([left, right].sort().join('|'));
    }
  }
  const witnesses = new Map();
  for (const edge of graph.edges) {
    const sourceGroup = keys[edge.source], targetGroup = keys[edge.target];
    if (sourceGroup === targetGroup) continue;
    const steps = edge.steps?.length ? edge.steps : [edge];
    if (steps.length !== 1 || steps[0].piece !== 0) continue;
    const pair = [sourceGroup, targetGroup].sort().join('|');
    if (!witnesses.has(pair)) witnesses.set(pair, { edge, sourceGroup, targetGroup, step: steps[0] });
  }
  assert(witnesses.size === neighbors.size,
    `shape: projected Cao adjacency count ${witnesses.size} != geometric neighbor count ${neighbors.size}`);
  for (const pair of neighbors) assert(witnesses.has(pair), `shape: missing one-step Cao witness for ${pair}`);
  for (const pair of witnesses.keys()) assert(neighbors.has(pair), `shape: extra projected Cao pair ${pair}`);
  return [...neighbors].sort().map(pair => ({ pair, ...witnesses.get(pair) }));
}

const shape = read('graph.json');
const shapeLayout = read('layout.json');
const mirror = read('graph.mirror.json');
const mirrorLayout = read('layout.mirror.json');
const corridor = read('graph.corridor.json');
const corridorLayout = read('layout.corridor.json');

checkGraph('shape', shape, shapeLayout);
checkGraph('mirror', mirror, mirrorLayout);
checkGraph('corridor', corridor, corridorLayout);
checkCaoProjection('shape', shape, false, 12);
checkCaoProjection('mirror', mirror, true, 8);
checkCaoProjection('corridor', corridor, true, 8);
const caoExactWitnesses = checkExactCaoClassAdjacency(shape);

assert(mirror.meta.quotient?.symmetry === 'horizontal_mirror', 'mirror: quotient metadata missing');
assert(mirror.meta.verified === true, 'mirror: Lean verification metadata missing');
assert(mirror.meta.edgeIntegrity === 'sound_and_complete', 'mirror: edge integrity metadata missing');
assert(mirror.meta.quotient.originalStateCount === shape.states.length, 'mirror: parent state count mismatch');
assert(mirror.meta.quotient.originalEdgeCount === shape.edges.length, 'mirror: parent edge count mismatch');
assert(mirrorLayout.mirrorPairs?.length === mirror.states.length, 'mirror: mirror-pair layout missing');

assert(corridor.meta.stateSpace === 'forced_corridor', 'corridor: state-space metadata missing');
assert(corridor.meta.verified === true, 'corridor: Lean verification metadata missing');
assert(corridor.meta.parentAdjacencyIntegrity === 'sound_and_complete',
  'corridor: parent adjacency integrity metadata missing');
assert(corridor.meta.parentEdgeLabelPolicy === 'one_representative_per_directed_adjacency',
  'corridor: parallel-edge policy metadata missing');
assert(corridor.meta.parentStateCount === mirror.states.length, 'corridor: parent state count mismatch');
assert(corridor.meta.parentEdgeCount === mirror.edges.length, 'corridor: parent edge count mismatch');
const mirrorDirectedAdjacencyKeys = new Set(
  mirror.edges.map(edge => `${edge.source}:${edge.target}`));
assert(corridor.meta.parentDirectedAdjacencyCount === mirrorDirectedAdjacencyKeys.size,
  'corridor: parent directed adjacency count mismatch');
assert(corridor.meta.parentParallelEdgeCount ===
  corridor.meta.parentEdgeCount - corridor.meta.parentDirectedAdjacencyCount,
  'corridor: parent parallel edge count mismatch');
assert(corridor.meta.suppressedStateCount === mirror.states.length - corridor.states.length,
  'corridor: suppressed state count mismatch');
const corridorDirectedAdjacencyCounts = new Map();
for (const [id, edge] of corridor.edges.entries()) {
  assert(edge.weight === edge.steps.length, `corridor edge #${id}: weight/steps mismatch`);
  assert(edge.path.length === edge.steps.length + 1, `corridor edge #${id}: path length mismatch`);
  assert(edge.path[0] === corridor.states[edge.source].mirrorId,
    `corridor edge #${id}: source anchor mismatch`);
  assert(edge.path.at(-1) === corridor.states[edge.target].mirrorId,
    `corridor edge #${id}: target anchor mismatch`);
  edge.steps.forEach((step, index) => {
    assert(step.source === edge.path[index] && step.target === edge.path[index + 1],
      `corridor edge #${id}: non-contiguous step ${index}`);
    const key = `${step.source}:${step.target}`;
    corridorDirectedAdjacencyCounts.set(key,
      (corridorDirectedAdjacencyCounts.get(key) || 0) + 1);
  });
}
assert(corridorDirectedAdjacencyCounts.size === mirrorDirectedAdjacencyKeys.size,
  'corridor: directed adjacency coverage size mismatch');
for (const key of mirrorDirectedAdjacencyKeys) {
  assert(corridorDirectedAdjacencyCounts.get(key) === 1,
    `corridor: directed adjacency not covered exactly once: ${key}`);
}
for (const key of corridorDirectedAdjacencyCounts.keys()) {
  assert(mirrorDirectedAdjacencyKeys.has(key),
    `corridor: foreign directed adjacency: ${key}`);
}

console.log(`shape=${shape.states.length} states, ${shape.edges.length} directed edges`);
console.log(`mirror=${mirror.states.length} states, ${mirror.edges.length} directed edges`);
console.log(`corridor=${corridor.states.length} anchors, ${corridor.edges.length} directed macro edges`);
console.log(`corridor shortest=${corridor.meta.primitiveShortestGoalDistance} primitive steps / ${corridor.meta.operationShortestGoalDistance} macro operations`);
console.log('Cao Cao groups=12 exact / 8 mirror / 8 corridor; changing edges contain a Cao Cao step');
console.log(`exact Cao Cao class neighbors=${caoExactWitnesses.length}; every pair has a concrete one-step witness`);
for (const { pair, edge, step } of caoExactWitnesses) {
  console.log(`  ${pair}: #${edge.source} -> #${edge.target} (${step.direction})`);
}
console.log('local state-space files and expansion paths valid: true');
