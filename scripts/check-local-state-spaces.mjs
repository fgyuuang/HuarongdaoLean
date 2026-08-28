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

const shape = read('graph.json');
const shapeLayout = read('layout.json');
const mirror = read('graph.mirror.json');
const mirrorLayout = read('layout.mirror.json');
const corridor = read('graph.corridor.json');
const corridorLayout = read('layout.corridor.json');

checkGraph('shape', shape, shapeLayout);
checkGraph('mirror', mirror, mirrorLayout);
checkGraph('corridor', corridor, corridorLayout);

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
console.log('local state-space files and expansion paths valid: true');
