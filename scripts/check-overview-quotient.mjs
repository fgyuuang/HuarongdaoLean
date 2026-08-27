import fs from 'node:fs';
import { buildOverviewGraphs, sameShapeKey, mirrorPositions } from '../frontend/overview-quotient.js';

const graph = JSON.parse(fs.readFileSync(new URL('../frontend/graph.json', import.meta.url), 'utf8'));
const { quotient, skeleton } = buildOverviewGraphs(graph);

function assert(condition, message) {
  if (!condition) throw new Error(message);
}

assert(quotient.orbitByState.length === graph.states.length, 'Not every concrete state has an orbit');
const stateByKey = new Map(graph.states.map(state => [state.key, state]));
for (const state of graph.states) {
  const orbit = quotient.nodes[quotient.orbitByState[state.id]];
  assert(orbit.members.includes(state.id), `Orbit membership missing for #${state.id}`);
  const mirrorKey = sameShapeKey(mirrorPositions(state.positions));
  const mirror = stateByKey.get(mirrorKey);
  assert(mirror, `Mirror state missing for #${state.id}`);
  assert(sameShapeKey(mirrorPositions(mirror.positions)) === state.key, `Mirror is not involutive for #${state.id}`);
  assert(mirror.goal === state.goal, `Mirror does not preserve goal for #${state.id}`);
  assert(quotient.orbitByState[state.id] === quotient.orbitByState[mirror.id], `Mirror orbit mismatch for #${state.id}`);
}
for (const orbit of quotient.nodes) assert(orbit.members.length <= 2, `Mirror orbit #${orbit.id} has more than two members`);

const quotientEdgeKeys = new Set();
for (const edge of quotient.edges) {
  assert(edge.source !== edge.target, `Quotient self-edge #${edge.id}`);
  const key = `${edge.source}:${edge.target}`;
  assert(!quotientEdgeKeys.has(key), `Duplicate quotient edge ${key}`);
  quotientEdgeKeys.add(key);
  const witnessSource = quotient.orbitByState[edge.witness.source];
  const witnessTarget = quotient.orbitByState[edge.witness.target];
  assert(
    (witnessSource === edge.source && witnessTarget === edge.target) ||
    (witnessSource === edge.target && witnessTarget === edge.source),
    `Invalid Lean edge witness for quotient edge #${edge.id}`
  );
}
for (const edge of graph.edges) {
  const source = quotient.orbitByState[edge.source];
  const target = quotient.orbitByState[edge.target];
  if (source === target) continue;
  const key = source < target ? `${source}:${target}` : `${target}:${source}`;
  assert(quotientEdgeKeys.has(key), `Concrete edge #${edge.source} -> #${edge.target} is absent from quotient`);
}

const coveredEdges = new Set();
for (const edge of skeleton.edges) {
  assert(edge.weight === edge.edgePath.length, `Wrong weight on skeleton edge #${edge.id}`);
  assert(edge.nodePath.length === edge.edgePath.length + 1, `Broken path on skeleton edge #${edge.id}`);
  assert(edge.nodePath[0] === edge.source && edge.nodePath.at(-1) === edge.target, `Wrong endpoints on skeleton edge #${edge.id}`);
  edge.edgePath.forEach((edgeId, index) => {
    assert(!coveredEdges.has(edgeId), `Quotient edge #${edgeId} covered twice`);
    coveredEdges.add(edgeId);
    const quotientEdge = quotient.edges[edgeId];
    const a = edge.nodePath[index], b = edge.nodePath[index + 1];
    assert(
      (quotientEdge.source === a && quotientEdge.target === b) ||
      (quotientEdge.source === b && quotientEdge.target === a),
      `Skeleton edge #${edge.id} is not contiguous at step ${index}`
    );
  });
}
assert(coveredEdges.size === quotient.edges.length, 'Skeleton does not cover every quotient edge');
for (let orbit = 0; orbit < quotient.nodes.length; orbit += 1) {
  assert(skeleton.locationByOrbit[orbit], `Quotient node #${orbit} has no skeleton location`);
  if (!skeleton.isAnchor[orbit]) assert(quotient.adjacency[orbit].length === 2, `Compressed node #${orbit} is not degree 2`);
  if (quotient.nodes[orbit].containsInitial || quotient.nodes[orbit].goal) {
    assert(skeleton.locationByOrbit[orbit].type === 'node', `Protected node #${orbit} was compressed`);
  }
}

console.log(`states=${graph.states.length}`);
console.log(`mirror-orbits=${quotient.nodes.length}, fixed=${quotient.fixedCount}, edges=${quotient.edges.length}`);
console.log(`skeleton-nodes=${skeleton.nodes.length}, weighted-edges=${skeleton.edges.length}`);
console.log(`compressed-degree-2=${skeleton.compressedNodeCount}, longest-corridor=${skeleton.longestCorridor}`);
console.log('all quotient witnesses and skeleton paths valid: true');
