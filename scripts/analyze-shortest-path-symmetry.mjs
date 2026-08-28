import { readFile } from 'node:fs/promises';

const pieceWidths = [2, 2, 1, 1, 1, 1, 1, 1, 1, 1];
const interchangeableGroups = [[2, 3, 4, 5], [6, 7, 8, 9]];

function canonicalPositions(positions) {
  const result = positions.map(position => [...position]);
  for (const group of interchangeableGroups) {
    const sorted = group.map(piece => result[piece]).sort((a, b) => a[0] - b[0] || a[1] - b[1]);
    group.forEach((piece, index) => { result[piece] = sorted[index]; });
  }
  return result;
}

function stateKey(positions) {
  const code = position => position[0] + 4 * position[1];
  const verticals = interchangeableGroups[0].map(piece => code(positions[piece])).sort((a, b) => a - b);
  const soldiers = interchangeableGroups[1].map(piece => code(positions[piece])).sort((a, b) => a - b);
  return `${code(positions[0])};${code(positions[1])};${verticals.join(',')};${soldiers.join(',')}`;
}

function mirrorKey(positions) {
  const mirrored = positions.map((position, piece) => [
    3 - (position[0] + pieceWidths[piece] - 1),
    position[1]
  ]);
  return stateKey(canonicalPositions(mirrored));
}

function countShortestNodePaths(graph, allowed = () => true) {
  const shortestDistance = Math.min(...graph.states.filter(state => state.goal).map(state => state.distance));
  const outgoing = Array.from({ length: graph.states.length }, () => []);
  for (const edge of graph.edges) outgoing[edge.source].push(edge.target);

  const ways = Array(graph.states.length).fill(0n);
  if (allowed(graph.meta.initial)) ways[graph.meta.initial] = 1n;
  const ordered = [...graph.states].sort((a, b) => a.distance - b.distance || a.id - b.id);
  for (const state of ordered) {
    if (!allowed(state.id) || ways[state.id] === 0n) continue;
    const distinctTargets = new Set(outgoing[state.id]);
    for (const target of distinctTargets) {
      const targetState = graph.states[target];
      if (allowed(target) && targetState.distance === state.distance + 1 && targetState.distance <= shortestDistance) {
        ways[target] += ways[state.id];
      }
    }
  }
  const shortestGoals = graph.states.filter(state => state.goal && state.distance === shortestDistance);
  return {
    shortestDistance,
    shortestGoalStates: shortestGoals.length,
    paths: shortestGoals.reduce((total, state) => total + ways[state.id], 0n)
  };
}

const [shapeGraph, mirrorGraph] = await Promise.all([
  readFile(new URL('../frontend/graph.json', import.meta.url), 'utf8').then(JSON.parse),
  readFile(new URL('../frontend/graph.mirror.json', import.meta.url), 'utf8').then(JSON.parse)
]);

const shape = countShortestNodePaths(shapeGraph);
const mirror = countShortestNodePaths(mirrorGraph);
const idByKey = new Map(shapeGraph.states.map(state => [state.key, state.id]));
const mirrorPartner = shapeGraph.states.map(state => idByKey.get(mirrorKey(state.positions)));
if (mirrorPartner.some(partner => partner === undefined)) throw new Error('A mirrored shape state is missing');
const fixedState = mirrorPartner.map((partner, id) => partner === id);
const fixed = countShortestNodePaths(shapeGraph, id => fixedState[id]);
const globalMirrorOrbits = (shape.paths + fixed.paths) / 2n;

const format = value => value.toLocaleString('en-US');
console.log('Shortest-path symmetry analysis (node sequences; parallel action labels deduplicated)');
console.log(`same-shape quotient: distance ${shape.shortestDistance}, ${format(shape.paths)} shortest paths, ${shape.shortestGoalStates} shortest goal states`);
console.log(`global left-right mirror orbits: ${format(globalMirrorOrbits)} (${format(fixed.paths)} mirror-fixed shortest paths)`);
console.log(`pointwise mirror quotient: distance ${mirror.shortestDistance}, ${format(mirror.paths)} shortest paths, ${mirror.shortestGoalStates} shortest goal state`);
console.log(`unique modulo left-right reflection: ${globalMirrorOrbits === 1n ? 'yes' : 'no'}`);
