import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';
import { computeStructuralLayout } from '../frontend/structural-layout-worker.js';
import {
  buildVisualStateSpace,
  createNodeClickHandler
} from '../frontend/state-space-visualization.js';

const root = dirname(dirname(fileURLToPath(import.meta.url)));
const solver = join(root, '.lake', 'build', 'bin', 'solve-puzzle.exe');

function solve(args) {
  return JSON.parse(execFileSync(solver, args.map(String), {
    encoding: 'utf8',
    maxBuffer: 64 * 1024 * 1024
  }));
}

function assertFiniteAndDeterministic(name, input, options = {}) {
  const first = computeStructuralLayout(input);
  const second = computeStructuralLayout(input);
  if (first.coordinates.length !== input.nodes.length * 3) {
    throw new Error(`${name}: coordinate count does not match graph nodes`);
  }
  for (let index = 0; index < first.coordinates.length; index++) {
    if (!Number.isFinite(first.coordinates[index])) {
      throw new Error(`${name}: layout contains a non-finite coordinate`);
    }
    if (first.coordinates[index] !== second.coordinates[index]) {
      throw new Error(`${name}: layout is not deterministic`);
    }
  }
  if (!(first.meta.edgeMean > 0) || !(first.meta.edgeDeviation >= 0) ||
      !(first.meta.edgeMax >= first.meta.edgeMean)) {
    throw new Error(`${name}: layout metrics are invalid`);
  }
  if (options.maxMirrorError != null &&
      Math.max(first.meta.mirrorXError, first.meta.mirrorYError) > options.maxMirrorError) {
    throw new Error(`${name}: mirror error is too large`);
  }
  return first;
}

const tinyResult = solve([
  3, 2, 1000, 20, 2,
  1, 1, 0, 0, 2, 0,
  1, 1, 1, 0, '*', '*',
  'bfs'
]);
const tiny = assertFiniteAndDeterministic('tiny', {
  board: { width: 3, height: 2 },
  shapes: [{ width: 1, height: 1 }, { width: 1, height: 1 }],
  nodes: tinyResult.graph.nodes,
  edges: tinyResult.graph.edges
}, { maxMirrorError: 0.6 });

const gateResult = solve([
  4, 4, 100000, 500, 3,
  2, 2, 0, 0, 2, 2,
  1, 2, 2, 0, '*', '*',
  1, 1, 3, 0, '*', '*',
  'bfs'
]);
const gate = assertFiniteAndDeterministic('gate', {
  board: { width: 4, height: 4 },
  shapes: [{ width: 2, height: 2 }, { width: 1, height: 2 }, { width: 1, height: 1 }],
  nodes: gateResult.graph.nodes,
  edges: gateResult.graph.edges
}, { maxMirrorError: 0.6 });
if (gate.meta.nodeCount !== 660 || gate.meta.edgeCount !== 1802) {
  throw new Error('gate: complete state graph size changed');
}

const gridWidth = 45;
const gridHeight = 36;
const gridNodes = [];
const gridEdges = [];
for (let y = 0; y < gridHeight; y++) {
  for (let x = 0; x < gridWidth; x++) {
    const id = y * gridWidth + x;
    gridNodes.push({ id, distance: x + y, positions: [{ x, y }] });
    if (x > 0) gridEdges.push({ source: id - 1, target: id });
    if (y > 0) gridEdges.push({ source: id - gridWidth, target: id });
  }
}
const binned = assertFiniteAndDeterministic('binned-grid', {
  board: { width: gridWidth, height: gridHeight },
  shapes: [{ width: 1, height: 1 }],
  nodes: gridNodes,
  edges: gridEdges
}, { maxMirrorError: 0.8 });

const labelled = assertFiniteAndDeterministic('labelled-generic-graph', {
  startId: 'goal',
  nodes: [
    { id: 'start' },
    { id: 'upper' },
    { id: 'lower' },
    { id: 'goal' }
  ],
  edges: [
    { source: 'start', target: 'upper' },
    { source: { id: 'start' }, target: { id: 'lower' } },
    { source: 'upper', target: 'goal' },
    { source: 'lower', target: 'goal' }
  ]
});
if (labelled.meta.edgeCount !== 4 || labelled.meta.mirrorXPairs !== 0 ||
    labelled.meta.mirrorYPairs !== 0 || labelled.meta.startIndex !== 3) {
  throw new Error('labelled-generic-graph: generic input normalization changed');
}

const labelledInput = {
  startId: 'goal',
  nodes: [
    { id: 'start', label: 'Start' },
    { id: 'upper', label: 'Upper' },
    { id: 'lower', label: 'Lower' },
    { id: 'goal', label: 'Goal' }
  ],
  edges: [
    { source: 'start', target: 'upper', action: 'up' },
    { source: { id: 'start' }, target: { id: 'lower' }, action: 'down' },
    { source: 'upper', target: 'goal', action: 'finish-upper' },
    { source: 'lower', target: 'goal', action: 'finish-lower' }
  ]
};
const visual = buildVisualStateSpace(labelledInput, labelled);
let clicked = null;
const click = createNodeClickHandler(visual, payload => { clicked = payload; });
click({ id: 'start' }, { type: 'test-click' });
if (clicked?.id !== 'start' || clicked.outgoing.length !== 2 ||
    clicked.neighbors.length !== 2 || clicked.event.type !== 'test-click' ||
    visual.startId !== 'goal') {
  throw new Error('labelled-generic-graph: click interaction contract changed');
}

console.log(
  `layout: ok (tiny ${tiny.meta.nodeCount}, gate ${gate.meta.nodeCount}, ` +
  `binned ${binned.meta.nodeCount}, labelled ${labelled.meta.nodeCount}; gate mirror ` +
  `${gate.meta.mirrorXError.toFixed(3)}/${gate.meta.mirrorYError.toFixed(3)})`
);
