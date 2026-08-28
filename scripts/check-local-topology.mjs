import fs from 'node:fs';
import assert from 'node:assert/strict';
import { analyzeLocalTopology } from '../frontend/local-topology.js';

function rankOverF2(rows, width) {
  const matrix = [...rows];
  let rank = 0;
  for (let column = 0; column < width; column += 1) {
    const bit = 1n << BigInt(column);
    const pivot = matrix.findIndex((row, index) => index >= rank && (row & bit));
    if (pivot < 0) continue;
    [matrix[rank], matrix[pivot]] = [matrix[pivot], matrix[rank]];
    for (let index = 0; index < matrix.length; index += 1) {
      if (index !== rank && (matrix[index] & bit)) matrix[index] ^= matrix[rank];
    }
    rank += 1;
  }
  return rank;
}

function mirrorKey(positions) {
  const widths = [2, 2, 1, 1, 1, 1, 1, 1, 1, 1];
  const mirrored = positions.map(([x, y], piece) => [3 - (x + widths[piece] - 1), y]);
  const code = ([x, y]) => x + 4 * y;
  return `${code(mirrored[0])};${code(mirrored[1])};` +
    `${[2, 3, 4, 5].map(piece => code(mirrored[piece])).sort((a, b) => a - b)};` +
    `${[6, 7, 8, 9].map(piece => code(mirrored[piece])).sort((a, b) => a - b)}`;
}

for (const name of ['graph.json', 'graph.mirror.json', 'graph.corridor.json']) {
  const graph = JSON.parse(fs.readFileSync(new URL(`../frontend/${name}`, import.meta.url), 'utf8'));
  const labelledEdges = new Set(graph.edges.map(edge =>
    `${edge.source}|${edge.piece}:${edge.direction}|${edge.target}`));
  const actionTargets = new Map(graph.edges.map(edge =>
    [`${edge.source}|${edge.piece}:${edge.direction}`, edge.target]));
  assert.equal(graph.states.every((state, id) => state.id === id), true, `${name}: dense ids`);
  const result = analyzeLocalTopology(graph);
  assert.equal(result.nodes.length, graph.states.length);
  for (const [id, node] of result.nodes.entries()) {
    assert.equal(node.squareCount, node.commutingPairs.length);
    assert.ok(node.localDimension <= node.degree, `${name} #${id}: dimension bound`);
    for (const square of node.commutingPairs) {
      const afterA = actionTargets.get(`${id}|${square.a}`);
      const afterB = actionTargets.get(`${id}|${square.b}`);
      assert.ok(afterA !== undefined && afterB !== undefined, `${name} #${id}: square starts`);
      assert.ok(labelledEdges.has(`${afterA}|${square.b}|${square.target}`), `${name} #${id}: a then b`);
      assert.ok(labelledEdges.has(`${afterB}|${square.a}|${square.target}`), `${name} #${id}: b then a`);
    }
  }
  if (name === 'graph.json') {
    const sample = result.nodes[1409];
    assert.deepEqual({
      degree: sample.degree,
      radius2Nodes: sample.radius2Nodes,
      radius2Edges: sample.radius2Edges,
      squareCount: sample.squareCount,
      linkComponents: sample.linkComponents,
      localDimension: sample.localDimension,
      localCutComponents: sample.localCutComponents
    }, {
      degree: 5,
      radius2Nodes: 18,
      radius2Edges: 23,
      squareCount: 4,
      linkComponents: 2,
      localDimension: 2,
      localCutComponents: 2
    }, 'graph.json #1409 remains the representative local-topology sample');

    const center = 1409;
    const neighbors = Array.from({ length: graph.states.length }, () => new Set());
    for (const edge of graph.edges) {
      neighbors[edge.source].add(edge.target);
      neighbors[edge.target].add(edge.source);
    }
    const ring1 = [...neighbors[center]];
    const localIds = new Set([center, ...ring1]);
    for (const id of ring1) for (const next of neighbors[id]) localIds.add(next);
    const localEdges = [...new Set(graph.edges.map(edge =>
      edge.source < edge.target ? `${edge.source}:${edge.target}` : `${edge.target}:${edge.source}`))]
      .filter(key => key.split(':').every(id => localIds.has(Number(id))));
    const edgeIndex = new Map(localEdges.map((key, index) => [key, index]));
    const squareRows = sample.commutingPairs.map(square => {
      const afterA = actionTargets.get(`${center}|${square.a}`);
      const afterB = actionTargets.get(`${center}|${square.b}`);
      const boundary = [[center, afterA], [afterA, square.target],
        [square.target, afterB], [afterB, center]];
      return boundary.reduce((row, [a, b]) => {
        const key = a < b ? `${a}:${b}` : `${b}:${a}`;
        return row ^ (1n << BigInt(edgeIndex.get(key)));
      }, 0n);
    });
    const boundaryRank = rankOverF2(squareRows, localEdges.length);
    const betti = [1, localEdges.length - (localIds.size - 1) - boundaryRank,
      squareRows.length - boundaryRank];
    assert.deepEqual(betti, [1, 2, 0], 'sample F2 Betti numbers');
    assert.equal(localIds.size - localEdges.length + squareRows.length, -1, 'sample Euler characteristic');

    const expectedLinkEdges = new Set(['4:下|7:右', '4:下|8:上', '7:右|9:右', '8:上|9:右']);
    assert.deepEqual(new Set(sample.commutingPairs.map(pair => `${pair.a}|${pair.b}`)), expectedLinkEdges,
      'sample action link is C4');
    assert.equal(sample.commutingPairs.some(pair => pair.a === '5:左' || pair.b === '5:左'), false,
      'Huang Zhong left is isolated in the action link');
    assert.equal(graph.states.find(state => state.key === mirrorKey(graph.states[center].positions))?.id, 1442,
      'sample mirror is exported node #1442');

    const bypass = [1261, 1329, 1408];
    assert.equal(bypass.every(id => !localIds.has(id) || id !== center), true);
    for (let index = 0; index + 1 < bypass.length; index += 1) {
      assert.ok(neighbors[bypass[index]].has(bypass[index + 1]), 'full-graph bypass edge exists');
    }
    console.log('sample #1409: Link=C4+point, chi=-1, betti=(1,2,0), mirror=#1442, bypass=1261-1329-1408');
  }
  console.log(`${name}: nodes=${result.summary.nodeCount}, undirectedEdges=${result.summary.edgeCount}, squareIncidences=${result.summary.squareIncidences}, localBottlenecks=${result.summary.bottleneckCount}`);
}
