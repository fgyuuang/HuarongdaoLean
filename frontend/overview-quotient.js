const BOARD_WIDTH = 4;
const PIECE_WIDTHS = [2, 2, 1, 1, 1, 1, 1, 1, 1, 1];
const VERTICAL_PIECES = [2, 3, 4, 5];
const SOLDIER_PIECES = [6, 7, 8, 9];

function cellIndex([x, y]) {
  return x + BOARD_WIDTH * y;
}

function sortedCells(positions, indices) {
  return indices.map(index => cellIndex(positions[index])).sort((a, b) => a - b).join(',');
}

export function sameShapeKey(positions) {
  return [
    cellIndex(positions[0]),
    cellIndex(positions[1]),
    sortedCells(positions, VERTICAL_PIECES),
    sortedCells(positions, SOLDIER_PIECES)
  ].join(';');
}

export function mirrorPositions(positions) {
  return positions.map(([x, y], index) => [BOARD_WIDTH - PIECE_WIDTHS[index] - x, y]);
}

/**
 * Quotient the already SameShape-normalized Lean graph by horizontal mirror.
 * Every edge retains a concrete Lean edge as a witness.
 */
export function buildSymmetryQuotient(graphData) {
  const states = graphData.states;
  const stateByKey = new Map(states.map(state => [state.key, state.id]));
  const representativeByState = new Int32Array(states.length);

  for (const state of states) {
    if (sameShapeKey(state.positions) !== state.key) {
      throw new Error(`State #${state.id} does not match its SameShape key`);
    }
    const mirrorKey = sameShapeKey(mirrorPositions(state.positions));
    const mirrorId = stateByKey.get(mirrorKey);
    if (mirrorId === undefined) throw new Error(`Mirror of state #${state.id} is missing`);
    representativeByState[state.id] = Math.min(state.id, mirrorId);
  }

  const orbitByRepresentative = new Map();
  for (const state of states) {
    const representative = representativeByState[state.id];
    if (!orbitByRepresentative.has(representative)) orbitByRepresentative.set(representative, []);
    orbitByRepresentative.get(representative).push(state.id);
  }

  const nodes = [...orbitByRepresentative.entries()].map(([representative, members], id) => ({
    id,
    representative,
    members: members.sort((a, b) => a - b),
    fixed: members.length === 1,
    goal: members.some(stateId => states[stateId].goal),
    containsInitial: members.includes(graphData.meta.initial)
  }));
  const orbitByState = new Int32Array(states.length);
  for (const node of nodes) for (const stateId of node.members) orbitByState[stateId] = node.id;

  const edgeByKey = new Map();
  const concreteEdges = new Set();
  let internalTransitions = 0;
  for (const edge of graphData.edges) {
    const concreteKey = edge.source < edge.target
      ? `${edge.source}:${edge.target}`
      : `${edge.target}:${edge.source}`;
    if (concreteEdges.has(concreteKey)) continue;
    concreteEdges.add(concreteKey);
    const source = orbitByState[edge.source];
    const target = orbitByState[edge.target];
    if (source === target) {
      internalTransitions += 1;
      continue;
    }
    const key = source < target ? `${source}:${target}` : `${target}:${source}`;
    const existing = edgeByKey.get(key);
    if (existing) {
      existing.multiplicity += 1;
    } else {
      edgeByKey.set(key, {
        id: edgeByKey.size,
        source: Math.min(source, target),
        target: Math.max(source, target),
        multiplicity: 1,
        witness: edge
      });
    }
  }

  const edges = [...edgeByKey.values()];
  const adjacency = Array.from({ length: nodes.length }, () => []);
  for (const edge of edges) {
    adjacency[edge.source].push(edge.id);
    adjacency[edge.target].push(edge.id);
  }

  return {
    nodes,
    edges,
    adjacency,
    orbitByState,
    representativeByState,
    internalTransitions,
    fixedCount: nodes.filter(node => node.fixed).length
  };
}

function otherEndpoint(edge, node) {
  return edge.source === node ? edge.target : edge.source;
}

/**
 * Contract maximal degree-2 corridors into weighted edges. Corridor states are
 * not declared equivalent: each weighted edge keeps the exact node/edge path.
 */
export function buildPathSkeleton(quotient) {
  const { nodes, edges, adjacency } = quotient;
  const isAnchor = nodes.map((node, id) =>
    adjacency[id].length !== 2 || node.containsInitial || node.goal
  );
  const visitedEdges = new Uint8Array(edges.length);
  const skeletonNodes = nodes.filter((_, id) => isAnchor[id]);
  const skeletonEdges = [];
  const locationByOrbit = Array(nodes.length).fill(null);
  for (const node of skeletonNodes) locationByOrbit[node.id] = { type: 'node', node: node.id };

  function walkCorridor(start, firstEdge) {
    const nodePath = [start];
    const edgePath = [];
    let current = start;
    let edgeId = firstEdge;

    while (true) {
      if (visitedEdges[edgeId]) return;
      visitedEdges[edgeId] = 1;
      edgePath.push(edgeId);
      current = otherEndpoint(edges[edgeId], current);
      nodePath.push(current);
      if (isAnchor[current]) break;
      const nextEdge = adjacency[current][0] === edgeId ? adjacency[current][1] : adjacency[current][0];
      if (nextEdge === undefined || visitedEdges[nextEdge]) break;
      edgeId = nextEdge;
    }

    const id = skeletonEdges.length;
    const skeletonEdge = {
      id,
      source: nodePath[0],
      target: nodePath.at(-1),
      weight: edgePath.length,
      nodePath,
      edgePath
    };
    skeletonEdges.push(skeletonEdge);
    for (let index = 1; index < nodePath.length - 1; index += 1) {
      locationByOrbit[nodePath[index]] = {
        type: 'edge',
        edge: id,
        index,
        ratio: index / (nodePath.length - 1)
      };
    }
  }

  for (const node of skeletonNodes) {
    for (const edgeId of adjacency[node.id]) {
      if (!visitedEdges[edgeId]) walkCorridor(node.id, edgeId);
    }
  }

  // A disconnected all-degree-2 component has no natural anchor. Preserve one
  // node so its cycle remains represented instead of silently disappearing.
  for (const edge of edges) {
    if (visitedEdges[edge.id]) continue;
    const fallback = edge.source;
    if (!isAnchor[fallback]) {
      isAnchor[fallback] = true;
      skeletonNodes.push(nodes[fallback]);
      locationByOrbit[fallback] = { type: 'node', node: fallback };
    }
    walkCorridor(fallback, edge.id);
  }

  return {
    nodes: skeletonNodes,
    edges: skeletonEdges,
    isAnchor,
    locationByOrbit,
    compressedNodeCount: nodes.length - skeletonNodes.length,
    longestCorridor: Math.max(0, ...skeletonEdges.map(edge => edge.weight))
  };
}

export function buildOverviewGraphs(graphData) {
  const quotient = buildSymmetryQuotient(graphData);
  const skeleton = buildPathSkeleton(quotient);
  return { quotient, skeleton };
}
