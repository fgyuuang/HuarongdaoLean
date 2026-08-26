import { computeStructuralLayout } from './structural-layout-worker.js';

function endpointKey(value) {
  return typeof value === 'object' && value !== null ? value.id : value;
}

function nodeId(node, index) {
  return node.id ?? index;
}

function resolveIndex(byId, nodeCount, value) {
  const key = endpointKey(value);
  if (byId.has(key)) return byId.get(key);
  return Number.isInteger(key) && key >= 0 && key < nodeCount ? key : -1;
}

function rootDistances(startIndex, outgoing, incoming) {
  const distances = new Int32Array(outgoing.length);
  distances.fill(-1);
  if (!outgoing.length) return distances;
  const queue = new Int32Array(outgoing.length);
  let head = 0;
  let tail = 1;
  queue[0] = startIndex;
  distances[startIndex] = 0;
  while (head < tail) {
    const source = queue[head++];
    for (const edge of [...outgoing[source], ...incoming[source]]) {
      const target = edge.sourceIndex === source ? edge.targetIndex : edge.sourceIndex;
      if (distances[target] >= 0) continue;
      distances[target] = distances[source] + 1;
      queue[tail++] = target;
    }
  }
  return distances;
}

export function buildVisualStateSpace(input, layoutResult) {
  const sourceNodes = input.nodes || [];
  const coordinates = layoutResult.coordinates;
  if (!coordinates || coordinates.length !== sourceNodes.length * 3) {
    throw new Error('layout coordinate count does not match state-space nodes');
  }

  const byId = new Map();
  sourceNodes.forEach((node, index) => {
    const id = nodeId(node, index);
    if (byId.has(id)) throw new Error(`duplicate state-space node id: ${String(id)}`);
    byId.set(id, index);
  });

  const outgoing = Array.from({ length: sourceNodes.length }, () => []);
  const incoming = Array.from({ length: sourceNodes.length }, () => []);
  const edges = [];
  for (const [edgeIndex, edge] of (input.edges || []).entries()) {
    const sourceIndex = resolveIndex(byId, sourceNodes.length, edge.source);
    const targetIndex = resolveIndex(byId, sourceNodes.length, edge.target);
    if (sourceIndex < 0 || targetIndex < 0) {
      throw new Error(`edge ${edgeIndex} refers to an unknown node`);
    }
    const visualEdge = {
      ...edge,
      index: edgeIndex,
      source: nodeId(sourceNodes[sourceIndex], sourceIndex),
      target: nodeId(sourceNodes[targetIndex], targetIndex),
      sourceIndex,
      targetIndex,
      raw: edge
    };
    edges.push(visualEdge);
    outgoing[sourceIndex].push(visualEdge);
    incoming[targetIndex].push(visualEdge);
  }

  const startIndex = resolveIndex(
    byId,
    sourceNodes.length,
    input.startId ?? nodeId(sourceNodes[0] || {}, 0)
  );
  const distances = rootDistances(Math.max(0, startIndex), outgoing, incoming);
  const nodes = sourceNodes.map((node, index) => {
    const x = coordinates[index * 3];
    const y = coordinates[index * 3 + 1];
    const z = coordinates[index * 3 + 2];
    return {
      ...node,
      id: nodeId(node, index),
      index,
      distance: Number.isFinite(node.distance) ? node.distance :
        Math.max(0, distances[index]),
      x,
      y,
      z,
      fx: x,
      fy: y,
      fz: z,
      raw: node
    };
  });

  function indexOf(reference) {
    if (reference && typeof reference === 'object' &&
        Number.isInteger(reference.index) &&
        reference.index >= 0 && reference.index < nodes.length) {
      return reference.index;
    }
    return resolveIndex(byId, nodes.length, reference);
  }

  function interaction(reference, event = null) {
    const index = indexOf(reference);
    if (index < 0) return null;
    const node = nodes[index];
    const neighborIndices = new Set();
    for (const edge of outgoing[index]) neighborIndices.add(edge.targetIndex);
    for (const edge of incoming[index]) neighborIndices.add(edge.sourceIndex);
    return {
      id: node.id,
      index,
      node,
      raw: node.raw,
      position: { x: node.x, y: node.y, z: node.z },
      outgoing: outgoing[index],
      incoming: incoming[index],
      neighbors: [...neighborIndices].map(target => nodes[target]),
      event
    };
  }

  return {
    startId: nodes[Math.max(0, startIndex)]?.id,
    startIndex: Math.max(0, startIndex),
    nodes,
    edges,
    links: edges,
    outgoing,
    incoming,
    meta: layoutResult.meta || {},
    indexOf,
    interaction
  };
}

export function computeVisualStateSpace(input, progress = () => {}) {
  return buildVisualStateSpace(input, computeStructuralLayout(input, progress));
}

export function createNodeClickHandler(visualStateSpace, onClick) {
  if (typeof onClick !== 'function') throw new Error('onClick must be a function');
  return (renderedNode, event = null) => {
    const payload = visualStateSpace.interaction(renderedNode, event);
    if (payload) onClick(payload);
    return payload;
  };
}
