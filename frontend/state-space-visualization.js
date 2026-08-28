import { computeStructuralLayout } from './structural-layout-worker.js';

function endpointKey(value) {
  return typeof value === 'object' && value !== null ? value.id : value;
}

function asNodeRecord(state, index, distance, positions) {
  if (state && typeof state === 'object' && !Array.isArray(state)) {
    return {
      ...state,
      id: state.id ?? index,
      distance: Number.isFinite(state.distance) ? state.distance : distance,
      positions: normalizePositions(state.positions ?? positions)
    };
  }
  const id = typeof state === 'string' || typeof state === 'number'
    ? state
    : index;
  return {
    id,
    state,
    distance,
    positions: normalizePositions(positions)
  };
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
  if (startIndex < 0 || startIndex >= outgoing.length) return distances;
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
  const coordinates = flattenCoordinates(layoutResult.coordinates);
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
  if (sourceNodes.length && startIndex < 0) {
    throw new Error(`unknown state-space start id: ${String(input.startId)}`);
  }
  const safeStartIndex = sourceNodes.length ? startIndex : 0;
  const distances = rootDistances(safeStartIndex, outgoing, incoming);
  const nodes = sourceNodes.map((node, index) => {
    const x = coordinates[index * 3];
    const y = coordinates[index * 3 + 1];
    const z = coordinates[index * 3 + 2];
    return {
      ...node,
      id: nodeId(node, index),
      index,
      distance: Number.isFinite(node.distance) ? node.distance :
        distances[index],
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
    startId: nodes[safeStartIndex]?.id,
    startIndex: safeStartIndex,
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

function normalizePositions(positions) {
  if (!Array.isArray(positions)) return positions;
  return positions.map(position => Array.isArray(position)
    ? { x: position[0], y: position[1] }
    : position);
}

function flattenCoordinates(coordinates) {
  if (coordinates == null) return coordinates;
  if (ArrayBuffer.isView(coordinates)) return coordinates;
  if (coordinates instanceof ArrayBuffer) return new Float32Array(coordinates);
  if (!Array.isArray(coordinates)) return coordinates;
  if (!coordinates.length || !Array.isArray(coordinates[0])) return coordinates;
  const flat = new Float32Array(coordinates.length * 3);
  coordinates.forEach((position, index) => {
    flat[index * 3] = Number(position[0] ?? position.x ?? 0);
    flat[index * 3 + 1] = Number(position[1] ?? position.y ?? 0);
    flat[index * 3 + 2] = Number(position[2] ?? position.z ?? 0);
  });
  return flat;
}

export function stateGraphToLayoutInput(graph, options = {}) {
  if (!graph || typeof graph !== 'object') {
    throw new TypeError('state graph must be an object');
  }
  const distances = graph.distance || graph.distances || [];
  const states = Array.isArray(graph.states) ? graph.states : [];
  const nodeList = Array.isArray(graph.nodes) && (graph.nodes.length || !states.length)
    ? graph.nodes
    : states;
  const sourceNodes = nodeList === graph.nodes
    ? nodeList.map((node, index) => asNodeRecord(
      node,
      index,
      distances[index],
      node?.positions ?? node?.position
    ))
    : nodeList.map((state, index) => asNodeRecord(
      state,
      index,
      distances[index],
      state?.positions ?? state?.position
    ));
  const sourceEdges = Array.isArray(graph.edges)
    ? graph.edges
    : (Array.isArray(graph.links) ? graph.links : []);
  const startId = options.startId ?? graph.startId ?? graph.initial ??
    graph.meta?.initial ?? sourceNodes[0]?.id ?? 0;
  return {
    ...options,
    board: options.board ?? graph.board,
    shapes: options.shapes ?? graph.shapes,
    startId,
    nodes: sourceNodes.map((node, index) => ({
      ...node,
      id: node.id ?? index,
      positions: normalizePositions(node.positions)
    })),
    edges: sourceEdges
  };
}

export function computeVisualStateGraph(graph, options = {}, progress = () => {}) {
  const input = stateGraphToLayoutInput(graph, options);
  return computeVisualStateSpace(input, progress);
}

export function computeVisualStateGraphAsync(
  graph,
  options = {},
  { workerFactory, onProgress } = {}
) {
  const input = stateGraphToLayoutInput(graph, options);
  const makeWorker = workerFactory || (() => {
    if (typeof Worker === 'undefined') {
      throw new Error('Web Worker is unavailable; use computeVisualStateGraph synchronously');
    }
    return new Worker(new URL('./structural-layout-worker.js', import.meta.url), {
      type: 'module'
    });
  });
  return new Promise((resolve, reject) => {
    let settled = false;
    let worker;
    const cleanup = () => {
      if (!worker) return;
      worker.onmessage = null;
      worker.onerror = null;
      worker.onmessageerror = null;
      worker.terminate?.();
    };
    const fail = error => {
      if (settled) return;
      settled = true;
      cleanup();
      reject(error instanceof Error ? error : new Error(String(error)));
    };
    try {
      worker = makeWorker(input);
    } catch (error) {
      fail(error);
      return;
    }
    worker.onmessage = event => {
      if (event.data?.type === 'progress') {
        onProgress?.(event.data.detail);
        return;
      }
      if (event.data?.type === 'error') {
        fail(new Error(event.data.message || 'structural layout failed'));
        return;
      }
      if (event.data?.type !== 'result') return;
      const layout = {
        coordinates: flattenCoordinates(event.data.coordinates),
        meta: event.data.meta || {}
      };
      try {
        const visual = buildVisualStateSpace(input, layout);
        if (settled) return;
        settled = true;
        cleanup();
        resolve(visual);
      } catch (error) {
        fail(error);
      }
    };
    worker.onerror = error => {
      fail(error instanceof Error ? error : new Error('structural layout worker failed'));
    };
    worker.onmessageerror = () => fail(new Error('structural layout worker message could not be decoded'));
    try {
      worker.postMessage(input);
    } catch (error) {
      fail(error);
    }
  });
}

export function createNodeClickHandler(visualStateSpace, onClick) {
  if (typeof onClick !== 'function') throw new Error('onClick must be a function');
  return (renderedNode, event = null) => {
    const payload = visualStateSpace.interaction(renderedNode, event);
    if (payload) onClick(payload);
    return payload;
  };
}
