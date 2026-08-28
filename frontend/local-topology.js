function edgeKey(a, b) {
  return a < b ? `${a}:${b}` : `${b}:${a}`;
}

function actionKey(edge) {
  return `${edge.piece}:${edge.direction}`;
}

function componentCount(vertices, neighbors) {
  if (!vertices.length) return 0;
  const allowed = new Set(vertices);
  const seen = new Set();
  let count = 0;
  for (const start of vertices) {
    if (seen.has(start)) continue;
    count += 1;
    const stack = [start];
    seen.add(start);
    while (stack.length) {
      const node = stack.pop();
      for (const next of neighbors.get(node) || []) {
        if (allowed.has(next) && !seen.has(next)) {
          seen.add(next);
          stack.push(next);
        }
      }
    }
  }
  return count;
}

function largestCliqueSize(vertices, neighbors) {
  let best = 0;
  function visit(candidates, size) {
    best = Math.max(best, size);
    if (size + candidates.length <= best) return;
    for (let index = 0; index < candidates.length; index += 1) {
      const vertex = candidates[index];
      const adjacent = neighbors.get(vertex) || new Set();
      visit(candidates.slice(index + 1).filter(next => adjacent.has(next)), size + 1);
    }
  }
  visit(vertices, 0);
  return best;
}

export function analyzeLocalTopology(graph) {
  const count = graph.states.length;
  const undirected = Array.from({ length: count }, () => new Set());
  const actions = Array.from({ length: count }, () => new Map());
  const uniqueEdges = new Set();
  for (const edge of graph.edges) {
    if (edge.source === edge.target) continue;
    undirected[edge.source].add(edge.target);
    undirected[edge.target].add(edge.source);
    uniqueEdges.add(edgeKey(edge.source, edge.target));
    const key = actionKey(edge);
    if (!actions[edge.source].has(key)) actions[edge.source].set(key, edge.target);
  }

  const nodes = graph.states.map((_, id) => {
    const entries = [...actions[id].entries()];
    const link = new Map(entries.map(([key]) => [key, new Set()]));
    const commutingPairs = [];
    for (let i = 0; i < entries.length; i += 1) for (let j = i + 1; j < entries.length; j += 1) {
      const [a, afterA] = entries[i], [b, afterB] = entries[j];
      const targetAB = actions[afterA].get(b);
      const targetBA = actions[afterB].get(a);
      if (targetAB !== undefined && targetAB === targetBA) {
        commutingPairs.push({ a, b, target: targetAB });
        link.get(a).add(b);
        link.get(b).add(a);
      }
    }

    const ring1 = [...undirected[id]];
    const radius = new Set([id, ...ring1]);
    for (const neighbor of ring1) for (const next of undirected[neighbor]) radius.add(next);
    let radius2Edges = 0;
    for (const node of radius) for (const next of undirected[node]) {
      if (node < next && radius.has(next)) radius2Edges += 1;
    }
    const withoutCenter = [...radius].filter(node => node !== id);
    const localNeighbors = new Map(withoutCenter.map(node => [node,
      new Set([...undirected[node]].filter(next => next !== id && radius.has(next)))
    ]));
    const cutComponents = componentCount(withoutCenter, localNeighbors);

    return {
      degree: undirected[id].size,
      radius2Nodes: radius.size,
      radius2Edges,
      squareCount: commutingPairs.length,
      commutingPairs,
      linkComponents: componentCount([...link.keys()], link),
      localDimension: largestCliqueSize([...link.keys()], link),
      localCutComponents: cutComponents,
      bottleneck: ring1.length > 1 && cutComponents > 1
    };
  });

  const metricSummary = key => {
    const values = nodes.map(node => Number(node[key]));
    return { min: Math.min(...values), max: Math.max(...values), mean: values.reduce((a, b) => a + b, 0) / values.length };
  };
  return {
    nodes,
    summary: {
      nodeCount: count,
      edgeCount: uniqueEdges.size,
      squareIncidences: nodes.reduce((sum, node) => sum + node.squareCount, 0),
      bottleneckCount: nodes.filter(node => node.bottleneck).length,
      degree: metricSummary('degree'),
      radius2Nodes: metricSummary('radius2Nodes'),
      squareCount: metricSummary('squareCount'),
      localDimension: metricSummary('localDimension')
    }
  };
}

export const topologyMetrics = {
  neutral: { label: '默认着色' },
  degree: { label: '节点度' },
  radius2Nodes: { label: '二阶邻域' },
  squareCount: { label: '交换方形' },
  linkComponents: { label: 'Link 分支' },
  localDimension: { label: '局部维数' },
  localCutComponents: { label: '局部瓶颈' }
};
