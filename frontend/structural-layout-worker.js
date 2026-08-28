const INF = 0x3fffffff;
const DIMENSIONS = 4;

function endpointKey(value) {
  return typeof value === 'object' && value !== null ? value.id : value;
}

function edgeKey(source, target) {
  return source < target ? `${source}:${target}` : `${target}:${source}`;
}

function uniqueEdges(nodes, sourceEdges) {
  const nodeCount = nodes.length;
  const byId = new Map(nodes.map((node, index) => [node.id ?? index, index]));
  const seen = new Set();
  const edges = [];
  for (const edge of sourceEdges) {
    const sourceKey = endpointKey(edge.source);
    const targetKey = endpointKey(edge.target);
    const source = byId.has(sourceKey) ? byId.get(sourceKey) :
      (Number.isInteger(sourceKey) && sourceKey >= 0 && sourceKey < nodeCount ? sourceKey : -1);
    const target = byId.has(targetKey) ? byId.get(targetKey) :
      (Number.isInteger(targetKey) && targetKey >= 0 && targetKey < nodeCount ? targetKey : -1);
    if (!Number.isInteger(source) || !Number.isInteger(target) ||
        source < 0 || target < 0 || source >= nodeCount || target >= nodeCount ||
        source === target) continue;
    const key = edgeKey(source, target);
    if (seen.has(key)) continue;
    seen.add(key);
    edges.push([source, target]);
  }
  return edges;
}

function adjacencyOf(nodeCount, edges) {
  const adjacency = Array.from({ length: nodeCount }, () => []);
  for (const [source, target] of edges) {
    adjacency[source].push(target);
    adjacency[target].push(source);
  }
  return adjacency;
}

function bfsDistances(start, adjacency) {
  const distances = new Int32Array(adjacency.length);
  distances.fill(-1);
  const queue = new Int32Array(adjacency.length);
  let head = 0;
  let tail = 1;
  queue[0] = start;
  distances[start] = 0;
  while (head < tail) {
    const source = queue[head++];
    const nextDistance = distances[source] + 1;
    for (const target of adjacency[source]) {
      if (distances[target] >= 0) continue;
      distances[target] = nextDistance;
      queue[tail++] = target;
    }
  }
  return distances;
}

function chooseLandmarks(adjacency, requested = 5, start = 0) {
  if (!adjacency.length) return { landmarks: [], distances: [] };
  const landmarks = [start];
  const distanceSets = [];
  const minDistance = new Int32Array(adjacency.length);
  minDistance.fill(INF);
  const selected = new Uint8Array(adjacency.length);
  selected[start] = 1;

  while (landmarks.length <= requested) {
    const current = landmarks[distanceSets.length];
    if (current == null) break;
    const distances = bfsDistances(current, adjacency);
    distanceSets.push(distances);
    for (let index = 0; index < distances.length; index++) {
      if (distances[index] >= 0 && distances[index] < minDistance[index]) {
        minDistance[index] = distances[index];
      }
    }
    if (landmarks.length === requested) break;
    let next = -1;
    let best = -1;
    for (let index = 0; index < minDistance.length; index++) {
      if (!selected[index] && minDistance[index] < INF && minDistance[index] > best) {
        best = minDistance[index];
        next = index;
      }
    }
    if (next < 0) break;
    selected[next] = 1;
    landmarks.push(next);
  }
  return { landmarks, distances: distanceSets };
}

function deterministicNoise(index, dimension) {
  let value = Math.imul(index + 1, 0x9e3779b1) ^ Math.imul(dimension + 11, 0x85ebca6b);
  value ^= value >>> 16;
  value = Math.imul(value, 0x7feb352d);
  value ^= value >>> 15;
  return ((value >>> 0) / 0xffffffff) * 2 - 1;
}

function stateFeature(node, dimension) {
  let total = 0;
  for (let index = 0; index < (node.positions?.length || 0); index++) {
    const position = node.positions[index];
    const a = deterministicNoise(index * 2 + 17, dimension);
    const b = deterministicNoise(index * 2 + 18, dimension + 7);
    total += position.x * a + position.y * b;
  }
  return total;
}

function normalizeDimensions(positions, nodeCount) {
  for (let dimension = 0; dimension < DIMENSIONS; dimension++) {
    let mean = 0;
    for (let index = 0; index < nodeCount; index++) {
      mean += positions[index * DIMENSIONS + dimension];
    }
    mean /= Math.max(1, nodeCount);
    let variance = 0;
    for (let index = 0; index < nodeCount; index++) {
      const offset = index * DIMENSIONS + dimension;
      positions[offset] -= mean;
      variance += positions[offset] * positions[offset];
    }
    const scale = Math.sqrt(variance / Math.max(1, nodeCount)) || 1;
    for (let index = 0; index < nodeCount; index++) {
      positions[index * DIMENSIONS + dimension] /= scale;
    }
  }
}

function averageEdgeLength(positions, edges, dimensions = 4) {
  if (!edges.length) return 1;
  let total = 0;
  for (const [source, target] of edges) {
    let squared = 0;
    for (let dimension = 0; dimension < dimensions; dimension++) {
      const delta = positions[source * DIMENSIONS + dimension] -
        positions[target * DIMENSIONS + dimension];
      squared += delta * delta;
    }
    total += Math.sqrt(squared);
  }
  return total / edges.length || 1;
}

function scaleToEdgeLength(positions, edges, nodeCount, target = 1.9) {
  const scale = target / averageEdgeLength(positions, edges);
  for (let index = 0; index < nodeCount * DIMENSIONS; index++) positions[index] *= scale;
}

function initialCoordinates(nodes, adjacency, edges, startIndex) {
  const nodeCount = nodes.length;
  const positions = new Float64Array(nodeCount * DIMENSIONS);
  const { landmarks, distances } = chooseLandmarks(adjacency, 5, startIndex);
  const distanceAt = (set, index) => {
    const value = distances[set]?.[index] ?? -1;
    return value < 0 ? (nodes[index].distance ?? 0) : value;
  };

  for (let index = 0; index < nodeCount; index++) {
    const d0 = distanceAt(0, index);
    const d1 = distanceAt(1, index);
    const d2 = distanceAt(2, index);
    const d3 = distanceAt(3, index);
    const d4 = distanceAt(4, index);
    const offset = index * DIMENSIONS;
    positions[offset] = d0 - d1;
    positions[offset + 1] = d2 - d3;
    positions[offset + 2] = (d0 + d1 - d2 - d3) * 0.5;
    positions[offset + 3] = d4 - (d0 + d1 + d2 + d3) * 0.25 +
      stateFeature(nodes[index], 3) * 0.08;
  }
  normalizeDimensions(positions, nodeCount);

  const order = Array.from({ length: nodeCount }, (_, index) => index)
    .sort((first, second) =>
      (nodes[first].distance ?? 0) - (nodes[second].distance ?? 0) || first - second);
  const placed = new Uint8Array(nodeCount);
  for (const index of order) {
    if (index === startIndex) {
      placed[index] = 1;
      continue;
    }
    const parents = adjacency[index].filter(target =>
      placed[target] && (nodes[target].distance ?? 0) < (nodes[index].distance ?? 0));
    if (parents.length) {
      const offset = index * DIMENSIONS;
      for (let dimension = 0; dimension < DIMENSIONS; dimension++) {
        let parentMean = 0;
        for (const parent of parents) {
          parentMean += positions[parent * DIMENSIONS + dimension];
        }
        parentMean /= parents.length;
        const jitter = deterministicNoise(index, dimension) * 0.18;
        positions[offset + dimension] =
          positions[offset + dimension] * 0.68 + (parentMean + jitter) * 0.32;
      }
    }
    placed[index] = 1;
  }
  scaleToEdgeLength(positions, edges, nodeCount);
  return { positions, landmarks };
}

function stateKey(positions) {
  return positions.map(position => `${position.x}:${position.y}`).join(';');
}

function mirrorMap(nodes, shapes, board, axis) {
  if (!board || !shapes.length || nodes.some(node => !Array.isArray(node.positions))) {
    const empty = new Int32Array(nodes.length);
    empty.fill(-1);
    return empty;
  }
  const byState = new Map(nodes.map((node, index) => [stateKey(node.positions), index]));
  const result = new Int32Array(nodes.length);
  result.fill(-1);
  for (let index = 0; index < nodes.length; index++) {
    const mirrored = nodes[index].positions.map((position, piece) => {
      const shape = shapes[piece] || { width: 1, height: 1 };
      return axis === 0
        ? { x: board.width - shape.width - position.x, y: position.y }
        : { x: position.x, y: board.height - shape.height - position.y };
    });
    result[index] = byState.get(stateKey(mirrored)) ?? -1;
  }
  return result;
}

function mirrorPairs(map) {
  const pairs = [];
  for (let index = 0; index < map.length; index++) {
    const target = map[index];
    if (target >= index) pairs.push([index, target]);
  }
  return pairs;
}

function seedMirrorAxis(positions, pairs, axis) {
  for (const [first, second] of pairs) {
    const firstOffset = first * DIMENSIONS;
    const secondOffset = second * DIMENSIONS;
    if (first === second) {
      positions[firstOffset + axis] = 0;
      continue;
    }
    let signed = (positions[firstOffset + axis] - positions[secondOffset + axis]) * 0.5;
    if (Math.abs(signed) < 0.2) {
      signed = (first < second ? -1 : 1) * (0.35 + Math.abs(deterministicNoise(first, axis)));
    }
    positions[firstOffset + axis] = signed;
    positions[secondOffset + axis] = -signed;
    for (let dimension = 0; dimension < DIMENSIONS; dimension++) {
      if (dimension === axis || dimension === 3) continue;
      const mean = (positions[firstOffset + dimension] + positions[secondOffset + dimension]) * 0.5;
      positions[firstOffset + dimension] = mean;
      positions[secondOffset + dimension] = mean;
    }
  }
}

function exactRepulsion(positions, velocities, nodeCount, repel) {
  for (let first = 0; first < nodeCount; first++) {
    const firstOffset = first * DIMENSIONS;
    for (let second = first + 1; second < nodeCount; second++) {
      const secondOffset = second * DIMENSIONS;
      const dx = positions[firstOffset] - positions[secondOffset];
      const dy = positions[firstOffset + 1] - positions[secondOffset + 1];
      const dz = positions[firstOffset + 2] - positions[secondOffset + 2];
      const dw = positions[firstOffset + 3] - positions[secondOffset + 3];
      const squaredLength = dx * dx + dy * dy + dz * dz + dw * dw;
      const inverseLength = 1 / Math.sqrt(Math.max(1e-12, squaredLength));
      const scale = repel * inverseLength / ((squaredLength + 1) * 10 + 2);
      velocities[firstOffset] += dx * scale;
      velocities[firstOffset + 1] += dy * scale;
      velocities[firstOffset + 2] += dz * scale;
      velocities[firstOffset + 3] += dw * scale;
      velocities[secondOffset] -= dx * scale;
      velocities[secondOffset + 1] -= dy * scale;
      velocities[secondOffset + 2] -= dz * scale;
      velocities[secondOffset + 3] -= dw * scale;
    }
  }
}

function binIndex(x, y, z, gridSize) {
  return (z * gridSize + y) * gridSize + x;
}

function spatialBins(positions, nodeCount) {
  let minX = Infinity, minY = Infinity, minZ = Infinity;
  let maxX = -Infinity, maxY = -Infinity, maxZ = -Infinity;
  for (let index = 0; index < nodeCount; index++) {
    const offset = index * DIMENSIONS;
    minX = Math.min(minX, positions[offset]);
    minY = Math.min(minY, positions[offset + 1]);
    minZ = Math.min(minZ, positions[offset + 2]);
    maxX = Math.max(maxX, positions[offset]);
    maxY = Math.max(maxY, positions[offset + 1]);
    maxZ = Math.max(maxZ, positions[offset + 2]);
  }
  const gridSize = Math.max(5, Math.min(16, Math.ceil(Math.cbrt(nodeCount / 12))));
  const scaleX = gridSize / Math.max(1e-6, maxX - minX);
  const scaleY = gridSize / Math.max(1e-6, maxY - minY);
  const scaleZ = gridSize / Math.max(1e-6, maxZ - minZ);
  const bins = Array.from({ length: gridSize ** 3 }, () => []);
  const nodeBins = new Int32Array(nodeCount * 3);
  for (let index = 0; index < nodeCount; index++) {
    const offset = index * DIMENSIONS;
    const x = Math.max(0, Math.min(gridSize - 1,
      Math.floor((positions[offset] - minX) * scaleX)));
    const y = Math.max(0, Math.min(gridSize - 1,
      Math.floor((positions[offset + 1] - minY) * scaleY)));
    const z = Math.max(0, Math.min(gridSize - 1,
      Math.floor((positions[offset + 2] - minZ) * scaleZ)));
    const binOffset = index * 3;
    nodeBins[binOffset] = x;
    nodeBins[binOffset + 1] = y;
    nodeBins[binOffset + 2] = z;
    bins[binIndex(x, y, z, gridSize)].push(index);
  }
  return { bins, nodeBins, gridSize };
}

function addRepulsion(positions, velocities, first, second, strength) {
  const firstOffset = first * DIMENSIONS;
  const secondOffset = second * DIMENSIONS;
  const dx = positions[firstOffset] - positions[secondOffset];
  const dy = positions[firstOffset + 1] - positions[secondOffset + 1];
  const dz = positions[firstOffset + 2] - positions[secondOffset + 2];
  const dw = positions[firstOffset + 3] - positions[secondOffset + 3];
  const squaredLength = dx * dx + dy * dy + dz * dz + dw * dw;
  const inverseLength = 1 / Math.sqrt(Math.max(1e-12, squaredLength));
  const scale = strength * inverseLength / ((squaredLength + 1) * 10 + 2);
  velocities[firstOffset] += dx * scale;
  velocities[firstOffset + 1] += dy * scale;
  velocities[firstOffset + 2] += dz * scale;
  velocities[firstOffset + 3] += dw * scale;
}

function sampledRepulsion(positions, velocities, nodeCount, repel, iteration) {
  const samples = nodeCount < 10000 ? 28 : 20;
  const multiplier = nodeCount / samples;
  for (let first = 0; first < nodeCount; first++) {
    let seed = (Math.imul(first + 1, 1664525) +
      Math.imul(iteration + 1, 1013904223)) >>> 0;
    for (let sample = 0; sample < samples; sample++) {
      seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0;
      const second = seed % nodeCount;
      if (first === second) continue;
      addRepulsion(positions, velocities, first, second, repel * multiplier);
    }
  }
}

function binnedRepulsion(positions, velocities, nodeCount, repel, iteration) {
  const { bins, nodeBins, gridSize } = spatialBins(positions, nodeCount);
  const farSamples = nodeCount < 2500 ? 20 : nodeCount < 10000 ? 14 : 10;
  for (let first = 0; first < nodeCount; first++) {
    const binOffset = first * 3;
    const bx = nodeBins[binOffset];
    const by = nodeBins[binOffset + 1];
    const bz = nodeBins[binOffset + 2];
    let localCount = 0;
    for (let dz = -1; dz <= 1; dz++) {
      const z = bz + dz;
      if (z < 0 || z >= gridSize) continue;
      for (let dy = -1; dy <= 1; dy++) {
        const y = by + dy;
        if (y < 0 || y >= gridSize) continue;
        for (let dx = -1; dx <= 1; dx++) {
          const x = bx + dx;
          if (x < 0 || x >= gridSize) continue;
          localCount += bins[binIndex(x, y, z, gridSize)].length;
        }
      }
    }
    const localLimit = nodeCount < 2500 ? 72 : nodeCount < 10000 ? 52 : 32;
    const localStride = Math.max(1, Math.ceil(localCount / localLimit));
    const localPhase =
      ((Math.imul(first + 1, 2654435761) + iteration) >>> 0) % localStride;
    let localCursor = 0;
    for (let dz = -1; dz <= 1; dz++) {
      const z = bz + dz;
      if (z < 0 || z >= gridSize) continue;
      for (let dy = -1; dy <= 1; dy++) {
        const y = by + dy;
        if (y < 0 || y >= gridSize) continue;
        for (let dx = -1; dx <= 1; dx++) {
          const x = bx + dx;
          if (x < 0 || x >= gridSize) continue;
          for (const second of bins[binIndex(x, y, z, gridSize)]) {
            const selected = localCursor % localStride === localPhase;
            localCursor++;
            if (first === second || !selected) continue;
            addRepulsion(positions, velocities, first, second, repel * localStride);
          }
        }
      }
    }

    let seed = (Math.imul(first + 1, 1664525) + Math.imul(iteration + 1, 1013904223)) >>> 0;
    let accepted = 0;
    for (let attempt = 0; accepted < farSamples && attempt < farSamples * 5; attempt++) {
      seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0;
      const second = seed % nodeCount;
      if (first === second) continue;
      const secondBinOffset = second * 3;
      if (Math.abs(nodeBins[secondBinOffset] - bx) <= 1 &&
          Math.abs(nodeBins[secondBinOffset + 1] - by) <= 1 &&
          Math.abs(nodeBins[secondBinOffset + 2] - bz) <= 1) continue;
      accepted++;
      addRepulsion(
        positions,
        velocities,
        first,
        second,
        repel * Math.max(1, nodeCount - localCount) / farSamples
      );
    }
  }
}

function edgeForces(positions, velocities, edges, attract) {
  for (const [source, target] of edges) {
    const sourceOffset = source * DIMENSIONS;
    const targetOffset = target * DIMENSIONS;
    const dx = positions[sourceOffset] - positions[targetOffset];
    const dy = positions[sourceOffset + 1] - positions[targetOffset + 1];
    const dz = positions[sourceOffset + 2] - positions[targetOffset + 2];
    const dw = positions[sourceOffset + 3] - positions[targetOffset + 3];
    const squaredLength = dx * dx + dy * dy + dz * dz + dw * dw;
    const inverseLength = 1 / Math.sqrt(Math.max(1e-12, squaredLength));
    const distanceSquared = squaredLength;
    const sixth = distanceSquared * distanceSquared * distanceSquared * 0.05;
    const force = ((sixth - 1) / (sixth + 1) * 0.2 - 0.1) * attract;
    velocities[sourceOffset] -= dx * inverseLength * force;
    velocities[sourceOffset + 1] -= dy * inverseLength * force;
    velocities[sourceOffset + 2] -= dz * inverseLength * force;
    velocities[sourceOffset + 3] -= dw * inverseLength * force;
    velocities[targetOffset] += dx * inverseLength * force;
    velocities[targetOffset + 1] += dy * inverseLength * force;
    velocities[targetOffset + 2] += dz * inverseLength * force;
    velocities[targetOffset + 3] += dw * inverseLength * force;
  }
}

function accumulateMirrorPairs(positions, corrections, pairs, axis) {
  for (const [first, second] of pairs) {
    const firstOffset = first * DIMENSIONS;
    const secondOffset = second * DIMENSIONS;
    const firstCorrection = first * 3;
    const secondCorrection = second * 3;
    if (first === second) {
      corrections[firstCorrection + axis] -= positions[firstOffset + axis] * 2;
      continue;
    }
    for (let dimension = 0; dimension < 3; dimension++) {
      const reflectedFirst = (dimension === axis ? -1 : 1) *
        positions[firstOffset + dimension];
      const reflectedSecond = (dimension === axis ? -1 : 1) *
        positions[secondOffset + dimension];
      corrections[firstCorrection + dimension] +=
        reflectedSecond - positions[firstOffset + dimension];
      corrections[secondCorrection + dimension] +=
        reflectedFirst - positions[secondOffset + dimension];
    }
  }
}

function applyMirrorForces(positions, corrections, mirrorX, mirrorY, nodeCount, strength) {
  corrections.fill(0);
  accumulateMirrorPairs(positions, corrections, mirrorX, 0);
  accumulateMirrorPairs(positions, corrections, mirrorY, 1);
  for (let index = 0; index < nodeCount; index++) {
    const positionOffset = index * DIMENSIONS;
    const correctionOffset = index * 3;
    positions[positionOffset] += corrections[correctionOffset] * strength;
    positions[positionOffset + 1] += corrections[correctionOffset + 1] * strength;
    positions[positionOffset + 2] += corrections[correctionOffset + 2] * strength;
  }
}

function integrate(positions, velocities, nodeCount, decay, dimension) {
  let centerX = 0;
  let centerY = 0;
  let centerZ = 0;
  let centerW = 0;
  const zScale = Math.max(0, Math.min(1, dimension - 2));
  const wScale = Math.max(0, Math.min(1, dimension - 3));
  for (let index = 0; index < nodeCount; index++) {
    const offset = index * DIMENSIONS;
    let squaredSpeed = 0;
    for (let component = 0; component < DIMENSIONS; component++) {
      const velocity = velocities[offset + component];
      squaredSpeed += velocity * velocity;
    }
    const speed = Math.sqrt(squaredSpeed);
    const speedScale = speed > 12 ? 12 / speed : 1;
    for (let component = 0; component < DIMENSIONS; component++) {
      let velocity = velocities[offset + component] * speedScale * decay;
      if (!Number.isFinite(velocity)) velocity = 0;
      velocities[offset + component] = velocity;
      positions[offset + component] += velocity;
      if (!Number.isFinite(positions[offset + component])) {
        positions[offset + component] = deterministicNoise(index, component);
      }
    }
    positions[offset + 2] *= zScale;
    positions[offset + 3] *= wScale;
    centerX += positions[offset];
    centerY += positions[offset + 1];
    centerZ += positions[offset + 2];
    centerW += positions[offset + 3];
  }
  const centering = 0.12 / Math.max(1, nodeCount);
  centerX *= centering;
  centerY *= centering;
  centerZ *= centering;
  centerW *= centering;
  for (let index = 0; index < nodeCount; index++) {
    const offset = index * DIMENSIONS;
    positions[offset] -= centerX;
    positions[offset + 1] -= centerY;
    positions[offset + 2] -= centerZ;
    positions[offset + 3] -= centerW;
  }
}

function stagePlan(nodeCount) {
  if (nodeCount < 120) return [240, 80];
  if (nodeCount < 900) return [220, 80];
  if (nodeCount <= 1400) return [180, 65];
  if (nodeCount < 2500) return [90, 34];
  if (nodeCount < 10000) return [54, 22];
  if (nodeCount < 50000) return [32, 12];
  return [18, 8];
}

function relax(positions, velocities, edges, mirrorX, mirrorY, nodeCount, progress) {
  const plan = stagePlan(nodeCount);
  const mirrorCorrections = new Float64Array(nodeCount * 3);
  const stages = [
    { name: '4D spread', iterations: plan[0], dimension: 3.98, repel: 1, attract: 1, decay: 0.65, mirror: 0.02 },
    { name: '4D -> 3D', iterations: plan[1], dimension: 3.95, repel: 0.72, attract: 1, decay: 0.7, mirror: 0.03 },
    { name: '3D projection', iterations: 1, dimension: 3, repel: 0, attract: 0, decay: 0, mirror: 0 }
  ];
  const totalIterations = stages.reduce((total, stage) => total + stage.iterations, 0);
  let completed = 0;
  let globalIteration = 0;
  for (const stage of stages) {
    for (let iteration = 0; iteration < stage.iterations; iteration++) {
      if (stage.repel > 0) {
        if (nodeCount <= 1400) exactRepulsion(positions, velocities, nodeCount, stage.repel);
        else {
          const binInterval = nodeCount < 5000 ? 3 : nodeCount < 10000 ? 4 : 8;
          if (globalIteration % binInterval === 0) {
            binnedRepulsion(positions, velocities, nodeCount, stage.repel, globalIteration);
          } else {
            sampledRepulsion(positions, velocities, nodeCount, stage.repel, globalIteration);
          }
        }
      }
      if (stage.attract > 0) edgeForces(positions, velocities, edges, stage.attract);
      integrate(positions, velocities, nodeCount, stage.decay, stage.dimension);
      if (stage.mirror > 0) applyMirrorForces(
        positions, mirrorCorrections, mirrorX, mirrorY, nodeCount, stage.mirror);
      completed++;
      globalIteration++;
      if (iteration === stage.iterations - 1 || iteration % 8 === 0) {
        progress({
          phase: stage.name,
          completed,
          total: totalIterations,
          ratio: completed / totalIterations
        });
      }
    }
  }
  for (let index = 0; index < nodeCount; index++) positions[index * DIMENSIONS + 3] = 0;
}

function finalCoordinates(positions, edges, nodeCount) {
  let centerX = 0;
  let centerY = 0;
  let centerZ = 0;
  for (let index = 0; index < nodeCount; index++) {
    const offset = index * DIMENSIONS;
    centerX += positions[offset];
    centerY += positions[offset + 1];
    centerZ += positions[offset + 2];
  }
  centerX /= Math.max(1, nodeCount);
  centerY /= Math.max(1, nodeCount);
  centerZ /= Math.max(1, nodeCount);
  const edgeLength = averageEdgeLength(positions, edges, 3);
  const scale = 2.4 / Math.max(0.01, edgeLength);
  const result = new Float32Array(nodeCount * 3);
  for (let index = 0; index < nodeCount; index++) {
    const sourceOffset = index * DIMENSIONS;
    const targetOffset = index * 3;
    result[targetOffset] = (positions[sourceOffset] - centerX) * scale;
    result[targetOffset + 1] = (positions[sourceOffset + 1] - centerY) * scale;
    result[targetOffset + 2] = (positions[sourceOffset + 2] - centerZ) * scale;
  }
  return result;
}

function mirrorError(coordinates, pairs, axis) {
  let squared = 0;
  let count = 0;
  for (const [first, second] of pairs) {
    const firstOffset = first * 3;
    const secondOffset = second * 3;
    for (let dimension = 0; dimension < 3; dimension++) {
      const residual = dimension === axis
        ? coordinates[firstOffset + dimension] + coordinates[secondOffset + dimension]
        : coordinates[firstOffset + dimension] - coordinates[secondOffset + dimension];
      squared += residual * residual;
      count++;
    }
  }
  return Math.sqrt(squared / Math.max(1, count));
}

function layoutMetrics(coordinates, edges, mirrorX, mirrorY) {
  let edgeTotal = 0;
  let edgeSquared = 0;
  let edgeMax = 0;
  for (const [source, target] of edges) {
    const sourceOffset = source * 3;
    const targetOffset = target * 3;
    const length = Math.hypot(
      coordinates[sourceOffset] - coordinates[targetOffset],
      coordinates[sourceOffset + 1] - coordinates[targetOffset + 1],
      coordinates[sourceOffset + 2] - coordinates[targetOffset + 2]
    );
    edgeTotal += length;
    edgeSquared += length * length;
    edgeMax = Math.max(edgeMax, length);
  }
  const edgeMean = edgeTotal / Math.max(1, edges.length);
  const edgeDeviation = Math.sqrt(Math.max(0,
    edgeSquared / Math.max(1, edges.length) - edgeMean * edgeMean));
  return {
    edgeMean,
    edgeDeviation,
    edgeMax,
    mirrorXPairs: mirrorX.length,
    mirrorYPairs: mirrorY.length,
    mirrorXError: mirrorError(coordinates, mirrorX, 0),
    mirrorYError: mirrorError(coordinates, mirrorY, 1)
  };
}

export function computeStructuralLayout(input, progress = () => {}) {
  const started = performance.now();
  const nodes = input.nodes || [];
  const edges = uniqueEdges(nodes, input.edges || []);
  const adjacency = adjacencyOf(nodes.length, edges);
  const byId = new Map(nodes.map((node, index) => [node.id ?? index, index]));
  const startIndex = byId.get(input.startId) ?? 0;
  const rootDistances = nodes.length ? bfsDistances(startIndex, adjacency) : new Int32Array();
  const layoutNodes = nodes.map((node, index) => ({
    ...node,
    distance: Number.isFinite(node.distance) ? node.distance :
      Math.max(0, rootDistances[index] ?? 0)
  }));
  const { positions, landmarks } = initialCoordinates(
    layoutNodes, adjacency, edges, startIndex);
  const shapes = input.shapes || [];
  const board = input.board || { width: 1, height: 1 };
  const horizontalPairs = mirrorPairs(mirrorMap(layoutNodes, shapes, board, 0));
  const verticalPairs = mirrorPairs(mirrorMap(layoutNodes, shapes, board, 1));
  seedMirrorAxis(positions, horizontalPairs, 0);
  seedMirrorAxis(positions, verticalPairs, 1);
  const velocities = new Float64Array(nodes.length * DIMENSIONS);
  relax(positions, velocities, edges, horizontalPairs, verticalPairs, nodes.length, progress);
  const coordinates = finalCoordinates(positions, edges, nodes.length);
  return {
    coordinates,
    meta: {
      algorithm: 'deterministic-landmark-hybrid-4d-force-v3',
      landmarks,
      startIndex,
      elapsedMs: performance.now() - started,
      nodeCount: nodes.length,
      edgeCount: edges.length,
      ...layoutMetrics(coordinates, edges, horizontalPairs, verticalPairs)
    }
  };
}

const isWorkerGlobal = typeof self !== 'undefined' &&
  typeof document === 'undefined' &&
  typeof WorkerGlobalScope !== 'undefined' &&
  self instanceof WorkerGlobalScope;

if (isWorkerGlobal) {
  self.onmessage = event => {
    try {
      const result = computeStructuralLayout(event.data, detail => {
        self.postMessage({ type: 'progress', detail });
      });
      self.postMessage(
        { type: 'result', coordinates: result.coordinates.buffer, meta: result.meta },
        [result.coordinates.buffer]
      );
    } catch (error) {
      self.postMessage({ type: 'error', message: error?.message || String(error) });
    }
  };
}
