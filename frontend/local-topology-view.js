import * as THREE from './vendor/three.module.min.js';
import { OrbitControls } from './vendor/OrbitControls.js';
import { analyzeLocalTopology } from './local-topology.js';

const CENTER_ID = 1409;
const pieceLabels = ['曹操', '关羽', '张飞', '赵云', '马超', '黄忠', '兵一', '兵二', '兵三', '兵四'];

function undirectedKey(a, b) {
  return a < b ? `${a}:${b}` : `${b}:${a}`;
}

function actionLabel(key) {
  const [piece, direction] = key.split(':');
  return `${pieceLabels[Number(piece)]}${direction}`;
}

function makeLabel(text, color = '#27302b') {
  const canvas = document.createElement('canvas');
  canvas.width = 160;
  canvas.height = 48;
  const context = canvas.getContext('2d');
  context.font = '600 22px ui-monospace, Consolas, monospace';
  context.textAlign = 'center';
  context.textBaseline = 'middle';
  context.fillStyle = 'rgba(250,250,247,.9)';
  context.fillRect(0, 4, 160, 40);
  context.fillStyle = color;
  context.fillText(text, 80, 25);
  const sprite = new THREE.Sprite(new THREE.SpriteMaterial({ map: new THREE.CanvasTexture(canvas), transparent: true, depthTest: false }));
  sprite.scale.set(2.8, 0.84, 1);
  sprite.renderOrder = 8;
  return sprite;
}

function connectedComponents(nodes, adjacency, omitted) {
  const allowed = new Set(nodes.filter(id => id !== omitted));
  const componentById = new Map();
  let component = 0;
  for (const start of allowed) {
    if (componentById.has(start)) continue;
    const stack = [start];
    componentById.set(start, component);
    while (stack.length) {
      const id = stack.pop();
      for (const next of adjacency[id]) if (allowed.has(next) && !componentById.has(next)) {
        componentById.set(next, component);
        stack.push(next);
      }
    }
    component += 1;
  }
  return { componentById, count: component };
}

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

export async function createLocalTopologyView(root, options = {}) {
  const canvas = root.querySelector('canvas');
  const tooltip = root.querySelector('.local-topology-tooltip');
  const response = await fetch('graph.json');
  if (!response.ok) throw new Error('graph.json unavailable for local topology sample');
  const graph = await response.json();
  const analysis = analyzeLocalTopology(graph);
  const centerMetric = analysis.nodes[CENTER_ID];

  const adjacency = Array.from({ length: graph.states.length }, () => new Set());
  const seenEdges = new Set();
  for (const edge of graph.edges) {
    adjacency[edge.source].add(edge.target);
    adjacency[edge.target].add(edge.source);
    seenEdges.add(undirectedKey(edge.source, edge.target));
  }
  const ring1 = [...adjacency[CENTER_ID]].sort((a, b) => a - b);
  const localIds = new Set([CENTER_ID, ...ring1]);
  for (const id of ring1) for (const next of adjacency[id]) localIds.add(next);
  const ids = [...localIds];
  const localEdges = [...seenEdges].map(key => key.split(':').map(Number))
    .filter(([a, b]) => localIds.has(a) && localIds.has(b));
  const components = connectedComponents(ids, adjacency, CENTER_ID);
  const localOutgoing = Array.from({ length: graph.states.length }, () => []);
  for (const edge of graph.edges) localOutgoing[edge.source].push(edge);
  let selectedId = CENTER_ID;

  const position = new Map([[CENTER_ID, new THREE.Vector3(0, 0, 0)]]);
  ring1.forEach((id, index) => {
    const angle = Math.PI * 2 * index / ring1.length - Math.PI / 2;
    const component = components.componentById.get(id) || 0;
    position.set(id, new THREE.Vector3(Math.cos(angle) * 4.2, Math.sin(angle) * 4.2, component ? 1.15 : -1.15));
  });
  const ring2 = ids.filter(id => id !== CENTER_ID && !ring1.includes(id));
  ring2.forEach((id, index) => {
    const parents = ring1.filter(parent => adjacency[id].has(parent));
    const anchor = parents.reduce((sum, parent) => sum.add(position.get(parent)), new THREE.Vector3())
      .multiplyScalar(1 / Math.max(1, parents.length));
    const angle = Math.atan2(anchor.y, anchor.x) + (index % 3 - 1) * 0.13;
    const component = components.componentById.get(id) || 0;
    position.set(id, new THREE.Vector3(Math.cos(angle) * (7.1 + (index % 2) * 0.65), Math.sin(angle) * (7.1 + (index % 2) * 0.65), component ? 1.65 : -1.65));
  });

  const scene = new THREE.Scene();
  scene.background = new THREE.Color(0xf2f3ef);
  const camera = new THREE.PerspectiveCamera(42, 1, 0.1, 100);
  camera.position.set(0, -1, 21);
  const renderer = new THREE.WebGLRenderer({ canvas, antialias: true, alpha: false });
  renderer.setPixelRatio(Math.min(devicePixelRatio, 2));
  renderer.outputColorSpace = THREE.SRGBColorSpace;
  const controls = new OrbitControls(camera, canvas);
  controls.enableDamping = true;
  controls.dampingFactor = 0.08;
  controls.minDistance = 8;
  controls.maxDistance = 42;

  const squareGroup = new THREE.Group();
  const squareEdgeKeys = new Set();
  const squareBoundaries = [];
  for (const square of centerMetric.commutingPairs) {
    const actionTargets = new Map(graph.edges.filter(edge => edge.source === CENTER_ID)
      .map(edge => [`${edge.piece}:${edge.direction}`, edge.target]));
    const afterA = actionTargets.get(square.a), afterB = actionTargets.get(square.b);
    if (![afterA, afterB, square.target].every(id => position.has(id))) continue;
    const corners = [CENTER_ID, afterA, square.target, afterB].map(id => position.get(id));
    const geometry = new THREE.BufferGeometry();
    geometry.setAttribute('position', new THREE.Float32BufferAttribute([
      ...corners[0], ...corners[1], ...corners[2], ...corners[0], ...corners[2], ...corners[3]
    ], 3));
    squareGroup.add(new THREE.Mesh(geometry, new THREE.MeshBasicMaterial({ color: 0xb33a32, transparent: true, opacity: 0.12, side: THREE.DoubleSide, depthWrite: false })));
    const boundary = [[CENTER_ID, afterA], [afterA, square.target], [square.target, afterB], [afterB, CENTER_ID]]
      .map(([a, b]) => undirectedKey(a, b));
    squareBoundaries.push(boundary);
    for (const key of boundary) squareEdgeKeys.add(key);
  }
  scene.add(squareGroup);

  for (const [a, b] of localEdges) {
    const geometry = new THREE.BufferGeometry().setFromPoints([position.get(a), position.get(b)]);
    scene.add(new THREE.Line(geometry, new THREE.LineBasicMaterial({ color: 0x8a948e, transparent: true, opacity: 0.48 })));
  }
  for (const key of squareEdgeKeys) {
    const [a, b] = key.split(':').map(Number);
    const geometry = new THREE.BufferGeometry().setFromPoints([position.get(a), position.get(b)]);
    squareGroup.add(new THREE.Line(geometry, new THREE.LineBasicMaterial({ color: 0xa63530, transparent: true, opacity: 0.92, depthTest: false })));
  }

  const meshes = [];
  let pointerDown = null;
  function pickMesh(event) {
    const rect = canvas.getBoundingClientRect();
    let best = null, bestDistance = 22;
    for (const mesh of meshes) {
      const projected = mesh.position.clone().project(camera);
      const x = rect.left + (projected.x + 1) * rect.width / 2;
      const y = rect.top + (1 - projected.y) * rect.height / 2;
      const distance = Math.hypot(event.clientX - x, event.clientY - y);
      if (distance < bestDistance) {
        best = mesh;
        bestDistance = distance;
      }
    }
    return best ? { object: best } : null;
  }
  for (const id of ids) {
    const ring = id === CENTER_ID ? 0 : ring1.includes(id) ? 1 : 2;
    const component = components.componentById.get(id) || 0;
    const color = ring === 0 ? 0xa62f2f : component === 0 ? 0x267f78 : 0xc08a2d;
    const mesh = new THREE.Mesh(
      new THREE.SphereGeometry(ring === 0 ? 0.52 : ring === 1 ? 0.36 : 0.25, 20, 14),
      new THREE.MeshBasicMaterial({ color })
    );
    mesh.position.copy(position.get(id));
    mesh.userData = { id, ring, component };
    meshes.push(mesh);
    scene.add(mesh);
    const label = makeLabel(`#${id}`, ring === 0 ? '#9f2d2d' : '#35403a');
    label.position.copy(mesh.position).add(new THREE.Vector3(0, 0.68, 0));
    scene.add(label);
  }

  root.querySelector('[data-local-stat="nodes"]').textContent = ids.length;
  root.querySelector('[data-local-stat="edges"]').textContent = localEdges.length;
  root.querySelector('[data-local-stat="squares"]').textContent = centerMetric.squareCount;
  root.querySelector('[data-local-stat="components"]').textContent = components.count;
  const edgeIndex = new Map(localEdges.map(([a, b], index) => [undirectedKey(a, b), index]));
  const boundaryRows = squareBoundaries.map(boundary => boundary.reduce((row, key) =>
    row ^ (1n << BigInt(edgeIndex.get(key))), 0n));
  const boundaryRank = rankOverF2(boundaryRows, localEdges.length);
  const betti = [1, localEdges.length - (ids.length - 1) - boundaryRank, squareBoundaries.length - boundaryRank];
  root.querySelector('[data-local-stat="euler"]').textContent = ids.length - localEdges.length + squareBoundaries.length;
  root.querySelector('[data-local-stat="betti"]').textContent = `(${betti.join(',')})`;
  root.querySelector('.local-square-list').innerHTML = centerMetric.commutingPairs.map((pair, index) =>
    `<li><b>Q${index + 1}</b><span>${actionLabel(pair.a)} ↔ ${actionLabel(pair.b)}</span><code>#${CENTER_ID} → #${pair.target}</code></li>`
  ).join('');

  function resize() {
    const rect = root.getBoundingClientRect();
    const width = Math.max(1, rect.width), height = Math.max(1, rect.height);
    renderer.setSize(width, height, false);
    camera.aspect = width / height;
    camera.updateProjectionMatrix();
  }
  function fit() {
    controls.target.set(0, 0, 0);
    camera.position.set(0, -1, 21);
    controls.update();
  }
  root.querySelector('[data-local-action="fit"]').addEventListener('click', fit);
  root.querySelectorAll('[data-square-mode]').forEach(button => button.addEventListener('click', () => {
    squareGroup.visible = button.dataset.squareMode === 'show';
    root.querySelectorAll('[data-square-mode]').forEach(item => item.classList.toggle('active', item === button));
  }));
  canvas.addEventListener('pointermove', event => {
    const rect = canvas.getBoundingClientRect();
    const hit = pickMesh(event);
    tooltip.classList.toggle('visible', Boolean(hit));
    if (!hit) return;
    const { id, ring, component } = hit.object.userData;
    const metric = analysis.nodes[id];
    tooltip.textContent = `#${id} · R${ring} · 分支 ${component + 1} · 度 ${metric.degree} · 方形 ${metric.squareCount}`;
    tooltip.style.left = `${event.clientX - rect.left + 12}px`;
    tooltip.style.top = `${event.clientY - rect.top + 12}px`;
  });
  canvas.addEventListener('pointerdown', event => {
    pointerDown = { x: event.clientX, y: event.clientY };
  });
  canvas.addEventListener('pointerup', async event => {
    if (!pointerDown || Math.hypot(event.clientX - pointerDown.x, event.clientY - pointerDown.y) > 5) return;
    const hit = pickMesh(event);
    if (!hit) return;
    const target = hit.object.userData.id;
    const parent = new Int32Array(graph.states.length);
    parent.fill(-2);
    parent[selectedId] = -1;
    const queue = new Int32Array(graph.states.length);
    let head = 0, tail = 1;
    queue[0] = selectedId;
    while (head < tail && parent[target] === -2) {
      const source = queue[head++];
      for (const edge of localOutgoing[source]) if (parent[edge.target] === -2) {
        parent[edge.target] = source;
        queue[tail++] = edge.target;
      }
    }
    if (parent[target] === -2 && target !== selectedId) return;
    const idsPath = [];
    for (let id = target; id !== -1; id = parent[id]) idsPath.push(id);
    idsPath.reverse();
    const steps = idsPath.slice(1).map((id, index) => ({
      state: graph.states[id],
      edge: localOutgoing[idsPath[index]].find(edge => edge.target === id)
    }));
    selectedId = target;
    meshes.forEach(mesh => mesh.scale.setScalar(mesh.userData.id === target ? 1.45 : 1));
    await options.onPath?.({ start: graph.states[idsPath[0]], target: graph.states[target], steps });
  });
  canvas.addEventListener('pointerleave', () => tooltip.classList.remove('visible'));
  new ResizeObserver(resize).observe(root);
  resize();

  let active = false;
  function animate() {
    requestAnimationFrame(animate);
    if (!active) return;
    controls.update();
    renderer.render(scene, camera);
  }
  animate();
  return {
    setActive(value) {
      active = value;
      if (active) {
        resize();
        renderer.render(scene, camera);
        options.onPath?.({ start: graph.states[selectedId], target: graph.states[selectedId], steps: [] });
      }
    },
    fit,
    screenPosition(id) {
      const point = position.get(id)?.clone().project(camera);
      if (!point) return null;
      const rect = canvas.getBoundingClientRect();
      return { x: rect.left + (point.x + 1) * rect.width / 2, y: rect.top + (1 - point.y) * rect.height / 2 };
    }
  };
}
