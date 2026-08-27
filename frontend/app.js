import * as THREE from './vendor/three.module.min.js';
import { OrbitControls } from './vendor/OrbitControls.js';
import { buildOverviewGraphs } from './overview-quotient.js';

const pieces = [
  { label: '曹操', cls: 'cao', w: 2, h: 2 },
  { label: '关羽', cls: 'guan', w: 2, h: 1 },
  { label: '张飞', cls: 'vertical', w: 1, h: 2 },
  { label: '赵云', cls: 'vertical', w: 1, h: 2 },
  { label: '马超', cls: 'vertical', w: 1, h: 2 },
  { label: '黄忠', cls: 'vertical', w: 1, h: 2 },
  { label: '兵一', cls: 'soldier', w: 1, h: 1 },
  { label: '兵二', cls: 'soldier', w: 1, h: 1 },
  { label: '兵三', cls: 'soldier', w: 1, h: 1 },
  { label: '兵四', cls: 'soldier', w: 1, h: 1 }
];
const ids = 'board state-count edge-count depth-count status-badge node-id distance degree selection last-move graph graph-force graph-wrap loading graph-summary zoom-label explored-count graph-count-label node-tooltip lean-valid lean-goal lean-transition result-dialog result-node result-moves result-distance result-optimal result-certification proof-dialog route-start-id route-end-id force-settings force-settings-toggle force-reset force-rest force-spring force-repulsion force-plane force-node-size force-damping force-line-width force-rest-value force-spring-value force-repulsion-value force-plane-value force-node-size-value force-damping-value force-line-width-value force3d-actions force3d-reheat force3d-pin force3d-status random-walk-toggle random-walk-status proof-trace proof-claim proof-explanation proof-step-list proof-tree proof-code proof-code-status proof-exact-count proof-quotient-count proof-length overview-controls overview-detail overview-collapse'.split(' ');
const ui = Object.fromEntries(ids.map(id => [id, document.getElementById(id)]));

let graphData, layoutData, outgoing, shortestGoalDistance = 0;
let current = 0, selected = null, history = [0], historyKinds = [], hintPath = [];
let playerMoves = 0, navigationUsed = false, shownGoal = null;
let graphMode = 'overview', selectionMode = 'end', routeStart = 0, routeEnd = null, routePath = [];
let overviewVariant = 'original', overviewGraphs = null, quotientPositions = null, skeletonOrbitPositions = null;
let overviewLayoutOrbit = -1;
let routeStartPinned = false;
let animationToken = 0, isAnimating = false, suppressCompletion = false;
const exploredNodes = new Set([0]);
const exploredEdges = new Map();

const scene = new THREE.Scene();
const camera = new THREE.PerspectiveCamera(45, 1, 0.1, 2000);
const renderer = new THREE.WebGLRenderer({ canvas: ui.graph, antialias: true, preserveDrawingBuffer: true });
renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
renderer.outputColorSpace = THREE.SRGBColorSpace;
const controls = new OrbitControls(camera, renderer.domElement);
controls.enableDamping = true;
controls.dampingFactor = 0.07;
controls.minDistance = 1;
controls.maxDistance = 600;
const graphGroup = new THREE.Group();
const overviewGroup = new THREE.Group();
const overviewOriginalGroup = new THREE.Group();
const overviewQuotientGroup = new THREE.Group();
const overviewSkeletonGroup = new THREE.Group();
const overviewExpansionGroup = new THREE.Group();
const exploreGroup = new THREE.Group();
overviewGroup.add(overviewOriginalGroup, overviewQuotientGroup, overviewSkeletonGroup, overviewExpansionGroup);
graphGroup.add(overviewGroup, exploreGroup);
scene.add(graphGroup);
const raycaster = new THREE.Raycaster();
raycaster.params.Points.threshold = 0.8;
const pointer = new THREE.Vector2();
let pointCloud = null, overviewPoints = null, overviewEdges = null, explorePoints = null, exploreEdges = null;
let pathLines = null, historyLines = null, currentMarker = null, startMarker = null, endMarker = null, edgePairs = [];
const overviewLayers = {};
let overviewExpansion = null, pendingNodePick = null;
let graphPositions = null, graphCenter = new THREE.Vector3(), graphSize = 100, exploreNodeIds = [];
let pointerDown = null;
let keyboardFocus = 'board';
let graphKeyboardIndex = 0;
let randomWalkTimer = null;
let randomWalkEnabled = false;
let forceGraph = null, forceNodes = [], forceLinks = [], forcePinned = true;
let forceCurrentMarker = null, forceStartMarker = null, forceEndMarker = null, forceHoveredNode = null;
let forceWidth = 0, forceHeight = 0, forceInitialFit = true;
const forcePointer = { x: 0, y: 0 };
// Explore mode uses a small, incremental force simulation. Positions are kept
// between rebuilds so adding frontier nodes does not make the graph jump.
const exploreForce = {
  positions: new Map(), velocities: new Map(), nodes: [], edges: [], running: false,
  lastTime: 0, temperature: 0.9,
  params: { rest: 2.15, spring: 0.12, repulsion: 11, plane: 0.32, nodeSize: 7, damping: 0.86, lineWidth: 1.5 }
};
const defaultForceParams = { ...exploreForce.params };

function isDarkTheme() { return document.documentElement.classList.contains('dark'); }
function updateSceneTheme() {
  const dark = isDarkTheme();
  scene.background = new THREE.Color(dark ? 0x1b1f1c : 0xf2f3ef);
  const palette = {
    original: { point: dark ? 0xaab3ae : 0x59635e, edge: dark ? 0x76807b : 0x7a857f, opacity: dark ? 0.16 : 0.28 },
    quotient: { opacity: dark ? 0.58 : 0.54, pointOpacity: dark ? 0.94 : 0.9 },
    skeleton: { opacity: dark ? 0.64 : 0.6, pointOpacity: dark ? 0.96 : 0.92 }
  };
  for (const [key, layer] of Object.entries(overviewLayers)) {
    if (key === 'original') {
      layer.points.material.color.set(palette[key].point);
      layer.edges.material.color.set(palette[key].edge);
    } else {
      layer.points.material.opacity = palette[key].pointOpacity;
      updateDerivedLayerColors(key);
    }
    layer.edges.material.opacity = palette[key].opacity;
  }
  if (forceGraph) {
    forceGraph
      .backgroundColor(dark ? '#1b1f1c' : '#f2f3ef')
      .nodeColor(forceNodeColor)
      .linkColor(() => dark ? '#77817c' : '#727c77')
      .refresh();
  }
  updateExpansionTheme();
  if (graphData && graphPositions) rebuildExploreGraph();
  if (currentMarker) updateGraphState();
}
updateSceneTheme();

async function loadGraph() {
  const [graphResponse, layoutResponse] = await Promise.all([fetch('graph.json'), fetch('layout.json')]);
  if (!graphResponse.ok) throw new Error('graph.json unavailable');
  if (!layoutResponse.ok) throw new Error('layout.json unavailable');
  graphData = await graphResponse.json();
  layoutData = await layoutResponse.json();
  if (layoutData.coordinates.length !== graphData.states.length) throw new Error('Layout/state count mismatch');
  outgoing = Array.from({ length: graphData.states.length }, () => []);
  for (const edge of graphData.edges) outgoing[edge.source].push(edge);
  ui['state-count'].textContent = graphData.meta.stateCount.toLocaleString();
  ui['edge-count'].textContent = graphData.meta.edgeCount.toLocaleString();
  ui['depth-count'].textContent = Math.max(...graphData.states.map(state => state.distance));
  ui['explored-count'].textContent = graphData.states.length.toLocaleString();
  shortestGoalDistance = Math.min(...graphData.states.filter(state => state.goal).map(state => state.distance));
  buildFullGraph();
  syncRouteControls();
  ui.loading.classList.add('hidden');
  renderState(0, false);
  requestAnimationFrame(fitGraph);
}

function renderState(id, pushHistory = true, moveText = '', transitionKind = 'graph') {
  if (!graphData?.states[id]) return;
  const previous = current;
  const changed = previous !== id;
  if (changed) recordExploration(previous, id);
  current = id;
  if (changed && pushHistory) {
    if (history.at(-1) !== id) {
      history.push(id);
      historyKinds.push(transitionKind);
      if (transitionKind === 'move') playerMoves += 1;
      else navigationUsed = true;
    }
    if (!isAnimating) hintPath = [];
  }
  const state = graphData.states[id];
  ui.board.replaceChildren();
  state.positions.forEach(([x, y], index) => {
    const spec = pieces[index];
    const wrap = document.createElement('div');
    wrap.className = 'piece ' + spec.cls + (selected === index ? ' selected' : '');
    Object.assign(wrap.style, { left: x * 25 + '%', top: y * 20 + '%', width: spec.w * 25 + '%', height: spec.h * 20 + '%' });
    const button = document.createElement('button');
    button.textContent = spec.label;
    button.title = index < 2 ? spec.label : spec.cls === 'vertical' ? '竖将' : '小兵';
    button.onclick = () => { selected = index; renderState(current, false); ui.selection.textContent = '已选择 ' + spec.label; };
    wrap.append(button); ui.board.append(wrap);
  });
  ui['node-id'].textContent = '#' + id;
  ui.distance.textContent = state.distance + ' 步';
  ui.degree.textContent = outgoing[id].length;
  ui['last-move'].textContent = moveText || (state.goal ? '曹操已到达出口' : '三维探索图已同步');
  ui['status-badge'].textContent = state.goal ? '已完成' : '探索中';
  ui['status-badge'].classList.toggle('goal', state.goal);
  ui['lean-valid'].innerHTML = '<i></i>true';
  ui['lean-goal'].textContent = String(state.goal);
  const latestKind = changed && pushHistory ? transitionKind : historyKinds.at(-1);
  ui['lean-transition'].textContent = latestKind === 'move' || latestKind === 'route' ? 'tryMove = some' : latestKind === 'graph' ? 'BFS reachable' : 'initial';
  if (graphMode === 'explore' && changed) rebuildExploreGraph();
  updateGraphState();
  updateProofTrace();
  if (!state.goal) shownGoal = null;
  if (!suppressCompletion && state.goal && shownGoal !== id) { shownGoal = id; showCompletion(state); }
}

function stopRandomWalk() {
  if (randomWalkTimer) clearInterval(randomWalkTimer);
  randomWalkTimer = null; randomWalkEnabled = false;
  if (ui['random-walk-toggle']) ui['random-walk-toggle'].checked = false;
  if (ui['random-walk-status']) ui['random-walk-status'].textContent = '关闭';
}
function randomWalkStep() {
  const candidates = outgoing[current] || [];
  if (!candidates.length) return;
  const previous = history.length > 1 ? history.at(-2) : null;
  const recent = new Set(history.slice(-7));
  const preferred = selected == null ? candidates : candidates.filter(edge => edge.piece === selected);
  const source = preferred.length ? preferred : candidates;
  // Prefer unexplored local states, then avoid the immediate reverse edge.
  const fresh = source.filter(edge => !recent.has(edge.target));
  const withoutBacktrack = source.filter(edge => edge.target !== previous);
  const pool = fresh.length ? fresh : (withoutBacktrack.length ? withoutBacktrack : source);
  const edge = pool[Math.floor(Math.random() * pool.length)];
  renderState(edge.target, true, '随机游走：' + pieces[edge.piece].label + '向' + edge.direction + ' · #' + edge.target, 'move');
}
function setRandomWalk(enabled) {
  if (!enabled) { stopRandomWalk(); return; }
  stopRandomWalk(); randomWalkEnabled = true;
  if (ui['random-walk-toggle']) ui['random-walk-toggle'].checked = true;
  if (ui['random-walk-status']) ui['random-walk-status'].textContent = '开启';
  randomWalkTimer = setInterval(randomWalkStep, 420);
}
function move(direction) {
  if (randomWalkEnabled) stopRandomWalk();
  cancelAnimation();
  if (selected == null) { ui.selection.textContent = '请先选择棋子'; return; }
  const edge = outgoing[current].find(item => item.piece === selected && item.direction === direction);
  if (!edge) { ui['last-move'].textContent = pieces[selected].label + '不能向' + direction + '移动'; return; }
  renderState(edge.target, true, pieces[selected].label + '向' + direction + ' · Lean 合法边 #' + edge.target, 'move');
}

document.querySelectorAll('[data-dir]').forEach(button => button.onclick = () => move(button.dataset.dir));
function focusKeyboardSurface(surface) {
  keyboardFocus = surface;
  const element = surface === 'board' ? ui.board : (graphMode === 'force' ? ui['graph-force'] : ui.graph);
  element?.classList.toggle('keyboard-active', true);
  document.querySelectorAll('.keyboard-surface').forEach(node => { if (node !== element) node.classList.remove('keyboard-active'); });
}
function boardPieceCenter(index) {
  const state = graphData.states[current], position = state.positions[index], spec = pieces[index];
  return { x: position[0] + spec.w / 2, y: position[1] + spec.h / 2 };
}
function selectPieceRelative(direction) {
  if (selected == null) selected = 0;
  const from = boardPieceCenter(selected);
  const candidates = pieces.map((_, index) => index).filter(index => index !== selected).map(index => {
    const point = boardPieceCenter(index), dx = point.x - from.x, dy = point.y - from.y;
    const forward = direction === '上' ? -dy : direction === '下' ? dy : direction === '左' ? -dx : dx;
    const lateral = direction === '上' || direction === '下' ? Math.abs(dx) : Math.abs(dy);
    return { index, forward, lateral, distance: Math.hypot(dx, dy) };
  }).filter(item => item.forward > 0.05).sort((a, b) => a.lateral - b.lateral || a.forward - b.forward || a.distance - b.distance);
  if (candidates.length) selected = candidates[0].index;
  renderState(current, false);
  ui.selection.textContent = '相对位置已选择 ' + pieces[selected].label + '（WASD 按棋盘方向选择）';
}
function graphNeighborsForKeyboard() {
  const candidates = [...new Map((outgoing[current] || []).map(edge => [edge.target, edge])).values()];
  return candidates;
}
function navigateGraphByKeyboard(direction) {
  const candidates = graphNeighborsForKeyboard();
  if (!candidates.length) { ui['last-move'].textContent = '当前节点没有可前进的合法边'; return; }
  const directional = candidates.filter(edge => edge.direction === direction);
  const pool = directional.length ? directional : candidates;
  const edge = pool[graphKeyboardIndex % pool.length];
  graphKeyboardIndex = (graphKeyboardIndex + 1) % pool.length;
  renderState(edge.target, true, '状态图键盘前进：' + direction + ' · #' + current + ' → #' + edge.target, 'graph');
}
function selectExploredNodeByKeyboard(step) {
  const ids = [...exploredNodes].filter(id => id !== current);
  if (!ids.length) { ui['last-move'].textContent = '当前还没有其他已开拓节点'; return; }
  graphKeyboardIndex = (graphKeyboardIndex + step + ids.length) % ids.length;
  const id = ids[graphKeyboardIndex];
  routeStart = current; routeEnd = id; routePath = shortestPath(current, id); syncRouteControls(); updateGraphState();
  ui['last-move'].textContent = 'W/S 选择已开拓节点：#' + id + '（按 Enter 前往）';
}
document.addEventListener('keydown', event => {
  if (event.target.matches('input,textarea,select') || document.querySelector('dialog[open]')) return;
  const map = { ArrowUp: '上', ArrowDown: '下', ArrowLeft: '左', ArrowRight: '右' };
  if (event.key === 'Tab') return;
  if (event.key.toLowerCase() === 'r') { event.preventDefault(); randomWalkStep(); return; }
  if (event.key.toLowerCase() === 't') { event.preventDefault(); setRandomWalk(!randomWalkEnabled); return; }
  if (keyboardFocus === 'board') {
    if (map[event.key]) { event.preventDefault(); move(map[event.key]); }
    else if (event.key.toLowerCase() === 'w') { event.preventDefault(); selectPieceRelative('上'); }
    else if (event.key.toLowerCase() === 's') { event.preventDefault(); selectPieceRelative('下'); }
    else if (event.key.toLowerCase() === 'a') { event.preventDefault(); selectPieceRelative('左'); }
    else if (event.key.toLowerCase() === 'd') { event.preventDefault(); selectPieceRelative('右'); }
    return;
  }
  if (map[event.key]) { event.preventDefault(); navigateGraphByKeyboard(map[event.key]); }
  else if (['w', 'a'].includes(event.key.toLowerCase())) { event.preventDefault(); selectExploredNodeByKeyboard(-1); }
  else if (['s', 'd'].includes(event.key.toLowerCase())) { event.preventDefault(); selectExploredNodeByKeyboard(1); }
  else if (event.key === 'Enter' && routeEnd !== null && routePath.length > 1) { event.preventDefault(); animateSelectedRoute(); }
});
ui.board?.addEventListener('focus', () => focusKeyboardSurface('board'));
ui.graph?.addEventListener('focus', () => focusKeyboardSurface('graph'));
ui['graph-force']?.addEventListener('focus', () => focusKeyboardSurface('graph'));
ui.board?.addEventListener('pointerdown', () => focusKeyboardSurface('board'));
ui.graph?.addEventListener('pointerdown', () => focusKeyboardSurface('graph'));
ui['graph-force']?.addEventListener('pointerdown', () => focusKeyboardSurface('graph'));
document.getElementById('undo').onclick = () => {
  cancelAnimation();
  if (history.length > 1) {
    history.pop();
    const removedKind = historyKinds.pop();
    if (removedKind === 'move') playerMoves = Math.max(0, playerMoves - 1);
    navigationUsed = historyKinds.some(kind => kind !== 'move');
    renderState(history.at(-1), false, '已撤回，探索图保留已发现节点');
  }
};
document.getElementById('reset').onclick = () => {
  cancelAnimation();
  stopRandomWalk();
  history = [0]; historyKinds = []; hintPath = []; selected = null; current = 0;
  playerMoves = 0; navigationUsed = false; shownGoal = null;
  routeStart = 0; routeEnd = null; routePath = []; routeStartPinned = false;
  exploreForce.positions.clear(); exploreForce.velocities.clear();
  exploredNodes.clear(); exploredNodes.add(0); exploredEdges.clear();
  syncRouteControls(); rebuildExploreGraph();
  renderState(0, false, '已回到经典初始状态'); requestAnimationFrame(fitGraph);
};
document.getElementById('hint').onclick = findGoalPath;
document.getElementById('go-goal').onclick = () => {
  stopRandomWalk();
  findGoalPath();
  if (routePath.length > 1) animateSelectedRoute();
};

function findGoalPath() {
  const parent = new Int32Array(graphData.states.length); parent.fill(-2); parent[current] = -1;
  const queue = new Int32Array(graphData.states.length); let head = 0, tail = 1; queue[0] = current; let goal = -1;
  while (head < tail) {
    const node = queue[head++];
    if (graphData.states[node].goal) { goal = node; break; }
    for (const edge of outgoing[node]) if (parent[edge.target] === -2) { parent[edge.target] = node; queue[tail++] = edge.target; }
  }
  if (goal < 0) { ui['last-move'].textContent = '未找到目标状态'; return; }
  hintPath = []; for (let at = goal; at !== -1; at = parent[at]) hintPath.push(at); hintPath.reverse();
  routeStart = current; routeEnd = goal; routePath = hintPath.slice(); syncRouteControls(); updateGraphState();
  const next = hintPath[1];
  if (next == null) ui['last-move'].textContent = '当前已经是目标状态';
  else {
    const edge = outgoing[current].find(item => item.target === next);
    ui['last-move'].textContent = '已规划到最近终点：' + (hintPath.length - 1) + ' 步；点击“导航到终点”或按 Enter 播放';
  }
}

function edgeKey(a, b) { return Math.min(a, b) + ':' + Math.max(a, b); }

function makePointTexture() {
  const canvas = document.createElement('canvas'); canvas.width = 32; canvas.height = 32;
  const context = canvas.getContext('2d');
  context.fillStyle = '#ffffff'; context.beginPath(); context.arc(16, 16, 13, 0, Math.PI * 2); context.fill();
  return new THREE.CanvasTexture(canvas);
}
const pointTexture = makePointTexture();

function averageMemberPositions(nodes) {
  const positions = new Float32Array(nodes.length * 3);
  nodes.forEach(node => {
    for (const stateId of node.members) {
      positions[node.id * 3] += graphPositions[stateId * 3];
      positions[node.id * 3 + 1] += graphPositions[stateId * 3 + 1];
      positions[node.id * 3 + 2] += graphPositions[stateId * 3 + 2];
    }
    const scale = 1 / Math.max(1, node.members.length);
    positions[node.id * 3] *= scale;
    positions[node.id * 3 + 1] *= scale;
    positions[node.id * 3 + 2] *= scale;
  });
  return positions;
}

function abstractShortestTree(nodeCount, edges, adjacency, seedPositions, start) {
  const distances = new Float64Array(nodeCount);
  distances.fill(Infinity);
  const parent = new Int32Array(nodeCount), parentEdge = new Int32Array(nodeCount);
  parent.fill(-1); parentEdge.fill(-1);
  const order = [], heapNodes = [], heapDistances = [];
  const currentX = seedPositions[start * 3], currentY = seedPositions[start * 3 + 1];
  const seedAngles = new Float64Array(nodeCount);
  for (let node = 0; node < nodeCount; node += 1) {
    seedAngles[node] = Math.atan2(seedPositions[node * 3 + 1] - currentY, seedPositions[node * 3] - currentX);
  }

  function pushHeap(node, distance) {
    let index = heapNodes.length;
    heapNodes.push(node); heapDistances.push(distance);
    while (index > 0) {
      const parentIndex = (index - 1) >> 1;
      if (heapDistances[parentIndex] <= distance) break;
      heapNodes[index] = heapNodes[parentIndex]; heapDistances[index] = heapDistances[parentIndex];
      index = parentIndex;
    }
    heapNodes[index] = node; heapDistances[index] = distance;
  }

  function popHeap() {
    const node = heapNodes[0], distance = heapDistances[0];
    const lastNode = heapNodes.pop(), lastDistance = heapDistances.pop();
    if (heapNodes.length) {
      let index = 0;
      while (true) {
        const left = index * 2 + 1, right = left + 1;
        if (left >= heapNodes.length) break;
        const child = right < heapNodes.length && heapDistances[right] < heapDistances[left] ? right : left;
        if (heapDistances[child] >= lastDistance) break;
        heapNodes[index] = heapNodes[child]; heapDistances[index] = heapDistances[child];
        index = child;
      }
      heapNodes[index] = lastNode; heapDistances[index] = lastDistance;
    }
    return [node, distance];
  }

  function angleDifference(a, b) {
    const difference = Math.abs(a - b) % (Math.PI * 2);
    return Math.min(difference, Math.PI * 2 - difference);
  }

  distances[start] = 0;
  pushHeap(start, 0);
  while (heapNodes.length) {
    const [node, distance] = popHeap();
    if (distance !== distances[node]) continue;
    order.push(node);
    for (const edgeId of adjacency[node]) {
      const edge = edges[edgeId];
      const next = edge.source === node ? edge.target : edge.source;
      const candidate = distance + Math.max(1, edge.weight || 1);
      const tied = candidate === distances[next];
      const currentParent = parent[next];
      const betterAngle = tied && (currentParent < 0 ||
        angleDifference(seedAngles[next], seedAngles[node]) < angleDifference(seedAngles[next], seedAngles[currentParent]));
      if (candidate < distances[next] || betterAngle) {
        distances[next] = candidate;
        parent[next] = node;
        parentEdge[next] = edgeId;
        if (!tied) pushHeap(next, candidate);
      }
    }
  }

  let maxDistance = 1;
  for (const distance of distances) if (Number.isFinite(distance)) maxDistance = Math.max(maxDistance, distance);
  for (let node = 0; node < nodeCount; node += 1) {
    if (Number.isFinite(distances[node])) continue;
    distances[node] = maxDistance + 1;
    parent[node] = start;
    order.push(node);
  }
  maxDistance = Math.max(...distances);
  return { distances, parent, parentEdge, order, seedAngles, maxDistance };
}

function focusedAbstractLayout({ nodeCount, edges, adjacency, seedPositions, currentNode, targetSize = 104 }) {
  const tree = abstractShortestTree(nodeCount, edges, adjacency, seedPositions, currentNode);
  const children = Array.from({ length: nodeCount }, () => []);
  for (let node = 0; node < nodeCount; node += 1) {
    if (tree.parent[node] >= 0) children[tree.parent[node]].push(node);
  }

  const subtreeSize = new Float64Array(nodeCount);
  subtreeSize.fill(1);
  for (let index = tree.order.length - 1; index >= 0; index -= 1) {
    const node = tree.order[index], parent = tree.parent[node];
    if (parent >= 0) subtreeSize[parent] += subtreeSize[node];
  }

  const angles = new Float64Array(nodeCount), spans = new Float64Array(nodeCount);
  spans[currentNode] = Math.PI * 2;
  function assignSectors(node, center, span) {
    const descendants = children[node];
    if (!descendants.length) return;
    descendants.sort((left, right) => tree.seedAngles[left] - tree.seedAngles[right] || left - right);
    const rawWeights = descendants.map(child => Math.pow(subtreeSize[child], 0.68));
    const weightSum = rawWeights.reduce((sum, weight) => sum + weight, 0);
    const gap = descendants.length > 1 ? Math.min(0.032, span * 0.035 / (descendants.length - 1)) : 0;
    const available = Math.max(span * 0.7, span - gap * (descendants.length - 1));
    let cursor = center - (available + gap * (descendants.length - 1)) / 2;
    descendants.forEach((child, index) => {
      const equalShare = 0.28 / descendants.length;
      const weightedShare = 0.72 * rawWeights[index] / weightSum;
      const childSpan = available * (equalShare + weightedShare);
      const childCenter = cursor + childSpan / 2;
      angles[child] = childCenter;
      spans[child] = childSpan;
      assignSectors(child, childCenter, childSpan);
      cursor += childSpan + gap;
    });
  }
  assignSectors(currentNode, 0, Math.PI * 2);

  const distanceLayers = new Map();
  for (let node = 0; node < nodeCount; node += 1) {
    if (node === currentNode) continue;
    const distance = tree.distances[node];
    if (!distanceLayers.has(distance)) distanceLayers.set(distance, []);
    distanceLayers.get(distance).push(node);
  }

  const positions = new Float32Array(nodeCount * 3);
  const verticalRanks = new Int32Array(nodeCount);
  for (const [distance, layer] of distanceLayers) {
    layer.sort((left, right) => angles[left] - angles[right] || left - right);
    layer.slice().sort((left, right) =>
      seedPositions[left * 3 + 2] - seedPositions[right * 3 + 2] || left - right
    ).forEach((node, index) => { verticalRanks[node] = index; });
    const normalizedDistance = distance / tree.maxDistance;
    const radius = targetSize * (0.1 * normalizedDistance + 0.9 * Math.pow(normalizedDistance, 0.66));
    layer.forEach((node, index) => {
      const hierarchyAngle = angles[node];
      const evenAngle = layer.length === 1
        ? hierarchyAngle
        : -Math.PI + Math.PI * 2 * (index + 0.5) / layer.length;
      const jitterLimit = Math.min(0.006, Math.PI * 0.18 / Math.max(1, layer.length));
      const jitter = ((((node * 2654435761) >>> 0) % 1000) / 999 - 0.5) * jitterLimit;
      const vertical = layer.length === 1 ? 0 : 0.8 * (1 - 2 * (verticalRanks[node] + 0.5) / layer.length);
      const planar = Math.sqrt(1 - vertical * vertical);
      const azimuth = evenAngle + jitter + normalizedDistance * 0.62;
      positions[node * 3] = Math.cos(azimuth) * planar * radius;
      positions[node * 3 + 1] = Math.sin(azimuth) * planar * radius;
      positions[node * 3 + 2] = vertical * radius;
    });
  }
  return { positions, ...tree };
}

function derivedLayerPalette(name) {
  const dark = isDarkTheme();
  if (name === 'quotient') return dark
    ? { pointNear: 0x83d5c6, pointFar: 0x59786f, treeNear: 0x74b5a9, treeFar: 0x2b3934, cross: 0x1b1f1c }
    : { pointNear: 0x176b64, pointFar: 0x78948b, treeNear: 0x2b756e, treeFar: 0xd3ddd8, cross: 0xf2f3ef };
  return dark
    ? { pointNear: 0xe2ad76, pointFar: 0x927664, treeNear: 0xd5a16a, treeFar: 0x3b332c, cross: 0x1b1f1c }
    : { pointNear: 0x8f4039, pointFar: 0xaa8879, treeNear: 0x994b44, treeFar: 0xded5cf, cross: 0xf2f3ef };
}

function updateDerivedLayerColors(name) {
  const layer = overviewLayers[name], metrics = layer?.layoutMetrics;
  if (!layer || !metrics) return;
  const palette = derivedLayerPalette(name);
  const pointNear = new THREE.Color(palette.pointNear), pointFar = new THREE.Color(palette.pointFar);
  const treeNear = new THREE.Color(palette.treeNear), treeFar = new THREE.Color(palette.treeFar);
  const cross = new THREE.Color(palette.cross);
  const pointColors = new Float32Array(metrics.nodeDistances.length * 3);
  metrics.nodeDistances.forEach((distance, index) => {
    const ratio = Math.pow(Math.min(1, distance / metrics.maxDistance), 0.62);
    pointNear.clone().lerp(pointFar, ratio).toArray(pointColors, index * 3);
  });
  layer.points.geometry.setAttribute('color', new THREE.BufferAttribute(pointColors, 3));

  const edgeColors = new Float32Array(layer.links.length * 6);
  layer.links.forEach((edge, index) => {
    if (!metrics.treeLinks[index]) {
      cross.toArray(edgeColors, index * 6);
      cross.toArray(edgeColors, index * 6 + 3);
      return;
    }
    const sourceRatio = Math.pow(Math.min(1, metrics.distanceByAbstractId[edge.source] / metrics.maxDistance), 0.62);
    const targetRatio = Math.pow(Math.min(1, metrics.distanceByAbstractId[edge.target] / metrics.maxDistance), 0.62);
    treeNear.clone().lerp(treeFar, sourceRatio).toArray(edgeColors, index * 6);
    treeNear.clone().lerp(treeFar, targetRatio).toArray(edgeColors, index * 6 + 3);
  });
  layer.edges.geometry.setAttribute('color', new THREE.BufferAttribute(edgeColors, 3));
  layer.points.material.color.set(0xffffff);
  layer.edges.material.color.set(0xffffff);
  layer.points.material.vertexColors = true;
  layer.edges.material.vertexColors = true;
  layer.points.material.needsUpdate = true;
  layer.edges.material.needsUpdate = true;
}

function updateOverviewLayerPositions(name, nodePositions, positionForNode, layoutMetrics) {
  const layer = overviewLayers[name];
  if (!layer) return;
  layer.points.geometry.setAttribute('position', new THREE.BufferAttribute(nodePositions, 3));
  layer.points.geometry.computeBoundingSphere();
  layer.positionForNode = positionForNode;
  const edgePositions = new Float32Array(layer.links.length * 6);
  layer.links.forEach((edge, index) => {
    edgePositions.set(positionForNode(edge.source), index * 6);
    edgePositions.set(positionForNode(edge.target), index * 6 + 3);
  });
  layer.edges.geometry.setAttribute('position', new THREE.BufferAttribute(edgePositions, 3));
  layer.edges.geometry.computeBoundingSphere();
  layer.layoutMetrics = layoutMetrics;
  updateDerivedLayerColors(name);
}

function relayoutDerivedOverviewLayers() {
  if (!overviewGraphs || !graphPositions) return;
  const quotient = overviewGraphs.quotient;
  const currentOrbit = quotient.orbitByState[current];
  if (overviewLayoutOrbit === currentOrbit) return;
  overviewLayoutOrbit = currentOrbit;

  const quotientSeeds = averageMemberPositions(quotient.nodes);
  const quotientLayout = focusedAbstractLayout({
    nodeCount: quotient.nodes.length,
    edges: quotient.edges,
    adjacency: quotient.adjacency,
    seedPositions: quotientSeeds,
    currentNode: currentOrbit,
    targetSize: 100
  });
  quotientPositions = quotientLayout.positions;
  const quotientTreeLinks = new Uint8Array(quotient.edges.length);
  for (const edgeId of quotientLayout.parentEdge) if (edgeId >= 0) quotientTreeLinks[edgeId] = 1;
  updateOverviewLayerPositions(
    'quotient',
    quotientPositions,
    id => quotientPositions.subarray(id * 3, id * 3 + 3),
    {
      nodeDistances: quotientLayout.distances,
      distanceByAbstractId: quotientLayout.distances,
      maxDistance: quotientLayout.maxDistance,
      treeLinks: quotientTreeLinks
    }
  );

  const skeleton = overviewGraphs.skeleton;
  const anchorIds = skeleton.nodes.map(node => node.id);
  const anchorIndexByOrbit = new Int32Array(quotient.nodes.length);
  anchorIndexByOrbit.fill(-1);
  anchorIds.forEach((orbitId, index) => { anchorIndexByOrbit[orbitId] = index; });
  const currentLocation = skeleton.locationByOrbit[currentOrbit];
  const virtualCurrent = currentLocation?.type === 'edge' ? anchorIds.length : -1;
  const skeletonNodeCount = anchorIds.length + (virtualCurrent >= 0 ? 1 : 0);
  const skeletonSeeds = new Float32Array(skeletonNodeCount * 3);
  anchorIds.forEach((orbitId, index) => {
    skeletonSeeds.set(quotientPositions.subarray(orbitId * 3, orbitId * 3 + 3), index * 3);
  });
  let skeletonCurrent = virtualCurrent >= 0 ? virtualCurrent : 0;
  if (currentLocation?.type === 'node') {
    skeletonCurrent = anchorIndexByOrbit[currentLocation.node];
  } else if (virtualCurrent >= 0) {
    skeletonSeeds.set(quotientPositions.subarray(currentOrbit * 3, currentOrbit * 3 + 3), virtualCurrent * 3);
  }

  const skeletonEdges = [];
  function addSkeletonLayoutEdge(source, target, weight, originalId) {
    skeletonEdges.push({ id: skeletonEdges.length, source, target, weight, originalId });
  }
  for (const edge of skeleton.edges) {
    if (currentLocation?.type === 'edge' && currentLocation.edge === edge.id) {
      addSkeletonLayoutEdge(anchorIndexByOrbit[edge.source], virtualCurrent, currentLocation.index, edge.id);
      addSkeletonLayoutEdge(virtualCurrent, anchorIndexByOrbit[edge.target], edge.weight - currentLocation.index, edge.id);
    } else {
      addSkeletonLayoutEdge(anchorIndexByOrbit[edge.source], anchorIndexByOrbit[edge.target], edge.weight, edge.id);
    }
  }
  const skeletonAdjacency = Array.from({ length: skeletonNodeCount }, () => []);
  for (const edge of skeletonEdges) {
    skeletonAdjacency[edge.source].push(edge.id);
    skeletonAdjacency[edge.target].push(edge.id);
  }
  const skeletonLayout = focusedAbstractLayout({
    nodeCount: skeletonNodeCount,
    edges: skeletonEdges,
    adjacency: skeletonAdjacency,
    seedPositions: skeletonSeeds,
    currentNode: skeletonCurrent,
    targetSize: 96
  });

  skeletonOrbitPositions = new Float32Array(quotient.nodes.length * 3);
  anchorIds.forEach((orbitId, index) => {
    skeletonOrbitPositions.set(skeletonLayout.positions.subarray(index * 3, index * 3 + 3), orbitId * 3);
  });
  if (virtualCurrent >= 0) {
    skeletonOrbitPositions.set(skeletonLayout.positions.subarray(virtualCurrent * 3, virtualCurrent * 3 + 3), currentOrbit * 3);
  }

  function interpolateCorridor(edge, fromIndex, toIndex, source, target) {
    const span = Math.max(1, toIndex - fromIndex);
    for (let index = fromIndex; index <= toIndex; index += 1) {
      const ratio = (index - fromIndex) / span;
      const orbitId = edge.nodePath[index];
      skeletonOrbitPositions[orbitId * 3] = source[0] + (target[0] - source[0]) * ratio;
      skeletonOrbitPositions[orbitId * 3 + 1] = source[1] + (target[1] - source[1]) * ratio;
      skeletonOrbitPositions[orbitId * 3 + 2] = 0;
    }
  }
  for (const edge of skeleton.edges) {
    const source = skeletonOrbitPositions.subarray(edge.source * 3, edge.source * 3 + 3);
    const target = skeletonOrbitPositions.subarray(edge.target * 3, edge.target * 3 + 3);
    if (currentLocation?.type === 'edge' && currentLocation.edge === edge.id) {
      const center = skeletonOrbitPositions.subarray(currentOrbit * 3, currentOrbit * 3 + 3);
      interpolateCorridor(edge, 0, currentLocation.index, source, center);
      interpolateCorridor(edge, currentLocation.index, edge.nodePath.length - 1, center, target);
    } else {
      interpolateCorridor(edge, 0, edge.nodePath.length - 1, source, target);
    }
  }

  const visibleSkeletonPositions = new Float32Array(skeleton.nodes.length * 3);
  skeleton.nodes.forEach((node, index) => {
    visibleSkeletonPositions.set(skeletonOrbitPositions.subarray(node.id * 3, node.id * 3 + 3), index * 3);
  });
  const skeletonDistanceByOrbit = new Float64Array(quotient.nodes.length);
  skeletonDistanceByOrbit.fill(Infinity);
  anchorIds.forEach((orbitId, index) => { skeletonDistanceByOrbit[orbitId] = skeletonLayout.distances[index]; });
  if (virtualCurrent >= 0) skeletonDistanceByOrbit[currentOrbit] = 0;
  for (const edge of skeleton.edges) {
    const sourceDistance = skeletonDistanceByOrbit[edge.source], targetDistance = skeletonDistanceByOrbit[edge.target];
    edge.nodePath.forEach((orbitId, index) => {
      skeletonDistanceByOrbit[orbitId] = Math.min(sourceDistance + index, targetDistance + edge.weight - index);
    });
  }
  const skeletonNodeDistances = new Float64Array(skeleton.nodes.length);
  skeleton.nodes.forEach((node, index) => { skeletonNodeDistances[index] = skeletonDistanceByOrbit[node.id]; });
  const skeletonTreeLinks = new Uint8Array(skeleton.edges.length);
  for (const layoutEdgeId of skeletonLayout.parentEdge) {
    if (layoutEdgeId >= 0) skeletonTreeLinks[skeletonEdges[layoutEdgeId].originalId] = 1;
  }
  updateOverviewLayerPositions(
    'skeleton',
    visibleSkeletonPositions,
    id => skeletonOrbitPositions.subarray(id * 3, id * 3 + 3),
    {
      nodeDistances: skeletonNodeDistances,
      distanceByAbstractId: skeletonDistanceByOrbit,
      maxDistance: skeletonLayout.maxDistance,
      treeLinks: skeletonTreeLinks
    }
  );
  if (overviewExpansion) clearOverviewExpansion();
}

function createOverviewLayer(name, group, nodePositions, nodeIds, abstractIds, links, positionForNode, pointSize) {
  const pointGeometry = new THREE.BufferGeometry();
  pointGeometry.setAttribute('position', new THREE.BufferAttribute(nodePositions, 3));
  const points = new THREE.Points(pointGeometry, new THREE.PointsMaterial({
    color: 0xaab3ae,
    size: pointSize,
    sizeAttenuation: false,
    map: pointTexture,
    alphaTest: 0.45,
    transparent: true,
    opacity: 0.72,
    depthWrite: false
  }));
  points.userData.nodeIds = nodeIds;
  points.userData.abstractIds = abstractIds;
  group.add(points);

  const edgePositions = new Float32Array(links.length * 6);
  links.forEach((edge, index) => {
    edgePositions.set(positionForNode(edge.source), index * 6);
    edgePositions.set(positionForNode(edge.target), index * 6 + 3);
  });
  const edgeGeometry = new THREE.BufferGeometry();
  edgeGeometry.setAttribute('position', new THREE.BufferAttribute(edgePositions, 3));
  const edges = new THREE.LineSegments(edgeGeometry, new THREE.LineBasicMaterial({
    color: 0x76807b,
    transparent: true,
    opacity: 0.2,
    depthWrite: false
  }));
  edges.userData.edgeData = links;
  group.add(edges);
  overviewLayers[name] = { group, points, edges, links, positionForNode };
}

function buildDerivedOverviewLayers() {
  overviewGraphs = buildOverviewGraphs(graphData);
  const quotient = overviewGraphs.quotient;
  quotientPositions = new Float32Array(quotient.nodes.length * 3);
  for (const node of quotient.nodes) {
    quotientPositions.set(graphPositions.subarray(node.representative * 3, node.representative * 3 + 3), node.id * 3);
  }
  createOverviewLayer(
    'quotient',
    overviewQuotientGroup,
    quotientPositions,
    quotient.nodes.map(node => node.representative),
    quotient.nodes.map(node => node.id),
    quotient.edges,
    id => quotientPositions.subarray(id * 3, id * 3 + 3),
    3
  );

  const skeleton = overviewGraphs.skeleton;
  skeletonOrbitPositions = new Float32Array(quotientPositions);
  for (const edge of skeleton.edges) {
    const source = new THREE.Vector3().fromArray(quotientPositions, edge.source * 3);
    const target = new THREE.Vector3().fromArray(quotientPositions, edge.target * 3);
    edge.nodePath.forEach((orbitId, index) => {
      const ratio = edge.nodePath.length === 1 ? 0 : index / (edge.nodePath.length - 1);
      const position = source.clone().lerp(target, ratio);
      skeletonOrbitPositions.set(position.toArray(), orbitId * 3);
    });
  }
  const skeletonNodePositions = new Float32Array(skeleton.nodes.length * 3);
  skeleton.nodes.forEach((node, index) => {
    skeletonNodePositions.set(skeletonOrbitPositions.subarray(node.id * 3, node.id * 3 + 3), index * 3);
  });
  createOverviewLayer(
    'skeleton',
    overviewSkeletonGroup,
    skeletonNodePositions,
    skeleton.nodes.map(node => node.representative),
    skeleton.nodes.map(node => node.id),
    skeleton.edges,
    id => skeletonOrbitPositions.subarray(id * 3, id * 3 + 3),
    3.4
  );
  overviewLayoutOrbit = -1;
  relayoutDerivedOverviewLayers();
}

function buildFullGraph() {
  const count = graphData.states.length;
  const raw = layoutData.coordinates;
  const min = [Infinity, Infinity, Infinity], max = [-Infinity, -Infinity, -Infinity];
  for (const coordinate of raw) for (let axis = 0; axis < 3; axis += 1) {
    min[axis] = Math.min(min[axis], coordinate[axis]); max[axis] = Math.max(max[axis], coordinate[axis]);
  }
  const center = min.map((value, axis) => (value + max[axis]) / 2);
  const scale = 110 / Math.max(...max.map((value, axis) => value - min[axis]));
  graphPositions = new Float32Array(count * 3);
  for (let id = 0; id < count; id += 1) for (let axis = 0; axis < 3; axis += 1) graphPositions[id * 3 + axis] = (raw[id][axis] - center[axis]) * scale;

  const seen = new Set(); edgePairs = [];
  for (const edge of graphData.edges) {
    const key = edgeKey(edge.source, edge.target);
    if (seen.has(key)) continue;
    seen.add(key); edgePairs.push([edge.source, edge.target]);
  }
  const originalLinks = edgePairs.map(([source, target], id) => ({ id, source, target, weight: 1 }));
  createOverviewLayer(
    'original',
    overviewOriginalGroup,
    graphPositions,
    null,
    null,
    originalLinks,
    id => graphPositions.subarray(id * 3, id * 3 + 3),
    1.5
  );
  buildDerivedOverviewLayers();

  currentMarker = makeRingMarker('#9f2d2d', '#ffffff', 22);
  startMarker = makeRingMarker('#d6a342', '#6f531f', 16);
  endMarker = makeRingMarker('#4ac6b8', '#1f6e66', 16);
  graphGroup.add(currentMarker, startMarker, endMarker);
  graphCenter.set(0, 0, 0); graphSize = 110;
  prepareForceGraphData();
  rebuildExploreGraph();
  setOverviewVariant('original', false);
  setGraphMode('overview', false);
  updateSceneTheme();
}

function makeRingMarker(primary, secondary, pixelDiameter) {
  const canvas = document.createElement('canvas'); canvas.width = 96; canvas.height = 96;
  const context = canvas.getContext('2d');
  context.strokeStyle = primary; context.lineWidth = 7; context.beginPath(); context.arc(48, 48, 36, 0, Math.PI * 2); context.stroke();
  context.strokeStyle = secondary; context.lineWidth = 3; context.beginPath(); context.arc(48, 48, 29, 0, Math.PI * 2); context.stroke();
  const sprite = new THREE.Sprite(new THREE.SpriteMaterial({ map: new THREE.CanvasTexture(canvas), transparent: true, depthTest: false }));
  sprite.scale.set(1, 1, 1); sprite.userData.pixelDiameter = pixelDiameter; sprite.renderOrder = 20; return sprite;
}

function prepareForceGraphData() {
  const raw = layoutData.coordinates;
  const min = [Infinity, Infinity, Infinity], max = [-Infinity, -Infinity, -Infinity];
  for (const coordinate of raw) for (let axis = 0; axis < 3; axis += 1) {
    min[axis] = Math.min(min[axis], coordinate[axis]);
    max[axis] = Math.max(max[axis], coordinate[axis]);
  }
  const center = min.map((value, axis) => (value + max[axis]) / 2);
  const scale = 1800 / Math.max(...max.map((value, axis) => value - min[axis]));
  forceNodes = graphData.states.map((state, id) => {
    const rx = (raw[id][0] - center[0]) * scale;
    const ry = (raw[id][1] - center[1]) * scale;
    const rz = (raw[id][2] - center[2]) * scale;
    return {
      id, distance: state.distance, goal: state.goal, goalDistance: raw[id][3],
      rx, ry, rz, x: rx, y: ry, z: rz, fx: rx, fy: ry, fz: rz
    };
  });
  forceLinks = edgePairs.map(([source, target]) => {
    const a = forceNodes[source], b = forceNodes[target];
    const restLength = Math.hypot(a.rx - b.rx, a.ry - b.ry, a.rz - b.rz);
    return { source, target, restLength: Math.max(0.8, Math.min(80, restLength)) };
  });
}

function forceNodeColor(node) {
  if (node.goal) return isDarkTheme() ? '#56c7b9' : '#28736d';
  if (node.goalDistance <= 20) return isDarkTheme() ? '#d4a651' : '#9a6b25';
  return isDarkTheme() ? '#aab3ae' : '#59635e';
}

function referenceAnchorForce(strength = 0.015) {
  let nodes = [];
  function force(alpha) {
    const k = strength * alpha;
    for (const node of nodes) {
      if (node.fx != null) continue;
      node.vx += (node.rx - node.x) * k;
      node.vy += (node.ry - node.y) * k;
      node.vz += (node.rz - node.z) * k;
    }
  }
  force.initialize = value => { nodes = value; };
  return force;
}

function forceNodePosition(id) {
  const node = forceNodes[id];
  return node && Number.isFinite(node.x) ? node : null;
}

function syncForceMarkerPositions() {
  if (!forceGraph || !forceCurrentMarker) return;
  const currentNode = forceNodePosition(current);
  const startNode = forceNodePosition(routeStart);
  const endNode = routeEnd === null ? null : forceNodePosition(routeEnd);
  if (currentNode) forceCurrentMarker.position.set(currentNode.x, currentNode.y, currentNode.z);
  if (startNode) forceStartMarker.position.set(startNode.x, startNode.y, startNode.z);
  if (endNode) forceEndMarker.position.set(endNode.x, endNode.y, endNode.z);
  forceStartMarker.visible = Boolean(startNode) && (routeStart !== current || routeEnd !== null);
  forceEndMarker.visible = Boolean(endNode);
}

function syncForceMarkerScales() {
  if (!forceGraph || !forceCurrentMarker) return;
  const cameraObject = forceGraph.camera();
  const cameraPosition = forceGraph.cameraPosition();
  const height = Math.max(1, ui['graph-force'].clientHeight);
  const field = 2 * Math.tan(THREE.MathUtils.degToRad(cameraObject.fov || 45) / 2);
  for (const marker of [forceCurrentMarker, forceStartMarker, forceEndMarker]) {
    const distance = Math.hypot(
      cameraPosition.x - marker.position.x,
      cameraPosition.y - marker.position.y,
      cameraPosition.z - marker.position.z
    );
    const worldSize = distance * field * marker.userData.pixelDiameter / height;
    marker.scale.set(worldSize, worldSize, 1);
  }
}

function forceCameraDistance() {
  if (!forceGraph) return 0;
  const position = forceGraph.cameraPosition();
  const target = forceGraph.controls().target || { x: 0, y: 0, z: 0 };
  return Math.hypot(position.x - target.x, position.y - target.y, position.z - target.z);
}

function updateForceTooltip(node = forceHoveredNode) {
  forceHoveredNode = node;
  ui['node-tooltip'].classList.toggle('visible', Boolean(node));
  ui['graph-force'].style.cursor = node ? 'pointer' : 'grab';
  if (!node) return;
  ui['node-tooltip'].textContent = '#' + node.id + ' · 起点距离 ' + node.distance + ' · 目标距离 ' + node.goalDistance;
  ui['node-tooltip'].style.left = forcePointer.x + 12 + 'px';
  ui['node-tooltip'].style.top = forcePointer.y + 12 + 'px';
}

function ensureForceGraph() {
  if (forceGraph) return forceGraph;
  if (!window.ForceGraph3D) throw new Error('3d-force-graph runtime unavailable');
  const container = ui['graph-force'];
  const rect = ui['graph-wrap'].getBoundingClientRect();
  ui['force3d-status'].textContent = '正在创建 25,955 个 3D 节点';
  forceGraph = new window.ForceGraph3D(container, {
    controlType: 'orbit',
    rendererConfig: { antialias: false, alpha: false, powerPreference: 'high-performance' }
  })
    .width(Math.max(1, Math.round(rect.width)))
    .height(Math.max(1, Math.round(rect.height)))
    .backgroundColor(isDarkTheme() ? '#1b1f1c' : '#f2f3ef')
    .showNavInfo(false)
    .nodeId('id')
    .nodeVal(node => node.goal ? 2.2 : 1)
    .nodeRelSize(0.85)
    .nodeResolution(3)
    .nodeColor(forceNodeColor)
    .nodeOpacity(0.9)
    .nodeLabel(() => '')
    .linkColor(() => isDarkTheme() ? '#77817c' : '#727c77')
    .linkOpacity(0.075)
    .linkWidth(0)
    .linkCurvature(0)
    .linkDirectionalParticles(0)
    .linkHoverPrecision(0)
    .enableNodeDrag(false)
    .enablePointerInteraction(true)
    .warmupTicks(0)
    .cooldownTicks(1)
    .cooldownTime(1200)
    .d3AlphaMin(0.02)
    .d3AlphaDecay(0.18)
    .d3VelocityDecay(0.65)
    .onNodeClick(node => selectRouteNode(Number(node.id)))
    .onNodeHover(node => updateForceTooltip(node))
    .onEngineTick(syncForceMarkerPositions)
    .onEngineStop(() => {
      ui['force3d-status'].textContent = forcePinned ? '参考坐标已固定' : '力导向已冷却';
      if (graphMode === 'force' && forceInitialFit) {
        forceInitialFit = false;
        requestAnimationFrame(() => forceGraph.zoomToFit(700, 48));
      }
      if (graphMode === 'force') updateGraphState();
    })
    .graphData({ nodes: forceNodes, links: forceLinks });

  const linkForce = forceGraph.d3Force('link');
  linkForce?.distance(link => link.restLength).strength(0.035).iterations(1);
  const chargeForce = forceGraph.d3Force('charge');
  chargeForce?.strength(-0.6).distanceMax(64).theta(1.35);
  forceGraph.d3Force('reference-anchor', referenceAnchorForce());
  forceGraph.renderer().setPixelRatio(Math.min(window.devicePixelRatio || 1, 1.5));

  forceCurrentMarker = makeRingMarker('#9f2d2d', '#ffffff', 22);
  forceStartMarker = makeRingMarker('#d6a342', '#6f531f', 16);
  forceEndMarker = makeRingMarker('#4ac6b8', '#1f6e66', 16);
  forceGraph.scene().add(forceCurrentMarker, forceStartMarker, forceEndMarker);
  syncForceMarkerPositions();
  syncForceMarkerScales();
  forceWidth = Math.max(1, Math.round(rect.width));
  forceHeight = Math.max(1, Math.round(rect.height));
  ui['force3d-status'].textContent = '参考坐标已固定';
  return forceGraph;
}

function releaseAndReheatForceGraph() {
  const graph = ensureForceGraph();
  forcePinned = false;
  for (const node of forceNodes) {
    node.fx = null; node.fy = null; node.fz = null;
  }
  ui['force3d-status'].textContent = 'd3-force-3d 正在松弛';
  graph.cooldownTicks(24).cooldownTime(2200).d3ReheatSimulation();
  updateGraphState();
}

function pinForceReferenceShape() {
  const graph = ensureForceGraph();
  forcePinned = true;
  for (const node of forceNodes) {
    node.x = node.fx = node.rx;
    node.y = node.fy = node.ry;
    node.z = node.fz = node.rz;
    node.vx = node.vy = node.vz = 0;
  }
  ui['force3d-status'].textContent = '正在恢复参考坐标';
  graph.cooldownTicks(1).cooldownTime(1200).d3ReheatSimulation();
  syncForceMarkerPositions();
  updateGraphState();
}

function nodePosition(id, target = new THREE.Vector3()) {
  if (graphMode === 'explore' && exploreForce.positions.has(id)) return target.copy(exploreForce.positions.get(id));
  if (overviewGraphs && overviewVariant !== 'original') {
    const orbitId = overviewGraphs.quotient.orbitByState[id];
    const positions = overviewVariant === 'skeleton' ? skeletonOrbitPositions : quotientPositions;
    return target.fromArray(positions, orbitId * 3);
  }
  return target.fromArray(graphPositions, id * 3);
}
function recordExploration(from, to) {
  exploredNodes.add(from); exploredNodes.add(to);
  const edge = outgoing[from]?.find(item => item.target === to) || outgoing[to]?.find(item => item.target === from);
  if (edge) exploredEdges.set(edgeKey(from, to), { source: from, target: to });
}
function clearExploreGroup() {
  while (exploreGroup.children.length) {
    const child = exploreGroup.children.at(-1); exploreGroup.remove(child); child.geometry?.dispose(); child.material?.dispose();
  }
}
function seedExplorePosition(id, index) {
  const existing = exploreForce.positions.get(id);
  if (existing) return existing.clone();
  const base = nodePosition(id, new THREE.Vector3());
  const angle = index * 2.399963;
  const radius = Math.min(12, 2 + Math.sqrt(index + 1) * 1.45);
  const position = base.lengthSq() > 0
    ? base.clone().multiplyScalar(0.12).add(new THREE.Vector3(Math.cos(angle) * radius, Math.sin(angle) * radius, 0.08 * Math.sin(angle * 1.7)))
    : new THREE.Vector3(Math.cos(angle) * radius, Math.sin(angle) * radius, 0);
  exploreForce.positions.set(id, position);
  exploreForce.velocities.set(id, new THREE.Vector3());
  return position;
}
function updateExploreForce(now) {
  if (graphMode !== 'explore' || !exploreForce.nodes.length || !explorePoints) return;
  const dt = Math.min(0.035, Math.max(0.001, (now - (exploreForce.lastTime || now)) / 1000));
  exploreForce.lastTime = now;
  const ids = exploreForce.nodes;
  const forces = new Map(ids.map(id => [id, new THREE.Vector3()]));
  // Compact local neighborhoods: short springs plus a small safety radius.
  const { repulsion, spring, rest, plane: planeStrength, damping } = exploreForce.params;
  const centering = 0.026;
  for (let i = 0; i < ids.length; i += 1) {
    const a = ids[i], pa = exploreForce.positions.get(a), fa = forces.get(a);
    fa.addScaledVector(pa, -centering);
    // Flatten the exploration view into a readable XY plane.
    fa.z -= pa.z * planeStrength;
    for (let j = i + 1; j < ids.length; j += 1) {
      const b = ids[j], pb = exploreForce.positions.get(b), delta = pa.clone().sub(pb);
      const distance = Math.max(0.65, delta.length());
      delta.multiplyScalar(repulsion / (distance * distance * distance));
      fa.add(delta); forces.get(b).sub(delta);
    }
  }
  for (const [source, target] of exploreForce.edges) {
    const a = exploreForce.positions.get(source), b = exploreForce.positions.get(target);
    const delta = b.clone().sub(a), distance = Math.max(0.001, delta.length());
    const force = delta.multiplyScalar(spring * (distance - rest) / distance);
    forces.get(source).add(force); forces.get(target).sub(force);
  }
  for (const id of ids) {
    const velocity = exploreForce.velocities.get(id), force = forces.get(id);
    velocity.addScaledVector(force, dt * 28).multiplyScalar(damping);
    velocity.z *= 0.72;
    if (id === current) velocity.multiplyScalar(0.35);
    velocity.clampLength(0, 2.5);
    exploreForce.positions.get(id).addScaledVector(velocity, dt * 12);
  }
  const positionAttribute = explorePoints.geometry.getAttribute('position');
  ids.forEach((id, index) => positionAttribute.setXYZ(index, ...exploreForce.positions.get(id).toArray()));
  positionAttribute.needsUpdate = true;
  if (exploreEdges) {
    const edgeAttribute = exploreEdges.geometry.getAttribute('position');
    exploreForce.edges.forEach(([source, target], index) => {
      edgeAttribute.setXYZ(index * 2, ...exploreForce.positions.get(source).toArray());
      edgeAttribute.setXYZ(index * 2 + 1, ...exploreForce.positions.get(target).toArray());
    });
    edgeAttribute.needsUpdate = true;
  }
  currentMarker?.position.copy(exploreForce.positions.get(current) || currentMarker.position);
  startMarker?.position.copy(exploreForce.positions.get(routeStart) || startMarker.position);
  if (routeEnd !== null) endMarker?.position.copy(exploreForce.positions.get(routeEnd) || endMarker.position);
  pathLines = disposeOverlay(pathLines);
  historyLines = disposeOverlay(historyLines);
  historyLines = makePath(history, 0xffbd55, 0.9); if (historyLines) graphGroup.add(historyLines);
  pathLines = makePath(routePath, isDarkTheme() ? 0xffffff : 0x27302b, 1, true); if (pathLines) graphGroup.add(pathLines);
}
function rebuildExploreGraph() {
  if (!graphData || !graphPositions) return;
  clearExploreGroup();
  const nodeSet = new Set(exploredNodes);
  const shownEdges = new Map(exploredEdges);
  for (const edge of outgoing[current] || []) {
    nodeSet.add(edge.target);
    shownEdges.set(edgeKey(edge.source, edge.target), { source: edge.source, target: edge.target });
  }
  exploreNodeIds = [...nodeSet];
  const positions = new Float32Array(exploreNodeIds.length * 3);
  const colors = new Float32Array(exploreNodeIds.length * 3);
  const dark = isDarkTheme();
  const discoveredColor = new THREE.Color(dark ? 0xd3dbd7 : 0x34443d);
  const frontierColor = new THREE.Color(dark ? 0x61706a : 0x7a8982);
  exploreNodeIds.forEach((id, index) => {
    const position = seedExplorePosition(id, index);
    positions.set(position.toArray(), index * 3);
    const color = exploredNodes.has(id) ? discoveredColor : frontierColor;
    colors.set([color.r, color.g, color.b], index * 3);
  });
  const pointGeometry = new THREE.BufferGeometry();
  pointGeometry.setAttribute('position', new THREE.BufferAttribute(positions, 3));
  pointGeometry.setAttribute('color', new THREE.BufferAttribute(colors, 3));
  explorePoints = new THREE.Points(pointGeometry, new THREE.PointsMaterial({ size: exploreForce.params.nodeSize, sizeAttenuation: false, map: pointTexture, alphaTest: 0.45, vertexColors: true, transparent: true, opacity: 0.96, depthWrite: false }));
  explorePoints.userData.nodeIds = exploreNodeIds;
  exploreGroup.add(explorePoints);

  const edges = [...shownEdges.values()];
  exploreForce.nodes = exploreNodeIds.slice();
  exploreForce.edges = edges.map(edge => [edge.source, edge.target]);
  const linePositions = new Float32Array(edges.length * 6);
  edges.forEach((edge, index) => {
    linePositions.set(exploreForce.positions.get(edge.source).toArray(), index * 6);
    linePositions.set(exploreForce.positions.get(edge.target).toArray(), index * 6 + 3);
  });
  const lineGeometry = new THREE.BufferGeometry(); lineGeometry.setAttribute('position', new THREE.BufferAttribute(linePositions, 3));
  exploreEdges = new THREE.LineSegments(lineGeometry, new THREE.LineBasicMaterial({ color: dark ? 0xa9b8b1 : 0x65766e, transparent: true, opacity: dark ? 0.52 : 0.42, depthWrite: false }));
  exploreEdges.material.linewidth = exploreForce.params.lineWidth;
  exploreGroup.add(exploreEdges);
  exploreForce.running = true;
  exploreForce.temperature = 0.9;
  if (graphMode === 'explore') {
    pointCloud = explorePoints;
    ui['explored-count'].textContent = exploreNodeIds.length.toLocaleString();
    ui['graph-summary'].textContent = '力导向探索图 · 弹簧吸引 / 节点排斥 · 已织入 ' + exploredNodes.size + ' 个状态 · 当前显示 ' + exploreNodeIds.length + ' 个节点';
  }
}

function disposeOverlay(object) {
  if (!object) return null;
  graphGroup.remove(object); object.geometry.dispose(); object.material.dispose(); return null;
}
function makePath(ids, color, opacity = 1, dashed = false) {
  if (ids.length < 2) return null;
  const points = ids.map(id => nodePosition(id, new THREE.Vector3()));
  const geometry = new THREE.BufferGeometry().setFromPoints(points);
  const material = dashed
    ? new THREE.LineDashedMaterial({ color, transparent: true, opacity, depthTest: false, dashSize: 0.45, gapSize: 0.28, linewidth: exploreForce.params.lineWidth })
    : new THREE.LineBasicMaterial({ color, transparent: true, opacity, depthTest: false });
  material.linewidth = exploreForce.params.lineWidth;
  const line = new THREE.Line(geometry, material);
  if (dashed) { line.computeLineDistances(); line.userData.dashed = true; }
  line.renderOrder = 12; return line;
}

function clearOverviewExpansion() {
  while (overviewExpansionGroup.children.length) {
    const child = overviewExpansionGroup.children.at(-1);
    overviewExpansionGroup.remove(child);
    child.geometry?.dispose();
    child.material?.dispose();
  }
  overviewExpansion = null;
  if (ui['overview-collapse']) ui['overview-collapse'].disabled = true;
  updateOverviewControls();
}

function expansionPoints(positions, nodeIds, abstractIds) {
  const geometry = new THREE.BufferGeometry().setFromPoints(positions);
  const points = new THREE.Points(geometry, new THREE.PointsMaterial({
    color: 0xd6a342,
    size: 7,
    sizeAttenuation: false,
    map: pointTexture,
    alphaTest: 0.45,
    transparent: true,
    depthTest: false
  }));
  points.userData.expansionRole = 'points';
  points.userData.expanded = true;
  points.userData.nodeIds = nodeIds;
  points.userData.abstractIds = abstractIds;
  points.renderOrder = 14;
  overviewExpansionGroup.add(points);
}

function expansionLine(positions) {
  if (positions.length < 2) return;
  const geometry = new THREE.BufferGeometry().setFromPoints(positions);
  const line = new THREE.Line(geometry, new THREE.LineBasicMaterial({
    color: 0xd6a342,
    transparent: true,
    opacity: 0.95,
    depthTest: false
  }));
  line.userData.expansionRole = 'line';
  line.renderOrder = 13;
  overviewExpansionGroup.add(line);
}

function updateExpansionTheme() {
  const dark = isDarkTheme();
  for (const child of overviewExpansionGroup.children) {
    if (child.userData.expansionRole === 'points') child.material.color.set(dark ? 0xffc76c : 0xb77518);
    if (child.userData.expansionRole === 'line') child.material.color.set(dark ? 0xffdca1 : 0x9f2d2d);
  }
}

function expandOrbit(orbitId) {
  clearOverviewExpansion();
  const orbit = overviewGraphs.quotient.nodes[orbitId];
  const positions = orbit.members.map(id => new THREE.Vector3().fromArray(graphPositions, id * 3));
  const center = new THREE.Vector3().fromArray(quotientPositions, orbitId * 3);
  const spokes = [];
  for (const position of positions) spokes.push(center.clone(), position.clone());
  if (spokes.length > 1) {
    const geometry = new THREE.BufferGeometry().setFromPoints(spokes);
    const lines = new THREE.LineSegments(geometry, new THREE.LineBasicMaterial({ color: 0xd6a342, transparent: true, opacity: 0.8, depthTest: false }));
    lines.userData.expansionRole = 'line';
    lines.renderOrder = 13;
    overviewExpansionGroup.add(lines);
  }
  expansionPoints(positions, orbit.members, orbit.members.map(() => orbitId));
  overviewExpansion = { type: 'orbit', orbitId, count: orbit.members.length };
  ui['overview-collapse'].disabled = false;
  updateExpansionTheme();
  updateOverviewControls();
}

function expandCorridor(edgeId) {
  clearOverviewExpansion();
  const edge = overviewGraphs.skeleton.edges[edgeId];
  const positions = edge.nodePath.map(orbitId => new THREE.Vector3().fromArray(skeletonOrbitPositions, orbitId * 3));
  expansionLine(positions);
  expansionPoints(
    positions,
    edge.nodePath.map(orbitId => overviewGraphs.quotient.nodes[orbitId].representative),
    edge.nodePath
  );
  overviewExpansion = { type: 'corridor', edgeId, count: edge.nodePath.length, weight: edge.weight };
  ui['overview-collapse'].disabled = false;
  updateExpansionTheme();
  updateOverviewControls();
}

function overviewDetailText() {
  if (!overviewGraphs) return '正在构造商图';
  if (overviewExpansion?.type === 'orbit') return `已展开镜像类 · ${overviewExpansion.count} 个具体状态`;
  if (overviewExpansion?.type === 'corridor') return `已展开路径 · ${overviewExpansion.weight} 步 · ${overviewExpansion.count} 个商节点`;
  if (overviewVariant === 'original') return `${graphData.states.length.toLocaleString()} 个具体状态 · ${edgePairs.length.toLocaleString()} 条连接`;
  if (overviewVariant === 'quotient') {
    const quotient = overviewGraphs.quotient;
    return `${quotient.nodes.length.toLocaleString()} 个镜像类 · ${quotient.fixedCount.toLocaleString()} 个自对称点`;
  }
  const skeleton = overviewGraphs.skeleton;
  return `${skeleton.nodes.length.toLocaleString()} 个锚点 · 压缩 ${skeleton.compressedNodeCount.toLocaleString()} 个中间点`;
}

function updateOverviewControls() {
  if (!ui['overview-controls']) return;
  ui['overview-controls'].hidden = graphMode !== 'overview';
  ui['overview-detail'].textContent = overviewDetailText();
  document.querySelectorAll('[data-overview-variant]').forEach(button => {
    const active = button.dataset.overviewVariant === overviewVariant;
    button.classList.toggle('active', active);
    button.setAttribute('aria-selected', String(active));
  });
}

function setOverviewVariant(variant, refit = true) {
  if (!overviewLayers[variant]) return;
  overviewVariant = variant;
  if (variant !== 'original') relayoutDerivedOverviewLayers();
  clearOverviewExpansion();
  for (const [name, layer] of Object.entries(overviewLayers)) layer.group.visible = name === variant;
  const active = overviewLayers[variant];
  overviewPoints = active.points;
  overviewEdges = active.edges;
  if (graphMode === 'overview') pointCloud = overviewPoints;
  updateOverviewControls();
  updateSceneTheme();
  updateGraphState();
  if (refit && graphMode === 'overview') requestAnimationFrame(fitGraph);
}

function updateGraphState() {
  if (!graphPositions || !currentMarker) return;
  if (graphMode === 'overview' && overviewVariant !== 'original') relayoutDerivedOverviewLayers();
  currentMarker.position.copy(nodePosition(current));
  startMarker.position.copy(nodePosition(routeStart));
  startMarker.visible = routeStart !== current || routeEnd !== null;
  endMarker.visible = routeEnd !== null;
  if (routeEnd !== null) endMarker.position.copy(nodePosition(routeEnd));
  historyLines = disposeOverlay(historyLines);
  pathLines = disposeOverlay(pathLines);
  historyLines = makePath(history, 0xffbd55, 0.9);
  if (historyLines) graphGroup.add(historyLines);
  pathLines = makePath(routePath, isDarkTheme() ? 0xffffff : 0x27302b, 1, true);
  if (pathLines) graphGroup.add(pathLines);
  syncForceMarkerPositions();
  if (graphMode === 'overview') {
    const nodeCount = overviewVariant === 'original'
      ? graphData.states.length
      : overviewVariant === 'quotient'
        ? overviewGraphs.quotient.nodes.length
        : overviewGraphs.skeleton.nodes.length;
    const edgeCount = overviewVariant === 'original'
      ? edgePairs.length
      : overviewVariant === 'quotient'
        ? overviewGraphs.quotient.edges.length
        : overviewGraphs.skeleton.edges.length;
    const label = overviewVariant === 'original' ? '参考全览 / 原图' : overviewVariant === 'quotient' ? '左右镜像商图' : '带权路径骨架';
    ui['explored-count'].textContent = nodeCount.toLocaleString();
    ui['graph-summary'].textContent = label + ' · 当前 #' + current + ' · ' + nodeCount.toLocaleString() + ' 个节点 · ' + edgeCount.toLocaleString() + ' 条连接';
  } else if (graphMode === 'force') {
    ui['explored-count'].textContent = graphData.states.length.toLocaleString();
    ui['graph-summary'].textContent = '3d-force-graph · 当前 #' + current + ' · ' + (forcePinned ? '参考坐标固定' : 'd3-force-3d 有限松弛') + ' · ' + edgePairs.length.toLocaleString() + ' 条连接';
  }
  updateOverviewControls();
  ui['zoom-label'].textContent = Math.round(graphMode === 'force' ? forceCameraDistance() : camera.position.distanceTo(controls.target)) + 'u';
}

function shortestPath(start, target) {
  if (start === target) return [start];
  const parent = new Int32Array(graphData.states.length); parent.fill(-2); parent[start] = -1;
  const queue = new Int32Array(graphData.states.length); let head = 0, tail = 1; queue[0] = start;
  while (head < tail && parent[target] === -2) {
    const node = queue[head++];
    for (const edge of outgoing[node]) if (parent[edge.target] === -2) { parent[edge.target] = node; queue[tail++] = edge.target; }
  }
  if (parent[target] === -2) return [];
  const path = []; for (let node = target; node !== -1; node = parent[node]) path.push(node); return path.reverse();
}
function syncRouteControls() {
  ui['route-start-id'].textContent = '#' + routeStart;
  ui['route-end-id'].textContent = routeEnd === null ? '未选择' : '#' + routeEnd;
  document.getElementById('pick-start').classList.toggle('active', selectionMode === 'start');
  document.getElementById('pick-end').classList.toggle('active', selectionMode === 'end');
  const play = document.getElementById('route-play');
  play.disabled = routeEnd === null || routePath.length < 2;
  play.textContent = isAnimating ? '■' : '▶';
  document.querySelector('.graph-toolbar').classList.toggle('route-playing', isAnimating);
}
function selectRouteNode(id) {
  cancelAnimation();
  if (selectionMode === 'start') {
    routeStart = id; routeEnd = null; routePath = []; selectionMode = 'end';
    ui['last-move'].textContent = '已选择路径起点 #' + id + '，请选择终点';
  } else {
    // Default target selection starts at the state currently shown on the board.
    // An explicitly pinned start remains available through “选择起点”.
    if (!routeStartPinned) routeStart = current;
    routeEnd = id; routePath = shortestPath(routeStart, routeEnd);
    ui['last-move'].textContent = '从当前节点 #' + routeStart + ' → #' + routeEnd + '，共 ' + Math.max(0, routePath.length - 1) + ' 条合法边';
    routeStartPinned = false;
  }
  syncRouteControls(); updateGraphState();
  if (routeEnd !== null && routePath.length) return animateSelectedRoute();
}
function cancelAnimation(update = true) {
  animationToken += 1; isAnimating = false; suppressCompletion = false;
  if (update && ui['route-start-id']) syncRouteControls();
}
function wait(milliseconds) { return new Promise(resolve => setTimeout(resolve, milliseconds)); }
async function animateSelectedRoute() {
  if (isAnimating) { cancelAnimation(); return; }
  if (routeEnd === null) return;
  const toStart = shortestPath(current, routeStart);
  const selectedPath = shortestPath(routeStart, routeEnd);
  if (!toStart.length || !selectedPath.length) return;
  routePath = selectedPath;
  const sequence = [...toStart, ...selectedPath.slice(1)];
  const token = ++animationToken; isAnimating = true; suppressCompletion = true; syncRouteControls(); updateGraphState();
  for (let index = 1; index < sequence.length; index += 1) {
    if (token !== animationToken) return;
    const from = sequence[index - 1], to = sequence[index];
    const edge = outgoing[from].find(item => item.target === to);
    if (!edge) throw new Error('Animated route contains a non-Lean edge: ' + from + ' -> ' + to);
    renderState(to, true, '路径动画 ' + index + '/' + (sequence.length - 1) + '：' + pieces[edge.piece].label + '向' + edge.direction, 'route');
    await wait(55);
  }
  if (token !== animationToken) return;
  isAnimating = false; suppressCompletion = false; syncRouteControls();
  ui['last-move'].textContent = '已沿 ' + (sequence.length - 1) + ' 条 Lean 合法边到达 #' + current;
  if (graphData.states[current].goal && shownGoal !== current) { shownGoal = current; showCompletion(graphData.states[current]); }
}
function locateCurrent() {
  if (graphMode === 'force') {
    const graph = ensureForceGraph();
    const node = forceNodePosition(current);
    if (!node) return;
    const cameraPosition = graph.cameraPosition();
    const target = graph.controls().target || { x: 0, y: 0, z: 0 };
    let dx = cameraPosition.x - target.x, dy = cameraPosition.y - target.y, dz = cameraPosition.z - target.z;
    let length = Math.hypot(dx, dy, dz);
    if (!length) { dx = 1; dy = 0.6; dz = 1; length = Math.hypot(dx, dy, dz); }
    const distance = 80;
    graph.cameraPosition(
      { x: node.x + dx / length * distance, y: node.y + dy / length * distance, z: node.z + dz / length * distance },
      { x: node.x, y: node.y, z: node.z },
      650
    );
    return;
  }
  const target = nodePosition(current, new THREE.Vector3());
  const direction = camera.position.clone().sub(controls.target).normalize();
  controls.target.copy(target); camera.position.copy(target).add(direction.multiplyScalar(16)); controls.update();
}
function setGraphMode(mode, refit = true) {
  if (!['overview', 'force', 'explore'].includes(mode)) return;
  const previousMode = graphMode;
  if (previousMode === 'force' && mode !== 'force' && forceGraph) forceGraph.pauseAnimation();
  graphMode = mode;
  overviewGroup.visible = mode === 'overview'; exploreGroup.visible = mode === 'explore';
  pointCloud = mode === 'overview' ? overviewPoints : mode === 'explore' ? explorePoints : null;
  ui.graph.hidden = mode === 'force';
  ui['graph-force'].hidden = mode !== 'force';
  ui['force3d-actions'].hidden = mode !== 'force';
  ui['graph-wrap'].dataset.mode = mode;
  ui['force-settings-toggle'].hidden = mode !== 'explore';
  if (mode !== 'explore') ui['force-settings'].hidden = true;
  document.querySelectorAll('[data-mode]').forEach(button => button.classList.toggle('active', button.dataset.mode === mode));
  ui['graph-count-label'].textContent = mode === 'explore' ? '当前织图节点' : mode === 'overview' ? '当前视图节点' : '完整图节点';
  if (mode === 'explore') rebuildExploreGraph();
  updateOverviewControls();
  updateGraphState();
  if (mode === 'force') {
    requestAnimationFrame(() => {
      try {
        const graph = ensureForceGraph();
        graph.resumeAnimation();
        resizeRenderer();
        syncForceMarkerPositions();
        syncForceMarkerScales();
        if (refit && !forceInitialFit) graph.zoomToFit(700, 48);
      } catch (error) {
        ui['force3d-status'].textContent = '3d-force-graph 初始化失败';
        console.error(error);
      }
    });
  } else if (refit) requestAnimationFrame(fitGraph);
}

function fitGraph() {
  if (graphMode === 'force') {
    ensureForceGraph().zoomToFit(700, 48);
    return;
  }
  let center = graphCenter.clone(), size = graphSize;
  if (graphMode === 'explore' && exploreGroup.children.length) {
    const box = new THREE.Box3().setFromObject(exploreGroup);
    center = box.getCenter(new THREE.Vector3());
    const dimensions = box.getSize(new THREE.Vector3());
    size = Math.max(4, dimensions.length());
  }
  controls.target.copy(center);
  const exploreView = graphMode === 'explore';
  const derivedOverview = graphMode === 'overview' && overviewVariant !== 'original';
  if (derivedOverview) {
    const box = new THREE.Box3().setFromObject(overviewLayers[overviewVariant].group);
    center = nodePosition(current, new THREE.Vector3());
    controls.target.copy(center);
    const corners = [
      new THREE.Vector3(box.min.x, box.min.y, box.min.z), new THREE.Vector3(box.max.x, box.min.y, box.min.z),
      new THREE.Vector3(box.min.x, box.max.y, box.min.z), new THREE.Vector3(box.max.x, box.max.y, box.min.z),
      new THREE.Vector3(box.min.x, box.min.y, box.max.z), new THREE.Vector3(box.max.x, box.min.y, box.max.z),
      new THREE.Vector3(box.min.x, box.max.y, box.max.z), new THREE.Vector3(box.max.x, box.max.y, box.max.z)
    ];
    const radius = Math.max(4, ...corners.map(corner => corner.distanceTo(center)));
    const distance = radius * 1.12 / Math.sin(THREE.MathUtils.degToRad(camera.fov) / 2);
    camera.up.set(0, 1, 0);
    camera.position.copy(center).add(new THREE.Vector3(0.82, 0.54, 1).normalize().multiplyScalar(distance));
  } else {
    camera.position.copy(center).add(exploreView
      ? new THREE.Vector3(0, 0, Math.max(12, size * 1.18))
      : new THREE.Vector3(size * 0.78, size * 0.48, size * 0.96));
  }
  camera.near = 0.05; camera.far = 1200; camera.updateProjectionMatrix(); controls.update();
}
function resizeRenderer() {
  const rect = ui['graph-wrap'].getBoundingClientRect();
  const width = Math.max(1, Math.round(rect.width)), height = Math.max(1, Math.round(rect.height));
  if (graphMode !== 'force') {
    const canvas = renderer.domElement;
    if (canvas.width !== Math.round(width * renderer.getPixelRatio()) || canvas.height !== Math.round(height * renderer.getPixelRatio())) renderer.setSize(width, height, false);
    camera.aspect = width / height; camera.updateProjectionMatrix();
  }
  if (graphMode === 'force' && forceGraph && (forceWidth !== width || forceHeight !== height)) {
    forceWidth = width; forceHeight = height;
    forceGraph.width(width).height(height);
  }
}
function updateMarkerScales() {
  const height = Math.max(1, renderer.domElement.clientHeight);
  const field = 2 * Math.tan(THREE.MathUtils.degToRad(camera.fov) / 2);
  for (const marker of [currentMarker, startMarker, endMarker]) {
    if (!marker) continue;
    const worldSize = marker.position.distanceTo(camera.position) * field * marker.userData.pixelDiameter / height;
    marker.scale.set(worldSize, worldSize, 1);
  }
}
function animate(now = performance.now()) {
  requestAnimationFrame(animate); resizeRenderer();
  if (graphMode === 'force') {
    syncForceMarkerScales();
    ui['zoom-label'].textContent = Math.round(forceCameraDistance()) + 'u';
    return;
  }
  controls.update();
  if (graphMode === 'explore') updateExploreForce(now);
  updateMarkerScales(); renderer.render(scene, camera);
}
requestAnimationFrame(animate);

function pickNode(event) {
  if (!pointCloud) return null;
  const rect = renderer.domElement.getBoundingClientRect();
  pointer.x = ((event.clientX - rect.left) / rect.width) * 2 - 1;
  pointer.y = -((event.clientY - rect.top) / rect.height) * 2 + 1;
  raycaster.setFromCamera(pointer, camera);
  raycaster.params.Points.threshold = Math.max(0.12, camera.position.distanceTo(controls.target) / (graphMode === 'explore' ? 105 : 170));
  const expansionPoints = overviewExpansionGroup.children.find(child => child.userData.expansionRole === 'points');
  if (graphMode === 'overview' && expansionPoints) {
    const expansionHit = raycaster.intersectObject(expansionPoints, false)[0];
    if (expansionHit) return expansionHit;
  }
  return raycaster.intersectObject(pointCloud, false)[0];
}
function pickOverviewEdge(event) {
  if (graphMode !== 'overview' || !overviewEdges) return null;
  const rect = renderer.domElement.getBoundingClientRect();
  pointer.x = ((event.clientX - rect.left) / rect.width) * 2 - 1;
  pointer.y = -((event.clientY - rect.top) / rect.height) * 2 + 1;
  raycaster.setFromCamera(pointer, camera);
  raycaster.params.Line.threshold = Math.max(0.08, camera.position.distanceTo(controls.target) / 260);
  return raycaster.intersectObject(overviewEdges, false)[0];
}
function stateIdFromPointHit(hit) {
  return hit.object.userData.nodeIds ? hit.object.userData.nodeIds[hit.index] : hit.index;
}
function abstractIdFromPointHit(hit) {
  return hit.object.userData.abstractIds ? hit.object.userData.abstractIds[hit.index] : null;
}
function edgeIdFromLineHit(hit) {
  return Math.floor((hit.index || 0) / 2);
}
renderer.domElement.addEventListener('pointerdown', event => { pointerDown = { x: event.clientX, y: event.clientY }; });
renderer.domElement.addEventListener('pointerup', event => {
  if (!pointerDown || Math.hypot(event.clientX - pointerDown.x, event.clientY - pointerDown.y) > 5) return;
  const hit = pickNode(event);
  if (hit) {
    const id = stateIdFromPointHit(hit);
    if (pendingNodePick) clearTimeout(pendingNodePick);
    pendingNodePick = setTimeout(() => { pendingNodePick = null; selectRouteNode(id); }, 220);
  }
});
renderer.domElement.addEventListener('dblclick', event => {
  if (pendingNodePick) clearTimeout(pendingNodePick);
  pendingNodePick = null;
  if (graphMode !== 'overview' || overviewVariant === 'original') return;
  const nodeHit = pickNode(event);
  if (nodeHit && overviewVariant === 'quotient') {
    expandOrbit(abstractIdFromPointHit(nodeHit));
    return;
  }
  if (overviewVariant === 'skeleton') {
    const edgeHit = pickOverviewEdge(event);
    if (edgeHit) expandCorridor(edgeIdFromLineHit(edgeHit));
  }
});
renderer.domElement.addEventListener('pointermove', event => {
  const hit = pointCloud ? pickNode(event) : null;
  const edgeHit = !hit && overviewVariant === 'skeleton' ? pickOverviewEdge(event) : null;
  ui['node-tooltip'].classList.toggle('visible', Boolean(hit || edgeHit));
  if (hit) {
    const id = stateIdFromPointHit(hit);
    const orbitId = abstractIdFromPointHit(hit);
    if (graphMode === 'overview' && overviewVariant !== 'original') {
      const orbit = overviewGraphs.quotient.nodes[orbitId];
      const prefix = overviewVariant === 'skeleton' ? '骨架锚点' : '镜像类';
      ui['node-tooltip'].textContent = hit.object.userData.expanded
        ? `展开状态 #${id} · 所属${prefix} · 点击可选为路径端点`
        : `${prefix} · 代表 #${id} · ${orbit.members.length} 个具体状态` + (overviewVariant === 'quotient' ? ' · 双击展开' : '');
    } else {
      ui['node-tooltip'].textContent = '#' + id + ' · 起点距离 ' + graphData.states[id].distance + ' · 目标距离 ' + layoutData.coordinates[id][3];
    }
    ui['node-tooltip'].style.left = event.offsetX + 12 + 'px'; ui['node-tooltip'].style.top = event.offsetY + 12 + 'px';
  } else if (edgeHit) {
    const edge = overviewGraphs.skeleton.edges[edgeIdFromLineHit(edgeHit)];
    ui['node-tooltip'].textContent = `压缩路径 · ${edge.weight} 步 · 双击展开具体商节点`;
    ui['node-tooltip'].style.left = event.offsetX + 12 + 'px'; ui['node-tooltip'].style.top = event.offsetY + 12 + 'px';
  }
});
renderer.domElement.addEventListener('pointerleave', () => ui['node-tooltip'].classList.remove('visible'));
ui['graph-force']?.addEventListener('pointermove', event => {
  const rect = ui['graph-wrap'].getBoundingClientRect();
  forcePointer.x = event.clientX - rect.left;
  forcePointer.y = event.clientY - rect.top;
  if (forceHoveredNode) updateForceTooltip(forceHoveredNode);
});
ui['graph-force']?.addEventListener('pointerleave', () => updateForceTooltip(null));

function formatForceValue(key, value) {
  return key === 'nodeSize' || key === 'repulsion' ? String(value) : Number(value).toFixed(2);
}
function syncForceSettings() {
  const mapping = { rest: 'force-rest', spring: 'force-spring', repulsion: 'force-repulsion', plane: 'force-plane', nodeSize: 'force-node-size', damping: 'force-damping', lineWidth: 'force-line-width' };
  for (const [key, id] of Object.entries(mapping)) {
    const input = ui[id], output = ui[id + '-value'];
    if (!input || !output) continue;
    input.value = exploreForce.params[key]; output.textContent = formatForceValue(key, exploreForce.params[key]);
  }
  if (explorePoints) explorePoints.material.size = exploreForce.params.nodeSize;
  if (exploreEdges) exploreEdges.material.linewidth = exploreForce.params.lineWidth;
}
function bindForceSettings() {
  const mapping = { rest: 'force-rest', spring: 'force-spring', repulsion: 'force-repulsion', plane: 'force-plane', nodeSize: 'force-node-size', damping: 'force-damping', lineWidth: 'force-line-width' };
  for (const [key, id] of Object.entries(mapping)) {
    ui[id]?.addEventListener('input', event => {
      exploreForce.params[key] = Number(event.target.value);
      syncForceSettings();
      exploreForce.lastTime = performance.now();
    });
  }
  ui['force-settings-toggle']?.addEventListener('click', () => {
    ui['force-settings'].hidden = !ui['force-settings'].hidden;
    syncForceSettings();
  });
  ui['force-reset']?.addEventListener('click', () => {
    Object.assign(exploreForce.params, defaultForceParams); syncForceSettings();
  });
  ui['random-walk-toggle']?.addEventListener('change', event => setRandomWalk(event.target.checked));
  ui['random-walk-once']?.addEventListener('click', randomWalkStep);
  ui['random-walk-toggle-button']?.addEventListener('click', () => setRandomWalk(!randomWalkEnabled));
  syncForceSettings();
}
bindForceSettings();
function zoomGraphBy(factor) {
  if (graphMode === 'force') {
    const graph = ensureForceGraph();
    const position = graph.cameraPosition();
    const target = graph.controls().target || { x: 0, y: 0, z: 0 };
    graph.cameraPosition({
      x: target.x + (position.x - target.x) * factor,
      y: target.y + (position.y - target.y) * factor,
      z: target.z + (position.z - target.z) * factor
    }, { x: target.x, y: target.y, z: target.z }, 240);
    return;
  }
  camera.position.sub(controls.target).multiplyScalar(factor).add(controls.target); controls.update();
}
document.getElementById('fit').onclick = fitGraph;
document.getElementById('locate-current').onclick = locateCurrent;
document.getElementById('zoom-in').onclick = () => zoomGraphBy(0.62);
document.getElementById('zoom-out').onclick = () => zoomGraphBy(1.55);
ui['force3d-reheat'].onclick = releaseAndReheatForceGraph;
ui['force3d-pin'].onclick = pinForceReferenceShape;
document.getElementById('pick-start').onclick = () => { selectionMode = 'start'; routeStartPinned = true; syncRouteControls(); };
document.getElementById('pick-end').onclick = () => { selectionMode = 'end'; syncRouteControls(); };
document.getElementById('route-play').onclick = animateSelectedRoute;
document.querySelectorAll('[data-mode]').forEach(button => button.onclick = () => setGraphMode(button.dataset.mode));
document.querySelectorAll('[data-overview-variant]').forEach(button => button.onclick = () => setOverviewVariant(button.dataset.overviewVariant));
ui['overview-collapse'].onclick = clearOverviewExpansion;
document.getElementById('theme').onclick = () => { document.documentElement.classList.toggle('dark'); updateSceneTheme(); };

const leanPieceNames = ['caoCao', 'guanYu', 'zhangFei', 'zhaoYun', 'maChao', 'huangZhong', 'soldier1', 'soldier2', 'soldier3', 'soldier4'];
const leanDirectionNames = { '上': 'up', '下': 'down', '左': 'left', '右': 'right' };

function escapeHtml(value) {
  return String(value).replace(/[&<>"]/g, char => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' })[char]);
}
function samePositions(a, b) {
  return a.length === b.length && a.every((pos, i) => pos[0] === b[i][0] && pos[1] === b[i][1]);
}
function movedPositions(source, edge) {
  const positions = source.positions.map(pos => pos.slice());
  const delta = { '上': [0, -1], '下': [0, 1], '左': [-1, 0], '右': [1, 0] }[edge.direction];
  positions[edge.piece] = [positions[edge.piece][0] + delta[0], positions[edge.piece][1] + delta[1]];
  return positions;
}
function sortedPositionKey(positions, indices) {
  return indices.map(i => positions[i].join(',')).sort().join('|');
}
function sameShapePositions(actual, representative) {
  return samePositions(actual.slice(0, 2), representative.slice(0, 2)) &&
    sortedPositionKey(actual, [2, 3, 4, 5]) === sortedPositionKey(representative, [2, 3, 4, 5]) &&
    sortedPositionKey(actual, [6, 7, 8, 9]) === sortedPositionKey(representative, [6, 7, 8, 9]);
}
function proofTraceSteps() {
  const steps = [];
  for (let i = 1; i < history.length; i += 1) {
    const sourceId = history[i - 1], targetId = history[i];
    const edge = (outgoing[sourceId] || []).find(candidate => candidate.target === targetId);
    if (!edge) continue;
    const source = graphData.states[sourceId], target = graphData.states[targetId];
    const actual = movedPositions(source, edge);
    const exact = samePositions(actual, target.positions);
    steps.push({ index: i, sourceId, targetId, source, target, edge, actual, exact,
      sameShape: exact || sameShapePositions(actual, target.positions) });
  }
  return steps;
}
function leanAction(step) {
  return '⟨.' + leanPieceNames[step.edge.piece] + ', .' + leanDirectionNames[step.edge.direction] + '⟩';
}
function generatedProofCode(steps, quotient) {
  const end = history.at(-1) || 0;
  if (!steps.length) return `def currentPath : Path classic classic :=
  Path.nil classic`;
  const type = quotient ? 'QPath' : 'Path';
  const proofNames = steps.map(step => {
    const action = leanAction(step);
    if (quotient) return `  -- step ${step.index}: #${step.sourceId} → #${step.targetId}
  .cons ${action} edge${step.index}_executed edge${step.index}_sameShape`;
    return `  -- step ${step.index}: #${step.sourceId} → #${step.targetId}
  .cons ${action} edge${step.index}_executed`;
  });
  let tail = '    .nil state' + end;
  for (let i = proofNames.length - 1; i >= 0; i -= 1) tail = proofNames[i] + '\n' + tail.replace(/^/gm, '  ');
  return `-- 状态常量与 edge*_executed / edge*_sameShape 由图证书导出。
def currentProof : ${type} state0 state${end} :=
${tail}`;
}
function updateProofTrace() {
  if (!graphData || !ui['proof-step-list']) return;
  const steps = proofTraceSteps();
  const quotientCount = steps.filter(step => !step.exact).length;
  const exactCount = steps.length - quotientCount;
  const quotient = quotientCount > 0;
  const target = history.at(-1) || 0;
  const goal = graphData.states[target]?.goal;
  const claimType = goal ? (quotient ? 'QSolution state0' : (navigationUsed ? 'Solution state0' : 'CertifiedPlay state0')) : (quotient ? 'QPath state0 state' + target : 'Path state0 state' + target);
  ui['proof-claim'].textContent = claimType;
  ui['proof-explanation'].textContent = !steps.length
    ? '零步证明由 Path.nil state0 构造。每次合法移动都会在这里增加一个 cons 构造器。'
    : quotient
      ? '当前证明包含规范代表切换，因此整体类型是 QPath：每一步同时保存 tryMove 等式和 SameShape 代表证明。'
      : '当前所有目标都与 tryMove 的带标签结果完全相同，因此这些 cons 构造器组成精确 Path。';
  ui['proof-exact-count'].textContent = exactCount;
  ui['proof-quotient-count'].textContent = quotientCount;
  ui['proof-length'].textContent = steps.length + ' steps';
  ui['proof-step-list'].innerHTML = steps.length ? steps.map(step => {
    const piece = pieces[step.edge.piece].label, action = leanAction(step);
    return '<li class="proof-step ' + (step.exact ? '' : 'quotient') + '" data-index="' + step.index + '">' +
      '<h4>#' + step.sourceId + ' → #' + step.targetId + '<span>' + (step.exact ? 'Step' : 'QStep') + '</span></h4>' +
      '<div class="proof-equation">tryMove state' + step.sourceId + ' ' + escapeHtml(action) + '<br>= some actual' + step.index +
      '<br><b>动作：</b>' + piece + '向' + step.edge.direction + '</div>' +
      (step.exact ? '<div class="proof-constructor">actual' + step.index + ' = state' + step.targetId + ' · Path.cons</div>' :
        '<div class="proof-equation proof-represented">SameShape actual' + step.index + ' state' + step.targetId + ' = true</div><div class="proof-constructor">QPath.cons executed represented tail</div>') + '</li>';
  }).join('') : '<div class="proof-empty">初始状态本身已有零步证明<code>Path.nil state0</code>移动一个棋子，观察证明项增加一个构造器。</div>';
  let tree = '<div><b>' + (quotient ? 'QPath' : 'Path') + '</b> state0 state' + target + '</div>';
  if (!steps.length) tree += '<div class="proof-tree-node"><em>Path.nil</em> state0</div>';
  for (const step of steps) tree += '<div class="proof-tree-node"><em>' + (quotient ? 'QPath.cons' : 'Path.cons') + '</em> ' + escapeHtml(leanAction(step)) +
    '<div>executed : tryMove … = some actual' + step.index + '</div>' +
    (!step.exact ? '<div class="quotient-term">represented : SameShape actual' + step.index + ' state' + step.targetId + '</div>' : '') + '</div>';
  tree += '<div class="proof-tree-node"><em>' + (quotient ? 'QPath.nil' : 'Path.nil') + '</em> state' + target + '</div>';
  if (goal) tree += '<div class="proof-tree-node"><b>solved</b> : goal state' + target + ' = true<br><em>⇒ ' + (quotient ? 'QSolution' : (navigationUsed ? 'Solution' : 'CertifiedPlay')) + '</em></div>';
  ui['proof-tree'].innerHTML = tree;
  ui['proof-code'].textContent = generatedProofCode(steps, quotient);
  ui['proof-code-status'].textContent = quotient ? 'QPath：执行等式 + 同形代表证书' : 'Path：每一步是精确 tryMove 等式';
}

function showCompletion(state) {
  ui['result-node'].textContent = '#' + state.id;
  ui['result-moves'].textContent = navigationUsed ? playerMoves + ' + 导航' : playerMoves + ' 步';
  ui['result-distance'].textContent = state.distance + ' 步';
  if (navigationUsed) {
    ui['result-certification'].textContent = '该终局节点由 Lean BFS 计算为从经典布局可达；本次过程使用了三维图导航，因此不作为连续玩家解计步。';
    ui['result-optimal'].textContent = '可达终局 · goal = true';
    ui['result-optimal'].className = 'result-verdict computed';
  } else if (playerMoves === shortestGoalDistance) {
    ui['result-certification'].textContent = '这条操作序列中的每一步都来自 Lean 导出的 tryMove 合法转换。';
    ui['result-optimal'].textContent = '达到 Lean BFS 计算的全局最短值：' + shortestGoalDistance + ' 步';
    ui['result-optimal'].className = 'result-verdict';
  } else {
    ui['result-certification'].textContent = '这条操作序列中的每一步都来自 Lean 导出的 tryMove 合法转换。';
    ui['result-optimal'].textContent = '合法完成 · 比计算最短值多 ' + Math.max(0, playerMoves - shortestGoalDistance) + ' 步';
    ui['result-optimal'].className = 'result-verdict computed';
  }
  if (!ui['result-dialog'].open) ui['result-dialog'].showModal();
}

function setProofTrace(open) {
  ui['proof-trace']?.classList.toggle('open', open);
  document.getElementById('proof-trace-toggle')?.classList.toggle('active', open);
  if (open) updateProofTrace();
}
document.getElementById('proof-trace-toggle').onclick = () => setProofTrace(!ui['proof-trace'].classList.contains('open'));
document.getElementById('proof-trace-close').onclick = () => setProofTrace(false);
document.querySelectorAll('[data-proof-view]').forEach(button => button.onclick = () => {
  document.querySelectorAll('[data-proof-view]').forEach(item => item.classList.toggle('active', item === button));
  document.querySelectorAll('.proof-view').forEach(view => view.classList.remove('active'));
  const id = button.dataset.proofView === 'code' ? 'proof-code-view' : 'proof-' + button.dataset.proofView;
  document.getElementById(id)?.classList.add('active');
});
document.getElementById('proof-copy').onclick = async () => {
  await navigator.clipboard.writeText(ui['proof-code'].textContent);
  const button = document.getElementById('proof-copy');
  button.textContent = '已复制'; setTimeout(() => { button.textContent = '复制代码'; }, 1200);
};

const openProof = () => { if (!ui['proof-dialog'].open) ui['proof-dialog'].showModal(); };
document.getElementById('proof-open').onclick = openProof;
document.getElementById('proof-open-panel').onclick = openProof;
document.getElementById('proof-close').onclick = () => ui['proof-dialog'].close();
document.getElementById('result-close').onclick = () => ui['result-dialog'].close();
document.getElementById('result-reset').onclick = () => { ui['result-dialog'].close(); document.getElementById('reset').click(); };
for (const dialog of document.querySelectorAll('dialog')) dialog.addEventListener('click', event => { if (event.target === dialog) dialog.close(); });

if (new URLSearchParams(location.search).has('test')) window.__HRD_TEST__ = {
  setMode: mode => setGraphMode(mode),
  setOverviewVariant: variant => setOverviewVariant(variant),
  expandOrbit,
  expandCorridor,
  selectStart: id => { selectionMode = 'start'; routeStartPinned = true; return selectRouteNode(id); },
  selectEnd: id => { selectionMode = 'end'; return selectRouteNode(id); },
  locateCurrent,
  reheatForce: releaseAndReheatForceGraph,
  pinForce: pinForceReferenceShape,
  forceScreen: id => {
    const node = forceNodePosition(id);
    if (!forceGraph || !node) return null;
    const point = forceGraph.graph2ScreenCoords(node.x, node.y, node.z);
    const rect = ui['graph-force'].getBoundingClientRect();
    return { x: rect.left + point.x, y: rect.top + point.y };
  },
  stop: cancelAnimation,
  state: () => ({
    current, graphMode, overviewVariant, overviewExpansion, routeStart, routeEnd, routeLength: routePath.length,
    explored: exploredNodes.size, shown: exploreNodeIds.length, isAnimating,
    cameraDistance: graphMode === 'force' ? forceCameraDistance() : camera.position.distanceTo(controls.target),
    pointSize: pointCloud?.material.size, sizeAttenuation: pointCloud?.material.sizeAttenuation,
    markerScale: graphMode === 'force' ? forceCurrentMarker?.scale.x : currentMarker?.scale.x,
    forceReady: Boolean(forceGraph), forcePinned, forceNodeCount: forceNodes.length, forceLinkCount: forceLinks.length,
    quotientNodes: overviewGraphs?.quotient.nodes.length, skeletonNodes: overviewGraphs?.skeleton.nodes.length
  })
};
new ResizeObserver(resizeRenderer).observe(ui['graph-wrap']);
window.addEventListener('beforeunload', () => forceGraph?._destructor());
loadGraph().catch(error => { ui.loading.innerHTML = '<strong>三维图载入失败，请刷新页面</strong>'; console.error(error); });
