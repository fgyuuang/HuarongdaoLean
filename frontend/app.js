import * as THREE from './vendor/three.module.min.js';
import { OrbitControls } from './vendor/OrbitControls.js';
import { createLocalTopologyView } from './local-topology-view.js';

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
const query = new URLSearchParams(location.search);
const requestedStateSpace = query.get('space');
const stateSpaceLayer = ['shape', 'mirror', 'corridor'].includes(requestedStateSpace)
  ? requestedStateSpace
  : 'mirror';
const isShapeSpace = stateSpaceLayer === 'shape';
const isMirrorSpace = stateSpaceLayer === 'mirror';
const isCorridorSpace = stateSpaceLayer === 'corridor';
const dataFiles = {
  shape: { graph: 'graph.json', layout: 'layout.json' },
  mirror: { graph: 'graph.mirror.json', layout: 'layout.mirror.json' },
  corridor: { graph: 'graph.corridor.json', layout: 'layout.corridor.json' }
}[stateSpaceLayer];
const ids = 'board state-count edge-count depth-count status-badge node-id distance degree selection last-move graph graph-force graph-wrap loading graph-summary zoom-label explored-count graph-count-label node-tooltip lean-valid lean-goal lean-transition result-dialog result-node result-moves result-distance result-optimal result-certification proof-dialog route-start-id route-end-id force-settings force-settings-toggle force-reset force-rest force-spring force-repulsion force-plane force-node-size force-damping force-line-width force-rest-value force-spring-value force-repulsion-value force-plane-value force-node-size-value force-damping-value force-line-width-value force3d-actions force3d-reheat force3d-pin force3d-status random-walk-toggle random-walk-status quotient-contract quotient-contract-toggle quotient-contract-value state-space-layer proof-trace proof-claim proof-explanation proof-step-list proof-tree proof-code proof-code-status proof-exact-count proof-quotient-count proof-length'.split(' ');
const ui = Object.fromEntries(ids.map(id => [id, document.getElementById(id)]));

let graphData, layoutData, parentGraphData = null, outgoing, shortestGoalDistance = 0, shortestOperationDistance = 0;
let current = 0, selected = null, history = [0], historyKinds = [], historyEdges = [], hintPath = [];
let historyCosts = [], playerMoves = 0, playerOperations = 0, navigationUsed = false, shownGoal = null;
let graphMode = 'overview', selectionMode = 'end', routeStart = 0, routeEnd = null, routePath = [];
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
const exploreGroup = new THREE.Group();
graphGroup.add(overviewGroup, exploreGroup);
scene.add(graphGroup);
const raycaster = new THREE.Raycaster();
raycaster.params.Points.threshold = 0.8;
const pointer = new THREE.Vector2();
let pointCloud = null, overviewPoints = null, overviewEdges = null, overviewMacroEdges = null, overviewEndpointPoints = null, contractionLines = null, explorePoints = null, exploreEdges = null;
let pathLines = null, historyLines = null, currentMarker = null, startMarker = null, endMarker = null, edgePairs = [];
let edgeWeights = new Map(), macroEndpointIds = new Set();
let macroEdgeCount = 0;
let graphPositions = null, graphCenter = new THREE.Vector3(), graphSize = 100, exploreNodeIds = [];
let overviewVisualPositions = null, contractionPairs = [], contractionProgress = 1, contractionAnimationToken = 0;
let pointerDown = null;
let keyboardFocus = 'board';
let graphKeyboardIndex = 0;
let randomWalkTimer = null;
let randomWalkEnabled = false;
let forceGraph = null, forceNodes = [], forceLinks = [], forcePinned = true;
let forceCurrentMarker = null, forceStartMarker = null, forceEndMarker = null, forceHoveredNode = null;
let forceWidth = 0, forceHeight = 0, forceInitialFit = true;
let localTopologyView = null, localTopologyViewPromise = null;
let topologyAnimationToken = 0;
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
function stateSpaceEdgeColor(dark = isDarkTheme()) {
  if (isCorridorSpace) return dark ? '#78bddc' : '#2f789d';
  return dark ? '#76807b' : '#7a857f';
}
function stateSpaceEdgeOpacity(dark = isDarkTheme()) {
  return isCorridorSpace ? (dark ? 0.38 : 0.46) : (dark ? 0.16 : 0.28);
}
function updateSceneTheme() {
  const dark = isDarkTheme();
  scene.background = new THREE.Color(dark ? 0x1b1f1c : 0xf2f3ef);
  if (overviewPoints) overviewPoints.material.color.set(dark ? 0xaab3ae : 0x59635e);
  if (overviewEdges) {
    overviewEdges.material.color.set(dark ? 0x76807b : 0x7a857f);
    overviewEdges.material.opacity = isCorridorSpace ? (dark ? 0.16 : 0.24) : stateSpaceEdgeOpacity(dark);
  }
  if (overviewMacroEdges) {
    overviewMacroEdges.material.color.set(dark ? 0x78bddc : 0x2f789d);
    overviewMacroEdges.material.opacity = dark ? 0.64 : 0.78;
  }
  if (overviewEndpointPoints) {
    overviewEndpointPoints.material.color.set(dark ? 0xf0c36a : 0xc47a1c);
  }
  if (contractionLines) {
    contractionLines.material.color.set(dark ? 0xd6a342 : 0xa66f12);
    const lineBase = dark ? 0.12 : 0.07;
    contractionLines.material.opacity =
      lineBase * (0.25 + 0.75 * Math.sin(Math.PI * contractionProgress));
  }
  if (forceGraph) {
    forceGraph
      .backgroundColor(dark ? '#1b1f1c' : '#f2f3ef')
      .nodeColor(forceNodeColor)
      .linkColor(link => link.macro ? (dark ? '#78bddc' : '#2f789d') : (dark ? '#76807b' : '#7a857f'))
      .refresh();
  }
  if (graphData && graphPositions) rebuildExploreGraph();
  if (currentMarker) updateGraphState();
}
updateSceneTheme();

async function loadGraph() {
  ui['state-space-layer'].value = stateSpaceLayer;
  const requests = [fetch(dataFiles.graph), fetch(dataFiles.layout)];
  if (isCorridorSpace) requests.push(fetch('graph.mirror.json'));
  const [graphResponse, layoutResponse, parentResponse] = await Promise.all(requests);
  if (!graphResponse.ok) throw new Error(`${dataFiles.graph} unavailable`);
  if (!layoutResponse.ok) throw new Error(`${dataFiles.layout} unavailable`);
  graphData = await graphResponse.json();
  layoutData = await layoutResponse.json();
  if (parentResponse) {
    if (!parentResponse.ok) throw new Error('graph.mirror.json unavailable');
    parentGraphData = await parentResponse.json();
  }
  if (layoutData.coordinates.length !== graphData.states.length) throw new Error('Layout/state count mismatch');
  outgoing = Array.from({ length: graphData.states.length }, () => []);
  for (const edge of graphData.edges) outgoing[edge.source].push(edge);
  ui['state-count'].textContent = graphData.meta.stateCount.toLocaleString();
  ui['edge-count'].textContent = graphData.meta.edgeCount.toLocaleString();
  ui['depth-count'].textContent = Math.max(...graphData.states.map(state =>
    isCorridorSpace ? state.operationDistance : state.distance));
  ui['explored-count'].textContent = graphData.states.length.toLocaleString();
  shortestGoalDistance = graphData.meta.primitiveShortestGoalDistance ??
    Math.min(...graphData.states.filter(state => state.goal).map(state => state.distance));
  shortestOperationDistance = graphData.meta.operationShortestGoalDistance || shortestGoalDistance;
  document.documentElement.dataset.stateSpace = stateSpaceLayer;
  ui['quotient-contract']?.closest('.quotient-contraction')?.toggleAttribute('hidden', !isMirrorSpace);
  document.getElementById('macro-edge-legend')?.toggleAttribute('hidden', !isCorridorSpace);
  document.getElementById('macro-endpoint-legend')?.toggleAttribute('hidden', !isCorridorSpace);
  buildFullGraph();
  syncRouteControls();
  const loadingTitle = ui.loading?.querySelector('strong');
  if (loadingTitle) loadingTitle.textContent = `载入 ${graphData.meta.stateCount.toLocaleString()} 个状态节点`;
  ui.loading.classList.add('hidden');
  renderState(0, false);
  requestAnimationFrame(fitGraph);
}

function renderState(id, pushHistory = true, moveText = '', transitionKind = 'graph', transitionEdge = null) {
  if (!graphData?.states[id]) return;
  const previous = current;
  const changed = previous !== id;
  if (changed) recordExploration(previous, id);
  current = id;
  if (changed && pushHistory) {
    if (history.at(-1) !== id) {
      history.push(id);
      historyKinds.push(transitionKind);
      const traversedEdge = transitionEdge ||
        outgoing[previous]?.find(edge => edge.target === id) || null;
      historyEdges.push(traversedEdge);
      const primitiveCost = traversedEdge?.weight || 1;
      historyCosts.push(primitiveCost);
      if (transitionKind === 'move') {
        playerMoves += primitiveCost;
        playerOperations += 1;
      }
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
  ui.distance.textContent = isCorridorSpace
    ? state.primitiveDistance + ' 步 / ' + state.operationDistance + ' 操作'
    : state.distance + ' 步';
  ui.degree.textContent = outgoing[id].length;
  ui['last-move'].textContent = moveText || (state.goal ? '曹操已到达出口' : '三维探索图已同步');
  ui['status-badge'].textContent = state.goal ? '已完成' : '探索中';
  ui['status-badge'].classList.toggle('goal', state.goal);
  ui['lean-valid'].innerHTML = '<i></i>true';
  ui['lean-goal'].textContent = String(state.goal);
  const latestKind = changed && pushHistory ? transitionKind : historyKinds.at(-1);
  ui['lean-transition'].textContent = isCorridorSpace && changed
    ? 'CorridorMacroStep'
    : latestKind === 'move' || latestKind === 'route' ? 'tryMove = some' : latestKind === 'graph' ? 'BFS reachable' : 'initial';
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
  const macroText = edge.weight > 1 ? ' · 归并 ' + edge.weight + ' 步' : '';
  renderState(edge.target, true, '随机游走：' + pieces[edge.piece].label + '向' + edge.direction + macroText + ' · #' + edge.target, 'move', edge);
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
  const macroText = edge.weight > 1 ? ' · 决策骨架将 ' + edge.weight + ' 步归并为一次操作' : '';
  renderState(edge.target, true, pieces[selected].label + '向' + direction + macroText + ' · #' + edge.target, 'move', edge);
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
  const macroText = edge.weight > 1 ? ' · ' + edge.weight + ' 个底层步骤' : '';
  renderState(edge.target, true, '状态图键盘前进：' + direction + macroText + ' · #' + current + ' → #' + edge.target, 'graph', edge);
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
    const removedCost = historyCosts.pop() || 1;
    historyEdges.pop();
    if (removedKind === 'move') {
      playerMoves = Math.max(0, playerMoves - removedCost);
      playerOperations = Math.max(0, playerOperations - 1);
    }
    navigationUsed = historyKinds.some(kind => kind !== 'move');
    renderState(history.at(-1), false, '已撤回，探索图保留已发现节点');
  }
};
document.getElementById('reset').onclick = () => {
  cancelAnimation();
  stopRandomWalk();
  history = [0]; historyKinds = []; historyEdges = []; historyCosts = []; hintPath = []; selected = null; current = 0;
  playerMoves = 0; playerOperations = 0; navigationUsed = false; shownGoal = null;
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
    ui['last-move'].textContent = '已规划到最近终点：' + (hintPath.length - 1) +
      (isCorridorSpace ? ' 次归并操作' : ' 步') + '；点击“导航到终点”或按 Enter 播放';
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

function buildFullGraph() {
  const count = graphData.states.length;
  const raw = layoutData.coordinates;
  const rawPairs = isMirrorSpace && layoutData.mirrorPairs?.length === count
    ? layoutData.mirrorPairs
    : raw.map(coordinate => ({ a: coordinate.slice(0, 3), b: coordinate.slice(0, 3), fixed: true }));
  const min = [Infinity, Infinity, Infinity], max = [-Infinity, -Infinity, -Infinity];
  for (const pair of rawPairs) for (const coordinate of [pair.a, pair.b]) for (let axis = 0; axis < 3; axis += 1) {
    min[axis] = Math.min(min[axis], coordinate[axis]);
    max[axis] = Math.max(max[axis], coordinate[axis]);
  }
  const center = min.map((value, axis) => (value + max[axis]) / 2);
  const scale = 110 / Math.max(...max.map((value, axis) => value - min[axis]));
  graphPositions = new Float32Array(count * 3);
  contractionPairs = [];
  let visualCount = count;
  for (const pair of rawPairs) if (!pair.fixed) visualCount += 1;
  overviewVisualPositions = new Float32Array(visualCount * 3);
  const overviewNodeIds = new Int32Array(visualCount);

  for (let id = 0; id < count; id += 1) {
    const merged = raw[id].slice(0, 3).map((value, axis) => (value - center[axis]) * scale);
    graphPositions.set(merged, id * 3);
    overviewVisualPositions.set(merged, id * 3);
    overviewNodeIds[id] = id;
  }

  let ghostIndex = count;
  for (let id = 0; id < count; id += 1) {
    const pair = rawPairs[id];
    if (pair.fixed) continue;
    const a = pair.a.map((value, axis) => (value - center[axis]) * scale);
    const b = pair.b.map((value, axis) => (value - center[axis]) * scale);
    const merged = Array.from(graphPositions.subarray(id * 3, id * 3 + 3));
    overviewVisualPositions.set(merged, ghostIndex * 3);
    overviewNodeIds[ghostIndex] = id;
    contractionPairs.push({ nodeId: id, mainIndex: id, ghostIndex, a, b, merged });
    ghostIndex += 1;
  }

  const pointGeometry = new THREE.BufferGeometry();
  pointGeometry.setAttribute('position', new THREE.BufferAttribute(overviewVisualPositions, 3));
  overviewPoints = new THREE.Points(pointGeometry, new THREE.PointsMaterial({ color: 0xaab3ae, size: 2.1, sizeAttenuation: false, map: pointTexture, alphaTest: 0.45, transparent: true, opacity: 0.84, depthWrite: false }));
  overviewPoints.userData.nodeIds = overviewNodeIds;
  overviewGroup.add(overviewPoints);

  const contractionGeometry = new THREE.BufferGeometry();
  contractionGeometry.setAttribute('position', new THREE.BufferAttribute(new Float32Array(contractionPairs.length * 6), 3));
  contractionLines = new THREE.LineSegments(contractionGeometry, new THREE.LineBasicMaterial({ color: 0xa66f12, transparent: true, opacity: 0.045, depthWrite: false }));
  overviewGroup.add(contractionLines);

  const seen = new Set(); edgeWeights = new Map(); macroEndpointIds = new Set(); edgePairs = [];
  for (const edge of graphData.edges) {
    const key = edgeKey(edge.source, edge.target);
    const weight = Math.max(edgeWeights.get(key) || 1, edge.weight || 1);
    edgeWeights.set(key, weight);
    if (!seen.has(key)) {
      seen.add(key);
      edgePairs.push([edge.source, edge.target]);
    }
  }
  if (isCorridorSpace) {
    for (const [source, target] of edgePairs) {
      if ((edgeWeights.get(edgeKey(source, target)) || 1) <= 1) continue;
      macroEndpointIds.add(source);
      macroEndpointIds.add(target);
    }
  }
  const ordinaryEdges = edgePairs.filter(([source, target]) => (edgeWeights.get(edgeKey(source, target)) || 1) === 1);
  const macroEdges = edgePairs.filter(([source, target]) => (edgeWeights.get(edgeKey(source, target)) || 1) > 1);
  macroEdgeCount = macroEdges.length;
  function edgeGeometryFor(pairs) {
    const positions = new Float32Array(pairs.length * 6);
    pairs.forEach(([source, target], index) => {
      positions.set(graphPositions.subarray(source * 3, source * 3 + 3), index * 6);
      positions.set(graphPositions.subarray(target * 3, target * 3 + 3), index * 6 + 3);
    });
    const geometry = new THREE.BufferGeometry();
    geometry.setAttribute('position', new THREE.BufferAttribute(positions, 3));
    return geometry;
  }
  overviewEdges = new THREE.LineSegments(edgeGeometryFor(ordinaryEdges), new THREE.LineBasicMaterial({
    color: isDarkTheme() ? 0x76807b : 0x7a857f,
    transparent: true,
    opacity: isCorridorSpace ? (isDarkTheme() ? 0.16 : 0.24) : stateSpaceEdgeOpacity(),
    depthWrite: false
  }));
  overviewGroup.add(overviewEdges);
  overviewMacroEdges = new THREE.LineSegments(edgeGeometryFor(macroEdges), new THREE.LineBasicMaterial({
    color: isDarkTheme() ? 0x78bddc : 0x2f789d,
    transparent: true,
    opacity: isDarkTheme() ? 0.64 : 0.78,
    depthWrite: false
  }));
  overviewGroup.add(overviewMacroEdges);
  if (isCorridorSpace && macroEndpointIds.size) {
    const endpointPositions = new Float32Array(macroEndpointIds.size * 3);
    [...macroEndpointIds].forEach((id, index) => endpointPositions.set(graphPositions.subarray(id * 3, id * 3 + 3), index * 3));
    const endpointGeometry = new THREE.BufferGeometry();
    endpointGeometry.setAttribute('position', new THREE.BufferAttribute(endpointPositions, 3));
    overviewEndpointPoints = new THREE.Points(endpointGeometry, new THREE.PointsMaterial({
      color: isDarkTheme() ? 0xf0c36a : 0xc47a1c,
      size: 5.2,
      sizeAttenuation: false,
      map: pointTexture,
      alphaTest: 0.35,
      transparent: true,
      opacity: 0.98,
      depthWrite: false
    }));
    overviewGroup.add(overviewEndpointPoints);
  }

  currentMarker = makeRingMarker('#9f2d2d', '#ffffff', 22);
  startMarker = makeRingMarker('#d6a342', '#6f531f', 16);
  endMarker = makeRingMarker('#4ac6b8', '#1f6e66', 16);
  graphGroup.add(currentMarker, startMarker, endMarker);
  graphCenter.set(0, 0, 0); graphSize = 110;
  updateQuotientContraction(1);
  prepareForceGraphData();
  rebuildExploreGraph();
  setGraphMode('overview', false);
  updateSceneTheme();
}

function updateQuotientContraction(value) {
  contractionProgress = THREE.MathUtils.clamp(Number(value) || 0, 0, 1);
  if (overviewVisualPositions && overviewPoints && contractionLines) {
    const linePositions = contractionLines.geometry.attributes.position.array;
    for (let index = 0; index < contractionPairs.length; index += 1) {
      const pair = contractionPairs[index];
      const main = pair.a.map((coordinate, axis) =>
        THREE.MathUtils.lerp(coordinate, pair.merged[axis], contractionProgress));
      const ghost = pair.b.map((coordinate, axis) =>
        THREE.MathUtils.lerp(coordinate, pair.merged[axis], contractionProgress));
      overviewVisualPositions.set(main, pair.mainIndex * 3);
      overviewVisualPositions.set(ghost, pair.ghostIndex * 3);
      linePositions.set(main, index * 6);
      linePositions.set(ghost, index * 6 + 3);
    }
    overviewPoints.geometry.attributes.position.needsUpdate = true;
    contractionLines.geometry.attributes.position.needsUpdate = true;
    const lineBase = isDarkTheme() ? 0.12 : 0.07;
    contractionLines.material.opacity =
      lineBase * (0.25 + 0.75 * Math.sin(Math.PI * contractionProgress));
    contractionLines.visible = contractionProgress < 0.999;
  }
  if (ui['quotient-contract']) ui['quotient-contract'].value = Math.round(contractionProgress * 100);
  if (ui['quotient-contract-value']) ui['quotient-contract-value'].textContent = Math.round(contractionProgress * 100) + '%';
  if (ui['quotient-contract-toggle']) ui['quotient-contract-toggle'].textContent = contractionProgress >= 0.5 ? '展开' : '合并';
  if (graphMode === 'overview' && graphData) {
    if (isCorridorSpace) {
      ui['graph-count-label'].textContent = '关键节点';
      ui['explored-count'].textContent = graphData.states.length.toLocaleString();
      ui['graph-summary'].textContent = '决策骨架 · 当前 #' + current + ' · ' +
        macroEdgeCount.toLocaleString() + ' 条蓝色归并边 · ' +
        (edgePairs.length - macroEdgeCount).toLocaleString() + ' 条灰色单步边 · ' +
        graphData.meta.suppressedStateCount.toLocaleString() + ' 个中间状态已隐藏';
      return;
    }
    if (isShapeSpace) {
      ui['graph-count-label'].textContent = '同形商节点';
      ui['explored-count'].textContent = graphData.states.length.toLocaleString();
      ui['graph-summary'].textContent = '同形标签商 · 当前 #' + current + ' · ' +
        graphData.states.length.toLocaleString() + ' 个状态 · ' +
        edgePairs.length.toLocaleString() + ' 条显示边';
      return;
    }
    const visualCount = graphData.states.length + (contractionProgress < 0.999 ? contractionPairs.length : 0);
    ui['graph-count-label'].textContent = contractionProgress < 0.999 ? '原图点位' : '商图节点';
    ui['explored-count'].textContent = visualCount.toLocaleString();
    ui['graph-summary'].textContent = '镜像两端向中点粘连 · 当前 #' + current + ' · 合并度 ' + Math.round(contractionProgress * 100) + '% · ' + edgePairs.length.toLocaleString() + ' 条商边';
  }
}

function animateQuotientContraction(target) {
  const start = contractionProgress;
  const token = ++contractionAnimationToken;
  const startedAt = performance.now();
  const duration = 720;
  function frame(now) {
    if (token !== contractionAnimationToken) return;
    const elapsed = Math.min(1, (now - startedAt) / duration);
    const eased = elapsed < 0.5 ? 2 * elapsed * elapsed : 1 - Math.pow(-2 * elapsed + 2, 2) / 2;
    updateQuotientContraction(THREE.MathUtils.lerp(start, target, eased));
    if (elapsed < 1) requestAnimationFrame(frame);
  }
  requestAnimationFrame(frame);
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
    return {
      source,
      target,
      macro: isCorridorSpace && (edgeWeights.get(edgeKey(source, target)) || 1) > 1,
      restLength: Math.max(0.8, Math.min(80, restLength))
    };
  });
}

function forceNodeColor(node) {
  if (isCorridorSpace && macroEndpointIds.has(Number(node.id))) return isDarkTheme() ? '#f0c36a' : '#c47a1c';
  if (node.goal) return isDarkTheme() ? '#56c7b9' : '#28736d';
  if (node.goalDistance <= 20) return isDarkTheme() ? '#d4a651' : '#9a6b25';
  return isDarkTheme() ? '#aab3ae' : '#59635e';
}

function renderTopologyBoard(state, moveText = '局部拓扑样本中心') {
  ui.board.replaceChildren();
  state.positions.forEach(([x, y], index) => {
    const spec = pieces[index];
    const wrap = document.createElement('div');
    wrap.className = 'piece ' + spec.cls;
    Object.assign(wrap.style, { left: x * 25 + '%', top: y * 20 + '%', width: spec.w * 25 + '%', height: spec.h * 20 + '%' });
    const button = document.createElement('button');
    button.textContent = spec.label;
    button.tabIndex = -1;
    wrap.append(button);
    ui.board.append(wrap);
  });
  ui['node-id'].textContent = '#' + state.id;
  ui.distance.textContent = state.distance + ' 步';
  ui.degree.textContent = '局部样本';
  ui['last-move'].textContent = moveText;
  ui['lean-transition'].textContent = 'ShapeStep';
  ui['lean-goal'].textContent = String(state.goal);
}

async function animateTopologyBoardPath({ start, target, steps }) {
  const token = ++topologyAnimationToken;
  if (!steps.length) {
    renderTopologyBoard(target);
    return;
  }
  renderTopologyBoard(start, '局部路径起点 #' + start.id);
  for (let index = 0; index < steps.length; index += 1) {
    await wait(90);
    if (token !== topologyAnimationToken || graphMode !== 'topology') return;
    const { state, edge } = steps[index];
    renderTopologyBoard(state, '局部路径 ' + (index + 1) + '/' + steps.length + '：' + pieces[edge.piece].label + '向' + edge.direction + ' · #' + state.id);
  }
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

function preferredFocusTargetId() {
  if (routeEnd !== null && graphData?.states[routeEnd]) return routeEnd;
  if (!graphData?.states?.length) return current;
  let bestId = null, bestDistance = Infinity;
  for (const state of graphData.states) {
    if (!state.goal) continue;
    const distance = isCorridorSpace
      ? (state.primitiveDistance ?? state.distance ?? Infinity)
      : (state.distance ?? Infinity);
    if (distance < bestDistance) {
      bestId = state.id;
      bestDistance = distance;
    }
  }
  return bestId ?? current;
}

function radiusAroundFlatPositions(target, positions) {
  let radiusSquared = 1;
  for (let index = 0; index < positions.length; index += 3) {
    const dx = positions[index] - target.x;
    const dy = positions[index + 1] - target.y;
    const dz = positions[index + 2] - target.z;
    radiusSquared = Math.max(radiusSquared, dx * dx + dy * dy + dz * dz);
  }
  return Math.sqrt(radiusSquared);
}

function targetCenteredFitDistance(radius, cameraObject, padding = 1.12) {
  const verticalFov = THREE.MathUtils.degToRad(cameraObject.fov || 45);
  const horizontalFov = 2 * Math.atan(Math.tan(verticalFov / 2) * Math.max(0.01, cameraObject.aspect || 1));
  const limitingFov = Math.min(verticalFov, horizontalFov);
  return radius * padding / Math.sin(limitingFov / 2);
}

function cameraDirection(position, target, fallback = new THREE.Vector3(0.78, 0.48, 0.96), focusToCenter = null) {
  const direction = new THREE.Vector3(position.x - target.x, position.y - target.y, position.z - target.z);
  if (direction.lengthSq() <= 1e-8) direction.copy(fallback);
  direction.normalize();
  if (focusToCenter?.lengthSq() > 1e-8) {
    const graphAxis = focusToCenter.clone().normalize();
    const alignment = direction.dot(graphAxis);
    if (Math.abs(alignment) > 0.72) {
      direction.addScaledVector(graphAxis, -alignment);
      if (direction.lengthSq() <= 1e-8) {
        const reference = Math.abs(graphAxis.y) < 0.9 ? new THREE.Vector3(0, 1, 0) : new THREE.Vector3(1, 0, 0);
        direction.crossVectors(reference, graphAxis);
      }
      direction.normalize();
    }
  }
  return direction;
}

function fitForceGraphToTarget(duration = 700) {
  const graph = ensureForceGraph();
  const focusNode = forceNodePosition(preferredFocusTargetId());
  if (!focusNode) return;
  const target = { x: focusNode.x, y: focusNode.y, z: focusNode.z };
  let radius = 1;
  for (const node of forceNodes) {
    if (![node.x, node.y, node.z].every(Number.isFinite)) continue;
    radius = Math.max(radius, Math.hypot(node.x - target.x, node.y - target.y, node.z - target.z));
  }
  const forceCenter = forceNodes.reduce((sum, node) => {
    if ([node.x, node.y, node.z].every(Number.isFinite)) sum.add(new THREE.Vector3(node.x, node.y, node.z));
    return sum;
  }, new THREE.Vector3()).multiplyScalar(1 / Math.max(1, forceNodes.length));
  const cameraObject = graph.camera();
  const distance = Math.max(80, targetCenteredFitDistance(radius, cameraObject));
  const direction = cameraDirection(
    graph.cameraPosition(),
    graph.controls().target || { x: 0, y: 0, z: 0 },
    undefined,
    forceCenter.sub(new THREE.Vector3(target.x, target.y, target.z))
  );
  cameraObject.far = Math.max(cameraObject.far, distance + radius * 2);
  cameraObject.updateProjectionMatrix();
  graph.cameraPosition({
    x: target.x + direction.x * distance,
    y: target.y + direction.y * distance,
    z: target.z + direction.z * distance
  }, target, duration);
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
  ui['force3d-status'].textContent = graphData ? `正在创建 ${graphData.meta.stateCount.toLocaleString()} 个 3D 节点` : '正在创建 3D 节点';
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
    .linkColor(link => link.macro
      ? (isDarkTheme() ? '#78bddc' : '#2f789d')
      : (isDarkTheme() ? '#76807b' : '#7a857f'))
    .linkOpacity(isCorridorSpace ? 0.24 : 0.075)
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
        requestAnimationFrame(() => fitForceGraphToTarget());
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
  return target.fromArray(graphPositions, id * 3);
}
function recordExploration(from, to) {
  exploredNodes.add(from); exploredNodes.add(to);
  const edge = outgoing[from]?.find(item => item.target === to) || outgoing[to]?.find(item => item.target === from);
  if (edge) {
    const key = edgeKey(from, to);
    exploredEdges.set(key, {
      source: from,
      target: to,
      macro: isCorridorSpace && (edgeWeights.get(key) || edge.weight || 1) > 1
    });
  }
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
  for (const { source, target } of exploreForce.edges) {
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
    exploreForce.edges.forEach(({ source, target }, index) => {
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
    const key = edgeKey(edge.source, edge.target);
    shownEdges.set(key, {
      source: edge.source,
      target: edge.target,
      macro: isCorridorSpace && (edgeWeights.get(key) || edge.weight || 1) > 1
    });
  }
  exploreNodeIds = [...nodeSet];
  const positions = new Float32Array(exploreNodeIds.length * 3);
  const colors = new Float32Array(exploreNodeIds.length * 3);
  const dark = isDarkTheme();
  const discoveredColor = new THREE.Color(dark ? 0xd3dbd7 : 0x34443d);
  const frontierColor = new THREE.Color(dark ? 0x61706a : 0x7a8982);
  const endpointColor = new THREE.Color(dark ? 0xf0c36a : 0xc47a1c);
  exploreNodeIds.forEach((id, index) => {
    const position = seedExplorePosition(id, index);
    positions.set(position.toArray(), index * 3);
    const color = isCorridorSpace && macroEndpointIds.has(id)
      ? endpointColor
      : exploredNodes.has(id) ? discoveredColor : frontierColor;
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
  exploreForce.edges = edges.map(edge => ({
    source: edge.source,
    target: edge.target,
    macro: Boolean(edge.macro)
  }));
  const linePositions = new Float32Array(edges.length * 6);
  const lineColors = new Float32Array(edges.length * 6);
  const ordinaryColor = new THREE.Color(dark ? 0xa9b8b1 : 0x65766e);
  const macroColor = new THREE.Color(dark ? 0x78bddc : 0x2f789d);
  edges.forEach((edge, index) => {
    linePositions.set(exploreForce.positions.get(edge.source).toArray(), index * 6);
    linePositions.set(exploreForce.positions.get(edge.target).toArray(), index * 6 + 3);
    const color = edge.macro ? macroColor : ordinaryColor;
    lineColors.set([color.r, color.g, color.b, color.r, color.g, color.b], index * 6);
  });
  const lineGeometry = new THREE.BufferGeometry();
  lineGeometry.setAttribute('position', new THREE.BufferAttribute(linePositions, 3));
  lineGeometry.setAttribute('color', new THREE.BufferAttribute(lineColors, 3));
  exploreEdges = new THREE.LineSegments(lineGeometry, new THREE.LineBasicMaterial({
    color: 0xffffff,
    vertexColors: true,
    transparent: true,
    opacity: isCorridorSpace ? 0.68 : (dark ? 0.52 : 0.42),
    depthWrite: false
  }));
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
function updateGraphState() {
  if (!graphPositions || !currentMarker) return;
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
    updateQuotientContraction(contractionProgress);
    if (isCorridorSpace) {
      ui['graph-summary'].textContent = '决策骨架 · 当前 #' + current + ' · ' +
        macroEdgeCount.toLocaleString() + ' 条蓝色归并边 · ' +
        (edgePairs.length - macroEdgeCount).toLocaleString() + ' 条灰色单步边 · ' +
        graphData.meta.suppressedStateCount.toLocaleString() + ' 个中间状态已隐藏 · 加权最短距离保持 ' + shortestGoalDistance;
    } else if (isShapeSpace) {
      ui['graph-summary'].textContent = '同形标签商 · 当前 #' + current + ' · ' +
        graphData.states.length.toLocaleString() + ' 个状态 · ' +
        edgePairs.length.toLocaleString() + ' 条显示边';
    } else {
      ui['graph-summary'].textContent = '镜像两端向中点粘连 · 当前 #' + current + ' · 合并度 ' +
        Math.round(contractionProgress * 100) + '% · ' + edgePairs.length.toLocaleString() + ' 条商边';
    }
  } else if (graphMode === 'force') {
    ui['explored-count'].textContent = graphData.states.length.toLocaleString();
    ui['graph-summary'].textContent = '3d-force-graph · 当前 #' + current + ' · ' + (forcePinned ? '参考坐标固定' : 'd3-force-3d 有限松弛') + ' · ' + edgePairs.length.toLocaleString() + ' 条连接';
  }
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
    ui['last-move'].textContent = '从当前节点 #' + routeStart + ' → #' + routeEnd + '，共 ' +
      Math.max(0, routePath.length - 1) + (isCorridorSpace ? ' 次归并操作' : ' 条合法边');
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
    const macroText = edge.weight > 1 ? ' · 展开为 ' + edge.weight + ' 个镜像商步骤' : '';
    renderState(to, true, '路径动画 ' + index + '/' + (sequence.length - 1) + '：' +
      pieces[edge.piece].label + '向' + edge.direction + macroText, 'route', edge);
    await wait(55);
  }
  if (token !== animationToken) return;
  isAnimating = false; suppressCompletion = false; syncRouteControls();
  const primitiveCost = sequence.slice(1).reduce((sum, target, index) => {
    const edge = outgoing[sequence[index]].find(item => item.target === target);
    return sum + (edge?.weight || 1);
  }, 0);
  ui['last-move'].textContent = isCorridorSpace
    ? '已执行 ' + (sequence.length - 1) + ' 次归并操作，展开为 ' + primitiveCost + ' 条镜像商边，到达 #' + current
    : '已沿 ' + primitiveCost + ' 条 Lean 合法边到达 #' + current;
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
  if (!['overview', 'force', 'explore', 'topology'].includes(mode)) return;
  const previousMode = graphMode;
  if (previousMode === 'topology' && mode !== 'topology') {
    topologyAnimationToken += 1;
    renderState(current, false);
  }
  if (previousMode === 'force' && mode !== 'force' && forceGraph) forceGraph.pauseAnimation();
  graphMode = mode;
  if (ui['quotient-contract']) ui['quotient-contract'].disabled = mode !== 'overview' || !isMirrorSpace;
  if (ui['quotient-contract-toggle']) ui['quotient-contract-toggle'].disabled = mode !== 'overview' || !isMirrorSpace;
  overviewGroup.visible = mode === 'overview'; exploreGroup.visible = mode === 'explore';
  pointCloud = mode === 'overview' ? overviewPoints : mode === 'explore' ? explorePoints : null;
  ui.graph.hidden = mode === 'force' || mode === 'topology';
  ui['graph-force'].hidden = mode !== 'force';
  document.getElementById('local-topology-view').hidden = mode !== 'topology';
  ui['force3d-actions'].hidden = mode !== 'force';
  ui['graph-wrap'].dataset.mode = mode;
  ui['force-settings-toggle'].hidden = mode !== 'explore';
  if (mode !== 'explore') ui['force-settings'].hidden = true;
  document.querySelectorAll('[data-mode]').forEach(button => button.classList.toggle('active', button.dataset.mode === mode));
  ui['graph-count-label'].textContent = mode === 'explore' ? '当前织图节点' : '完整图节点';
  if (mode === 'explore') rebuildExploreGraph();
  if (mode === 'topology') {
    setProofTrace(false);
    localTopologyViewPromise ||= createLocalTopologyView(document.getElementById('local-topology-view'), { onPath: animateTopologyBoardPath })
      .then(view => { localTopologyView = view; view.setActive(graphMode === 'topology'); return view; })
      .catch(error => {
        document.querySelector('.local-topology-loading').textContent = '局部子图载入失败';
        console.error(error);
      });
  }
  localTopologyView?.setActive(mode === 'topology');
  updateGraphState();
  if (mode === 'force') {
    requestAnimationFrame(() => {
      try {
        const graph = ensureForceGraph();
        graph.resumeAnimation();
        resizeRenderer();
        syncForceMarkerPositions();
        syncForceMarkerScales();
        if (refit && !forceInitialFit) fitForceGraphToTarget();
      } catch (error) {
        ui['force3d-status'].textContent = '3d-force-graph 初始化失败';
        console.error(error);
      }
    });
  } else if (mode === 'topology') {
    if (refit) localTopologyViewPromise?.then(view => view?.fit());
  } else if (refit) requestAnimationFrame(fitGraph);
}

function fitGraph() {
  if (graphMode === 'topology') {
    localTopologyView?.fit();
    return;
  }
  if (graphMode === 'force') {
    fitForceGraphToTarget();
    return;
  }
  if (graphMode === 'explore' && exploreGroup.children.length) {
    const box = new THREE.Box3().setFromObject(exploreGroup);
    const center = box.getCenter(new THREE.Vector3());
    const dimensions = box.getSize(new THREE.Vector3());
    const size = Math.max(4, dimensions.length());
    controls.target.copy(center);
    camera.position.copy(center).add(new THREE.Vector3(0, 0, Math.max(12, size * 1.18)));
    camera.near = 0.05; camera.far = 1200; camera.updateProjectionMatrix(); controls.update();
    ui['zoom-label'].textContent = Math.round(camera.position.distanceTo(controls.target)) + 'u';
    return;
  }
  const focusTarget = nodePosition(preferredFocusTargetId(), new THREE.Vector3());
  const positions = overviewVisualPositions || graphPositions;
  const radius = radiusAroundFlatPositions(focusTarget, positions);
  const distance = targetCenteredFitDistance(radius, camera);
  const direction = cameraDirection(camera.position, controls.target, undefined, graphCenter.clone().sub(focusTarget));
  controls.target.copy(focusTarget);
  camera.position.copy(focusTarget).add(direction.multiplyScalar(distance));
  controls.maxDistance = Math.max(600, distance * 1.25);
  camera.near = 0.05;
  camera.far = Math.max(1200, distance + radius * 2);
  camera.updateProjectionMatrix();
  controls.update();
  ui['zoom-label'].textContent = Math.round(camera.position.distanceTo(controls.target)) + 'u';
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
  const rect = renderer.domElement.getBoundingClientRect();
  pointer.x = ((event.clientX - rect.left) / rect.width) * 2 - 1;
  pointer.y = -((event.clientY - rect.top) / rect.height) * 2 + 1;
  raycaster.setFromCamera(pointer, camera);
  raycaster.params.Points.threshold = Math.max(0.12, camera.position.distanceTo(controls.target) / (graphMode === 'explore' ? 105 : 170));
  return raycaster.intersectObject(pointCloud, false)[0];
}
renderer.domElement.addEventListener('pointerdown', event => { pointerDown = { x: event.clientX, y: event.clientY }; });
renderer.domElement.addEventListener('pointerup', event => {
  if (!pointerDown || Math.hypot(event.clientX - pointerDown.x, event.clientY - pointerDown.y) > 5) return;
  const hit = pickNode(event);
  if (hit) {
    const id = pointCloud.userData.nodeIds ? pointCloud.userData.nodeIds[hit.index] : hit.index;
    selectRouteNode(id);
  }
});
renderer.domElement.addEventListener('pointermove', event => {
  const hit = pointCloud ? pickNode(event) : null;
  ui['node-tooltip'].classList.toggle('visible', Boolean(hit));
  if (hit) {
    const id = pointCloud.userData.nodeIds ? pointCloud.userData.nodeIds[hit.index] : hit.index;
    ui['node-tooltip'].textContent = '#' + id + ' · 起点距离 ' + graphData.states[id].distance + ' · 目标距离 ' + layoutData.coordinates[id][3];
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
  ui['zoom-label'].textContent = Math.round(camera.position.distanceTo(controls.target)) + 'u';
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
ui['quotient-contract']?.addEventListener('input', event => {
  contractionAnimationToken += 1;
  updateQuotientContraction(Number(event.target.value) / 100);
  updateGraphState();
});
ui['quotient-contract-toggle']?.addEventListener('click', () => {
  animateQuotientContraction(contractionProgress >= 0.5 ? 0 : 1);
});
ui['state-space-layer']?.addEventListener('change', event => {
  const nextUrl = new URL(location.href);
  if (event.target.value === 'mirror') nextUrl.searchParams.delete('space');
  else nextUrl.searchParams.set('space', event.target.value);
  nextUrl.searchParams.delete('view');
  location.href = nextUrl.toString();
});
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
  let primitiveIndex = 0;
  for (let i = 1; i < history.length; i += 1) {
    const sourceId = history[i - 1], targetId = history[i];
    const edge = historyEdges[i - 1] ||
      (outgoing[sourceId] || []).find(candidate => candidate.target === targetId);
    if (!edge) continue;
    const primitiveEdges = edge.steps?.length ? edge.steps : [edge];
    for (const primitiveEdge of primitiveEdges) {
      primitiveIndex += 1;
      const primitiveSourceId = primitiveEdge.source;
      const primitiveTargetId = primitiveEdge.target;
      const source = isCorridorSpace
        ? parentGraphData.states[primitiveSourceId]
        : graphData.states[primitiveSourceId];
      const target = isCorridorSpace
        ? parentGraphData.states[primitiveTargetId]
        : graphData.states[primitiveTargetId];
      const actual = movedPositions(source, primitiveEdge);
      const exact = samePositions(actual, target.positions);
      steps.push({
        index: primitiveIndex,
        macroIndex: i,
        macroWeight: edge.weight || 1,
        sourceId: primitiveSourceId,
        targetId: primitiveTargetId,
        source,
        target,
        edge: primitiveEdge,
        actual,
        exact,
        sameShape: exact || sameShapePositions(actual, target.positions)
      });
    }
  }
  return steps;
}
function leanAction(step) {
  return '⟨.' + leanPieceNames[step.edge.piece] + ', .' + leanDirectionNames[step.edge.direction] + '⟩';
}
function generatedProofCode(steps, quotient) {
  if (isCorridorSpace) {
    return `-- ${history.length - 1} corridor operations expand to ${steps.length} mirror-quotient steps.
def currentCorridorWalk :
    corridorTask.Walk corridorTask.initial currentAnchor :=
  corridorCertificate

def currentMirrorWalk :
    MirrorShapeWalk mirrorShapeInitial currentAnchor.1 :=
  corridorWalkExpand currentCorridorWalk

example : currentMirrorWalk.length =
    currentCorridorWalk.actions.sum :=
  corridorWalkExpand_length currentCorridorWalk`;
  }
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
  const claimType = isCorridorSpace
    ? 'corridorTask.Walk anchor0 anchor' + target
    : goal ? (quotient ? 'QSolution state0' : (navigationUsed ? 'Solution state0' : 'CertifiedPlay state0')) : (quotient ? 'QPath state0 state' + target : 'Path state0 state' + target);
  ui['proof-claim'].textContent = claimType;
  ui['proof-explanation'].textContent = isCorridorSpace
    ? '当前记录包含 ' + Math.max(0, history.length - 1) + ' 次 CorridorMacroStep；经 corridorWalkExpand 展开为 ' + steps.length + ' 个 MirrorShapeStep，宏权重之和等于底层路径长度。'
    : !steps.length
    ? '零步证明由 Path.nil state0 构造。每次合法移动都会在这里增加一个 cons 构造器。'
    : quotient
      ? '当前证明包含规范代表切换，因此整体类型是 QPath：每一步同时保存 tryMove 等式和 SameShape 代表证明。'
      : '当前所有目标都与 tryMove 的带标签结果完全相同，因此这些 cons 构造器组成精确 Path。';
  ui['proof-exact-count'].textContent = exactCount;
  ui['proof-quotient-count'].textContent = quotientCount;
  ui['proof-length'].textContent = isCorridorSpace
    ? Math.max(0, history.length - 1) + ' macro / ' + steps.length + ' primitive'
    : steps.length + ' steps';
  ui['proof-step-list'].innerHTML = steps.length ? steps.map(step => {
    const piece = pieces[step.edge.piece].label, action = leanAction(step);
    return '<li class="proof-step ' + (step.exact ? '' : 'quotient') + '" data-index="' + step.index + '">' +
      '<h4>#' + step.sourceId + ' → #' + step.targetId + '<span>' +
      (isCorridorSpace ? '宏 ' + step.macroIndex + ' · ' : '') + (step.exact ? 'Step' : 'QStep') + '</span></h4>' +
      '<div class="proof-equation">tryMove state' + step.sourceId + ' ' + escapeHtml(action) + '<br>= some actual' + step.index +
      '<br><b>动作：</b>' + piece + '向' + step.edge.direction + '</div>' +
      (step.exact ? '<div class="proof-constructor">actual' + step.index + ' = state' + step.targetId + ' · Path.cons</div>' :
        '<div class="proof-equation proof-represented">SameShape actual' + step.index + ' state' + step.targetId + ' = true</div><div class="proof-constructor">QPath.cons executed represented tail</div>') + '</li>';
  }).join('') : isCorridorSpace
    ? '<div class="proof-empty">初始锚点具有零操作证明<code>Task.Walk.nil corridorTask.initial</code>每条宏边都可由 corridorWalkExpand 展开。</div>'
    : '<div class="proof-empty">初始状态本身已有零步证明<code>Path.nil state0</code>移动一个棋子，观察证明项增加一个构造器。</div>';
  let tree = isCorridorSpace
    ? '<div><b>corridorTask.Walk</b> anchor0 anchor' + target + '<br><em>corridorWalkExpand</em> ↓</div>'
    : '<div><b>' + (quotient ? 'QPath' : 'Path') + '</b> state0 state' + target + '</div>';
  if (!steps.length) tree += '<div class="proof-tree-node"><em>Path.nil</em> state0</div>';
  for (const step of steps) tree += '<div class="proof-tree-node"><em>' + (quotient ? 'QPath.cons' : 'Path.cons') + '</em> ' + escapeHtml(leanAction(step)) +
    '<div>executed : tryMove … = some actual' + step.index + '</div>' +
    (!step.exact ? '<div class="quotient-term">represented : SameShape actual' + step.index + ' state' + step.targetId + '</div>' : '') + '</div>';
  tree += '<div class="proof-tree-node"><em>' + (quotient ? 'QPath.nil' : 'Path.nil') + '</em> state' + target + '</div>';
  if (goal) tree += '<div class="proof-tree-node"><b>solved</b> : goal state' + target + ' = true<br><em>⇒ ' + (quotient ? 'QSolution' : (navigationUsed ? 'Solution' : 'CertifiedPlay')) + '</em></div>';
  ui['proof-tree'].innerHTML = tree;
  ui['proof-code'].textContent = generatedProofCode(steps, quotient);
  ui['proof-code-status'].textContent = isCorridorSpace
    ? 'CorridorMacroStep：可展开宏边 + 权重保持'
    : quotient ? 'QPath：执行等式 + 同形代表证书' : 'Path：每一步是精确 tryMove 等式';
}

function showCompletion(state) {
  ui['result-node'].textContent = '#' + state.id;
  ui['result-moves'].textContent = isCorridorSpace
    ? playerOperations + ' 操作 / ' + playerMoves + ' 步'
    : navigationUsed ? playerMoves + ' + 导航' : playerMoves + ' 步';
  ui['result-distance'].textContent = state.distance + ' 步';
  if (navigationUsed) {
    ui['result-certification'].textContent = '该终局节点由 Lean BFS 计算为从经典布局可达；本次过程使用了三维图导航，因此不作为连续玩家解计步。';
    ui['result-optimal'].textContent = '可达终局 · goal = true';
    ui['result-optimal'].className = 'result-verdict computed';
  } else if (playerMoves === shortestGoalDistance) {
    ui['result-certification'].textContent = '这条操作序列中的每一步都来自 Lean 导出的 tryMove 合法转换。';
    ui['result-optimal'].textContent = isCorridorSpace
      ? '底层最短值 ' + shortestGoalDistance + ' 步；决策骨架的最少宏操作值为 ' + shortestOperationDistance
      : '达到 Lean BFS 计算的全局最短值：' + shortestGoalDistance + ' 步';
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
  selectStart: id => { selectionMode = 'start'; routeStartPinned = true; return selectRouteNode(id); },
  selectEnd: id => { selectionMode = 'end'; return selectRouteNode(id); },
  fit: fitGraph,
  focusTargetId: preferredFocusTargetId,
  overviewScreen: id => {
    const point = nodePosition(id, new THREE.Vector3()).project(camera);
    const rect = ui.graph.getBoundingClientRect();
    return { x: rect.left + (point.x + 1) * rect.width / 2, y: rect.top + (1 - point.y) * rect.height / 2 };
  },
  localTopologyScreen: id => localTopologyView?.screenPosition(id) || null,
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
    current, graphMode, routeStart, routeEnd, routeLength: routePath.length,
    explored: exploredNodes.size, shown: exploreNodeIds.length, isAnimating,
    cameraDistance: graphMode === 'force' ? forceCameraDistance() : camera.position.distanceTo(controls.target),
    pointSize: pointCloud?.material.size, sizeAttenuation: pointCloud?.material.sizeAttenuation,
    markerScale: graphMode === 'force' ? forceCurrentMarker?.scale.x : currentMarker?.scale.x,
    forceReady: Boolean(forceGraph), forcePinned, forceNodeCount: forceNodes.length, forceLinkCount: forceLinks.length,
    overviewVisualCount: overviewVisualPositions ? overviewVisualPositions.length / 3 : 0,
    contractionPairCount: contractionPairs.length,
    macroEdgeCount,
    ordinaryEdgeCount: edgePairs.length - macroEdgeCount,
    macroEndpointCount: macroEndpointIds.size
  })
};
new ResizeObserver(resizeRenderer).observe(ui['graph-wrap']);
window.addEventListener('beforeunload', () => forceGraph?._destructor());
loadGraph().catch(error => { ui.loading.innerHTML = '<strong>三维图载入失败，请刷新页面</strong>'; console.error(error); });
