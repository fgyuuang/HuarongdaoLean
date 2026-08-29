import * as THREE from './vendor/three.module.min.js';
import { OrbitControls } from './vendor/OrbitControls.js';
import {
  buildVisualStateSpace,
  stateGraphToLayoutInput
} from './state-space-visualization.js';

const $ = id => document.getElementById(id);
const directionLabels = { up: '上', down: '下', left: '左', right: '右' };
const colors = ['#a83934', '#28736d', '#c58d34', '#6f7f9b', '#9b6f82', '#70965e', '#b47745', '#557b78', '#8a7755', '#765f94'];
const presets = {
  tiny: { width: 3, height: 2, pieces: [
    { id: 1, width: 1, height: 1, x: 0, y: 0, goalX: 2, goalY: 0 },
    { id: 2, width: 1, height: 1, x: 1, y: 0, goalX: null, goalY: null }
  ] },
  gate: { width: 4, height: 4, pieces: [
    { id: 1, width: 2, height: 2, x: 0, y: 0, goalX: 2, goalY: 2 },
    { id: 2, width: 1, height: 2, x: 2, y: 0, goalX: null, goalY: null },
    { id: 3, width: 1, height: 1, x: 3, y: 0, goalX: null, goalY: null }
  ] },
  classic: { width: 4, height: 5, pieces: [
    { id:1,width:2,height:2,x:1,y:0,goalX:1,goalY:3 },
    { id:2,width:2,height:1,x:1,y:2,goalX:null,goalY:null },
    { id:3,width:1,height:2,x:0,y:0,goalX:null,goalY:null },
    { id:4,width:1,height:2,x:3,y:0,goalX:null,goalY:null },
    { id:5,width:1,height:2,x:0,y:2,goalX:null,goalY:null },
    { id:6,width:1,height:2,x:3,y:2,goalX:null,goalY:null },
    { id:7,width:1,height:1,x:1,y:3,goalX:null,goalY:null },
    { id:8,width:1,height:1,x:2,y:3,goalX:null,goalY:null },
    { id:9,width:1,height:1,x:0,y:4,goalX:null,goalY:null },
    { id:10,width:1,height:1,x:3,y:4,goalX:null,goalY:null }
  ] },
  custom: { width: 4, height: 4, pieces: [{ id: 1, width: 1, height: 1, x: 0, y: 0, goalX: 3, goalY: 3 }] }
};
let pieces = [], solution = null, resultData = null, playStep = 0, busy = false, searchStrategy = 'astar', playSelectedBlock = null;
let genericGraph = null, genericOutgoing = [], graphCurrent = 0, graphHistory = [0], graphHistoryEdges = [], graphMode = 'overview';
let graphLayout = [], graphExploreLayout = new Map(), graphVisibleIds = [], graphRouteStart = 0, graphRouteEnd = null, graphRouteEdges = [], graphSelectionMode = 'end', graphRoutePinned = false, graphAnimationToken = 0;
let labForceGraph = null, labForceNodes = [], labForceLinks = [], labForcePinned = false, labForceNeedsFit = false, labForceWidth = 0, labForceHeight = 0, labForceHighlightedLinks = new Set();
let labForcePointerDown = null, labForceDragActive = false;
let labGraphViewportWidth = 1, labGraphViewportHeight = 1;
let structuralLayoutWorker = null, structuralLayoutRequest = 0, structuralLayoutReady = false, structuralLayoutMeta = null;
const labGraphScene = new THREE.Scene(), labGraphCamera = new THREE.PerspectiveCamera(45, 1, 0.1, 3000);
const labGraphRenderer = new THREE.WebGLRenderer({ canvas: $('lab-graph-canvas'), antialias: true, powerPreference: 'high-performance' });
labGraphRenderer.setPixelRatio(Math.min(devicePixelRatio || 1, 1.5)); labGraphRenderer.outputColorSpace = THREE.SRGBColorSpace;
const labGraphControls = new OrbitControls(labGraphCamera, labGraphRenderer.domElement); labGraphControls.enableDamping = true; labGraphControls.dampingFactor = .07; labGraphControls.minDistance = 2; labGraphControls.maxDistance = 900;
const labGraphRaycaster = new THREE.Raycaster(), labGraphPointer = new THREE.Vector2(), labGraphGroup = new THREE.Group();
labGraphRaycaster.params.Points.threshold = .45; labGraphScene.add(labGraphGroup);
let labGraphPoints = null, labGraphPointerDown = null, labGraphHoverPosition = null;
let labGraphHoverFrame = null, labGraphLastHoverPick = 0;

function syncFullSpaceEntry(mode) {
  const link = document.querySelector('.full-space-entry');
  if (!link) return;
  const inLab = mode === 'lab';
  link.href = inLab ? 'full-space.html?from=lab' : 'full-space.html?from=main';
  link.textContent = inLab ? '全空间预览' : '全空间预览';
  link.title = inLab
    ? '打开全空间预览；返回时保留关卡实验室'
    : '查看 898 个连续分量的全空间总览';
}

function switchMode(mode) {
  const lab = mode === 'lab';
  $('laboratory').hidden = !lab; $('classic-workspace').hidden = lab;
  $('mode-lab').classList.toggle('active', lab); $('mode-classic').classList.toggle('active', !lab);
  syncFullSpaceEntry(mode);
  const nextUrl = new URL(location.href);
  if (lab) nextUrl.searchParams.set('mode', 'lab');
  else nextUrl.searchParams.delete('mode');
  history.replaceState(history.state, '', nextUrl);
  if (lab) renderAll();
}
$('mode-classic').onclick = () => switchMode('classic');
$('mode-lab').onclick = () => switchMode('lab');

function loadPreset(name) {
  const preset = structuredClone(presets[name]);
  $('lab-width').value = preset.width; $('lab-height').value = preset.height; $('lab-timeout-seconds').value = name === 'classic' ? 180 : 120; pieces = preset.pieces;
  $('lab-source-note').hidden = true;
  $('lab-initial-type').textContent = 'ValidState spec initial';
  document.querySelectorAll('[data-lab-preset]').forEach(button => button.classList.toggle('active', button.dataset.labPreset === name));
  clearResult(); renderAll();
}
document.querySelectorAll('[data-lab-preset]').forEach(button => button.onclick = () => loadPreset(button.dataset.labPreset));

async function loadFullSpaceComponent(componentId) {
  const response = await fetch('./full-shape-components.json');
  if (!response.ok) throw new Error(`全空间分量数据加载失败：HTTP ${response.status}`);
  const data = await response.json();
  const component = data.components?.find(item => item.id === componentId);
  if (!component || !Array.isArray(component.positions) || component.positions.length !== 10) {
    throw new Error(`找不到全空间分量 #${componentId}`);
  }
  $('lab-width').value = data.meta?.width ?? 4;
  $('lab-height').value = data.meta?.height ?? 5;
  $('lab-timeout-seconds').value = 180;
  pieces = [
    { id: 1, width: 2, height: 2, x: component.positions[0][0], y: component.positions[0][1], goalX: 1, goalY: 3 },
    { id: 2, width: 2, height: 1, x: component.positions[1][0], y: component.positions[1][1], goalX: null, goalY: null },
    ...component.positions.slice(2, 6).map((position, index) => ({
      id: index + 3, width: 1, height: 2, x: position[0], y: position[1], goalX: null, goalY: null
    })),
    ...component.positions.slice(6, 10).map((position, index) => ({
      id: index + 7, width: 1, height: 1, x: position[0], y: position[1], goalX: null, goalY: null
    }))
  ];
  document.querySelectorAll('[data-lab-preset]').forEach(button => button.classList.remove('active'));
  $('lab-source-note').hidden = false;
  $('lab-source-note').innerHTML = `<strong>全空间分量 #${component.id}</strong> · 已载入其确定性代表棋盘（${component.stateCount.toLocaleString('zh-CN')} 个连续状态）。该代表可继续编辑，不自动声称属于经典初态的 25,955 状态分量。`;
  $('lab-initial-type').textContent = `ShapeState representative · component #${component.id}`;
  clearResult();
  renderAll();
  setStatus('idle', `已接入全空间分量 #${component.id}`);
}
document.querySelectorAll('[data-lab-strategy]').forEach(button => button.onclick = () => {
  searchStrategy = button.dataset.labStrategy; document.querySelectorAll('[data-lab-strategy]').forEach(item => item.classList.toggle('active', item === button));
  $('lab-solve').textContent = searchStrategy === 'astar' ? 'Lean A* 求解' : 'Lean BFS 建图';
  $('lab-strategy-note').textContent = searchStrategy === 'astar' ? '启发式搜索找到目标后停止；返回可验证的搜索子图。' : '继续展开直到队列耗尽或资源截断；用于完整状态图探索。'; clearResult();
});

function numericInput(value, field, min = 0) {
  const input = document.createElement('input'); input.type = 'number'; input.min = min; input.value = value ?? '';
  input.placeholder = '—'; input.dataset.field = field; return input;
}
function renderPieceList() {
  const list = $('lab-piece-list'); list.replaceChildren();
  pieces.forEach((piece, index) => {
    const constrained = piece.goalX != null && piece.goalY != null;
    const row = document.createElement('div'); row.className = 'lab-piece-row';
    const id = document.createElement('strong'); id.textContent = piece.id;
    const size = document.createElement('span'); size.className = 'lab-input-pair'; size.append(numericInput(piece.width, 'width', 1), document.createTextNode('×'), numericInput(piece.height, 'height', 1));
    const start = document.createElement('span'); start.className = 'lab-input-pair'; start.append(numericInput(piece.x, 'x'), document.createTextNode(','), numericInput(piece.y, 'y'));
    const goal = document.createElement('span'); goal.className = 'lab-goal-editor';
    const toggleLabel = document.createElement('label'); toggleLabel.className = 'lab-goal-toggle';
    const toggle = document.createElement('input'); toggle.type = 'checkbox'; toggle.checked = constrained;
    toggleLabel.append(toggle, document.createTextNode(constrained ? '已约束' : '任意'));
    const goalPair = document.createElement('span'); goalPair.className = 'lab-input-pair';
    const goalX = numericInput(piece.goalX, 'goalX'), goalY = numericInput(piece.goalY, 'goalY');
    goalX.disabled = goalY.disabled = !constrained; goalPair.append(goalX, document.createTextNode(','), goalY); goal.append(toggleLabel, goalPair);
    toggle.onchange = () => {
      if (toggle.checked) { piece.goalX = Math.max(0, piece.x); piece.goalY = Math.max(0, piece.y); }
      else { piece.goalX = null; piece.goalY = null; }
      clearResult(); renderAll();
    };
    const remove = document.createElement('button'); remove.textContent = '×'; remove.title = '删除木块'; remove.disabled = pieces.length === 1;
    remove.onclick = () => { pieces.splice(index, 1); pieces.forEach((item, i) => item.id = i + 1); clearResult(); renderAll(); };
    row.append(id, size, start, goal, remove);
    row.querySelectorAll('input[type="number"]').forEach(input => input.oninput = () => {
      if (input.value === '') return;
      piece[input.dataset.field] = Number(input.value); clearResult(); renderBoards();
    });
    list.append(row);
  });
}
$('lab-add-piece').onclick = () => {
  const id = pieces.length + 1; pieces.push({ id, width: 1, height: 1, x: 0, y: 0, goalX: null, goalY: null }); clearResult(); renderAll();
};

function boardDimensions() { return { width: Math.max(1, Number($('lab-width').value)), height: Math.max(1, Number($('lab-height').value)) }; }
function enableBlockDrag(block, index, kind) {
  block.onpointerdown = event => {
    event.preventDefault();
    const board = block.parentElement, boardRect = board.getBoundingClientRect(), blockRect = block.getBoundingClientRect();
    const { width, height } = boardDimensions();
    const offsetX = Math.floor((event.clientX - blockRect.left) / (boardRect.width / width));
    const offsetY = Math.floor((event.clientY - blockRect.top) / (boardRect.height / height));
    block.classList.add('dragging');
    const move = pointer => {
      const x = Math.max(0, Math.min(width - pieces[index].width, Math.floor((pointer.clientX - boardRect.left) / boardRect.width * width) - offsetX));
      const y = Math.max(0, Math.min(height - pieces[index].height, Math.floor((pointer.clientY - boardRect.top) / boardRect.height * height) - offsetY));
      block.style.left = x / width * 100 + '%'; block.style.top = y / height * 100 + '%'; block.dataset.dragX = x; block.dataset.dragY = y;
    };
    const up = pointer => {
      move(pointer); const x = Number(block.dataset.dragX), y = Number(block.dataset.dragY);
      if (kind === 'initial') { pieces[index].x = x; pieces[index].y = y; }
      else { pieces[index].goalX = x; pieces[index].goalY = y; }
      window.removeEventListener('pointermove', move); window.removeEventListener('pointerup', up);
      clearResult(); renderAll();
    };
    window.addEventListener('pointermove', move); window.addEventListener('pointerup', up, { once: true });
  };
}
function enableBlockResize(block, index, position) {
  const handle = document.createElement('button'); handle.className = 'lab-resize-handle'; handle.type = 'button'; handle.title = '拖动改变木块尺寸'; handle.setAttribute('aria-label', '改变块 ' + pieces[index].id + ' 的尺寸');
  handle.onpointerdown = event => {
    event.preventDefault(); event.stopPropagation();
    const board = block.parentElement, rect = board.getBoundingClientRect(), { width, height } = boardDimensions(), piece = pieces[index], origin = position;
    block.classList.add('resizing');
    const move = pointer => {
      const nextWidth = Math.max(1, Math.min(width - origin.x, Math.ceil((pointer.clientX - rect.left) / (rect.width / width)) - origin.x));
      const nextHeight = Math.max(1, Math.min(height - origin.y, Math.ceil((pointer.clientY - rect.top) / (rect.height / height)) - origin.y));
      block.style.width = nextWidth / width * 100 + '%'; block.style.height = nextHeight / height * 100 + '%'; block.dataset.resizeWidth = nextWidth; block.dataset.resizeHeight = nextHeight;
    };
    const up = pointer => {
      move(pointer); piece.width = Number(block.dataset.resizeWidth); piece.height = Number(block.dataset.resizeHeight);
      window.removeEventListener('pointermove', move); window.removeEventListener('pointerup', up); clearResult(); renderAll();
    };
    window.addEventListener('pointermove', move); window.addEventListener('pointerup', up, { once: true });
  };
  block.append(handle);
}

function firstFreeInitialCell() {
  const { width, height } = boardDimensions(), used = new Set();
  for (const piece of pieces) for (let y=piece.y;y<piece.y+piece.height;y++) for(let x=piece.x;x<piece.x+piece.width;x++) used.add(x+','+y);
  for(let y=0;y<height;y++)for(let x=0;x<width;x++)if(!used.has(x+','+y))return {x,y}; return null;
}
function addPieceFromCell(x, y, kind) {
  if (pieces.length >= 64) { setStatus('invalid','最多支持 64 个编号块'); return; }
  const initial = kind === 'initial' ? {x,y} : firstFreeInitialCell();
  if (!initial) { setStatus('invalid','初态棋盘没有空格可放置新块'); return; }
  pieces.push({id:pieces.length+1,width:1,height:1,x:initial.x,y:initial.y,goalX:kind==='goal'?x:null,goalY:kind==='goal'?y:null}); clearResult(); renderAll();
}

function canShrinkBoard(dimension) {
  const {width,height}=boardDimensions();
  return pieces.every(piece => {
    const xMax=piece.x+piece.width, yMax=piece.y+piece.height;
    const gx=piece.goalX == null ? 0 : piece.goalX+piece.width, gy=piece.goalY == null ? 0 : piece.goalY+piece.height;
    return dimension==='width' ? xMax <= width-1 && (piece.goalX == null || gx <= width-1) : yMax <= height-1 && (piece.goalY == null || gy <= height-1);
  });
}
function changeBoardDimension(dimension, delta) {
  const input=dimension==='width' ? $('lab-width') : $('lab-height'), current=Number(input.value), next=current+delta, max=16;
  if(next<1||next>max)return;
  if(delta<0&&!canShrinkBoard(dimension)){setStatus('invalid',dimension==='width'?'不能删除这一列：有木块或目标约束在边界上':'不能删除这一行：有木块或目标约束在边界上');return;}
  input.value=next;clearResult();renderBoards();
}
document.querySelectorAll('[data-board-dimension]').forEach(button=>button.onclick=()=>changeBoardDimension(button.dataset.boardDimension,Number(button.dataset.boardDelta)));

function enableBoardResize(element) {
  const handle=document.createElement('button');handle.type='button';handle.className='lab-board-resize-handle';handle.title='拖动改变棋盘列数和行数';handle.textContent='↘';
  handle.onpointerdown=event=>{
    event.preventDefault();event.stopPropagation();const rect=element.getBoundingClientRect(),start=boardDimensions(),cellWidth=rect.width/start.width,cellHeight=rect.height/start.height;
    const move=pointer=>{const width=Math.max(1,Math.min(16,Math.round((pointer.clientX-rect.left)/cellWidth))),height=Math.max(1,Math.min(16,Math.round((pointer.clientY-rect.top)/cellHeight)));$('lab-width').value=width;$('lab-height').value=height;element.dataset.resizeBoard=width+'x'+height;};
    const up=pointer=>{move(pointer);window.removeEventListener('pointermove',move);window.removeEventListener('pointerup',up);clearResult();renderAll();};
    window.addEventListener('pointermove',move);window.addEventListener('pointerup',up,{once:true});
  };element.append(handle);
}

function renderBoard(element, positions, goal = false, editableKind = null) {
  const { width, height } = boardDimensions(); element.replaceChildren();
  element.style.setProperty('--cols', width); element.style.setProperty('--rows', height); element.style.aspectRatio = width + ' / ' + height;
  const occupied = new Map();
  pieces.forEach((piece, index) => {
    const position = positions[index]; if (!position) return;
    const block = document.createElement('div'); block.dataset.piece = index; block.className = 'lab-block' + (goal ? ' target' : ''); block.textContent = piece.id;
    Object.assign(block.style, { left: position.x / width * 100 + '%', top: position.y / height * 100 + '%', width: piece.width / width * 100 + '%', height: piece.height / height * 100 + '%', background: colors[index % colors.length] });
    let invalid = position.x < 0 || position.y < 0 || position.x + piece.width > width || position.y + piece.height > height;
    for (let y = position.y; y < position.y + piece.height; y++) for (let x = position.x; x < position.x + piece.width; x++) {
      const key = x + ',' + y; if (occupied.has(key)) invalid = true; occupied.set(key, index);
    }
    block.classList.toggle('invalid', invalid); if (editableKind) { enableBlockDrag(block, index, editableKind); enableBlockResize(block, index, position); } element.append(block);
  });
  if (editableKind) for(let y=0;y<height;y++) for(let x=0;x<width;x++) if(!occupied.has(x+','+y)) {
    const add=document.createElement('button');add.type='button';add.className='lab-add-cell';add.textContent='+';add.title='在 ('+x+','+y+') 添加 1×1 编号块';
    Object.assign(add.style,{left:x/width*100+'%',top:y/height*100+'%',width:100/width+'%',height:100/height+'%'});add.onclick=()=>addPieceFromCell(x,y,editableKind);element.append(add);
  }

}
function initialPositions() { return pieces.map(piece => ({ x: piece.x, y: piece.y })); }
function goalPositions() { return pieces.map(piece => piece.goalX == null ? null : ({ x: piece.goalX, y: piece.goalY })); }
function renderBoards() { renderBoard($('lab-initial-board'), initialPositions(), false, 'initial'); renderBoard($('lab-goal-board'), goalPositions(), true, 'goal'); }
function renderAll() { renderPieceList(); renderBoards(); }
$('lab-width').oninput = $('lab-height').oninput = () => { clearResult(); renderBoards(); };

function boundedInput(id, fallback, min, max) {
  const input=$(id), parsed=input.value.trim()===''?fallback:Number(input.value), value=Math.max(min,Math.min(max,Number.isFinite(parsed)?Math.trunc(parsed):fallback));input.value=value;return value;
}
function payload(validateOnly = false) {
  const { width, height } = boardDimensions(), maxStates=boundedInput('lab-max-states',100000,1,2000000), maxDepth=boundedInput('lab-max-depth',500,0,10000), timeoutSeconds=boundedInput('lab-timeout-seconds',120,1,600);
  return { board: { width, height }, pieces: pieces.map(piece => ({ ...piece })), options: {
    maxStates: validateOnly ? 1 : maxStates, maxDepth: validateOnly ? 0 : maxDepth, timeoutMs: timeoutSeconds * 1000, strategy: validateOnly ? 'bfs' : searchStrategy
  } };
}
function setStatus(kind, text) { const status = $('lab-status'); status.className = 'lab-status ' + kind; status.querySelector('span').textContent = text; }
function setChain(stage, state) { $('lab-proof-' + stage).className = state; }
function clearResult() {
  stopStructuralLayout(); disposeLabForceGraph(); solution = null; resultData = null; genericGraph = null; genericOutgoing = []; graphCurrent = 0; graphHistory = [0]; graphHistoryEdges = []; playStep = 0; playSelectedBlock = null; $('lab-result').className = 'lab-result empty'; $('lab-result').querySelector('.lab-empty').hidden = false; $('lab-result').querySelector('.lab-result-content').hidden = true;
  setStatus('idle', '规格已修改'); ['spec','search','check','exists'].forEach(stage => setChain(stage, ''));
}
async function callSolver(validateOnly) {
  if (busy) return; busy = true; setStatus('running', validateOnly ? 'Lean 正在验证规格' : searchStrategy === 'astar' ? 'Lean A* 正在启发式搜索' : 'Lean BFS 正在枚举状态图');
  try {
    const response = await fetch('/api/puzzle/solve', { method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify(payload(validateOnly)) });
    const data = await response.json(); if (!response.ok) throw new Error(data.error?.message || '请求失败');
    showResult(data, validateOnly);
  } catch (error) {
    const timeout = /timed out|timeout/i.test(error.message);
    setStatus(timeout ? 'limit' : 'invalid', timeout ? '搜索等待时间已用完；关卡并未判定失败，可增加等待秒数或状态上限继续' : error.message);
    setChain('spec', timeout ? 'pass' : 'fail'); setChain('search', timeout ? 'warn' : ''); setChain('check',''); setChain('exists','');
  }
  finally { busy = false; }
}
$('lab-validate').onclick = () => callSolver(true); $('lab-solve').onclick = () => callSolver(false);

function difficulty(stats) {
  if (stats.shortestLength == null) return '—';
  const score = stats.shortestLength + Math.log2(Math.max(1, stats.visitedStates));
  return score < 8 ? '入门' : score < 16 ? '基础' : score < 28 ? '进阶' : score < 45 ? '困难' : '专家';
}
function showResult(data, validateOnly) {
  const valid = data.validation?.wellFormed === true; setChain('spec', valid ? 'pass' : 'fail');
  if (!valid) { setStatus('invalid', '关卡定义无效'); return; }
  if (validateOnly) { setStatus('valid', '关卡成立 · 可开始搜索'); return; }
  const unreachableProof = data.proof?.kind === 'unreachable-certificate' && data.proof?.verified === true;
  setChain('search', data.status === 'solved' ? 'pass' : data.status === 'limit' ? 'warn' : data.status === 'unreachable' ? (unreachableProof ? 'pass' : 'warn') : '');
  setChain('check', data.proof?.verified ? 'pass' : ''); setChain('exists', data.proof?.verified ? 'pass' : '');
  setStatus(data.status === 'solved' ? 'valid' : data.status === 'limit' ? 'limit' : 'invalid',
    data.status === 'solved' ? (data.stats.algorithm === 'astar' ? 'A* 已找到并验证解' : 'BFS 已找到并验证解') : data.status === 'unreachable' ? '完整状态图中不可达' : data.status === 'limit' ? '达到搜索上限，结论未知' : '关卡定义无效');
  const result = $('lab-result'); result.className = 'lab-result ' + data.status; result.querySelector('.lab-empty').hidden = true; result.querySelector('.lab-result-content').hidden = false;
  $('lab-visited').textContent = data.stats.visitedStates.toLocaleString(); $('lab-expanded').textContent = data.stats.expandedStates.toLocaleString(); $('lab-generated').textContent = data.stats.generatedTransitions.toLocaleString(); $('lab-length').textContent = data.stats.shortestLength ?? '—'; $('lab-difficulty').textContent = difficulty(data.stats); $('lab-algorithm').textContent = data.stats.algorithm === 'astar' ? 'A*' : 'BFS';
  disposeLabForceGraph(); solution = data.solution; resultData = data; genericGraph = data.graph; genericOutgoing = []; graphCurrent = 0; graphHistory = [0]; graphHistoryEdges = []; playStep = 0; renderSolution(data); initializeGenericGraph();
}
function renderSolution(data) {
  const verified = data.proof?.verified === true; const unreachableProof = data.proof?.kind === 'unreachable-certificate' && verified; const proofVerified = verified;
  $('lab-proof-badge').textContent = unreachableProof ? 'Lean 已证明不可达' : verified ? 'Lean 已重放验证' : '未验证'; $('lab-proof-badge').className = proofVerified ? 'verified' : '';
  if (!solution) { renderBoard($('lab-play-board'), initialPositions()); $('lab-step-label').textContent = '无路径'; $('lab-actions').replaceChildren(); $('lab-proof-code').textContent = unreachableProof ? 'checkClosedGraph + checkNoGoal ⇒ 不存在可达目标状态。' : data.status === 'unreachable' ? 'BFS 已耗尽，但当前返回结果尚未形成内核不可达证书。' : '搜索受资源上限截断，不能推出不可达。'; return; }
  const positions = solution.states[playStep].positions; if(genericGraph) renderCurrentPlayBoard(); else renderBoard($('lab-play-board'), positions);
  $('lab-step-label').textContent = playStep + ' / ' + solution.actions.length; $('lab-prev').disabled = playStep === 0; $('lab-next').disabled = playStep === solution.actions.length;
  const actionList = $('lab-actions'); actionList.innerHTML = solution.actions.map((action, index) => '<button class="' + (playStep === index + 1 ? 'active' : '') + '" data-step="' + (index + 1) + '"><b>' + (index + 1) + '</b><span>块 ' + action.block + ' 向' + directionLabels[action.direction] + '</span><code>tryMove = some state' + (index + 1) + '</code></button>').join('');
  actionList.querySelectorAll('button').forEach(button => button.onclick = () => replaySolutionStep(Number(button.dataset.step)));
  const actionsLean = solution.actions.map(action => '  ⟨' + (action.block - 1) + ', .' + action.direction + '⟩').join(',\n');
  $('lab-proof-code').textContent = `def actions : List Action := [
${actionsLean}
]

checked : checkSolution spec actions = true
solves  : Solves spec actions := checkSolution_sound checked
exists  : Nonempty (Solution spec)
        := verified_search_implies_exists verified

-- 每个动作由 runMoves 依次产生一个 Path.cons。
-- 路径长度由所选搜索算法计算；搜索器最短性尚未封装为内核定理。`;
}
function renderCurrentPlayBoard() {
  if (!genericGraph?.nodes[graphCurrent]) return;
  renderBoard($('lab-play-board'), genericGraph.nodes[graphCurrent].positions);
  $('lab-play-mode').textContent = 'Lean 图节点 #'+graphCurrent;
  $('lab-step-label').textContent = '节点 #'+graphCurrent;
  $('lab-play-board').querySelectorAll('.lab-block').forEach(block => {
    const index=Number(block.dataset.piece);block.classList.toggle('selected',index===playSelectedBlock);
    let start=null;
    block.onpointerdown=event=>{start={x:event.clientX,y:event.clientY};playSelectedBlock=index;$('lab-play-board').querySelectorAll('.lab-block').forEach(item=>item.classList.toggle('selected',Number(item.dataset.piece)===index));};
    block.onpointerup=event=>{if(!start)return;const dx=event.clientX-start.x,dy=event.clientY-start.y;if(Math.hypot(dx,dy)>12)manualMove(index,Math.abs(dx)>Math.abs(dy)?(dx>0?'right':'left'):(dy>0?'down':'up'));};
    block.onclick=()=>{playSelectedBlock=index;renderCurrentPlayBoard();};
  });
}
function manualMove(index,direction) {
  if(!genericGraph)return;const edge=(graphAdjacency()[graphCurrent]||[]).find(item=>item.block===index+1&&item.direction===direction);
  if(!edge){setStatus('limit','块 '+(index+1)+' 不能向'+directionLabels[direction]+'移动');return false;}
  applyGraphEdge(edge);setStatus(genericGraph.nodes[edge.target].goal?'valid':'idle',genericGraph.nodes[edge.target].goal?'已到达目标 · 路径已成为证明':'手动探索 · Lean 合法边');return true;
}
function replaySolutionStep(step){
  if(!solution||!genericGraph)return;graphAnimationToken++;graphCurrent=0;graphHistory=[0];graphHistoryEdges=[];playSelectedBlock=null;
  for(let index=0;index<step;index++){const action=solution.actions[index],edge=(graphAdjacency()[graphCurrent]||[]).find(item=>item.block===action.block&&item.direction===action.direction);if(!edge)break;graphCurrent=edge.target;graphHistory.push(edge.target);graphHistoryEdges.push(edge);}playStep=step;renderCurrentPlayBoard();updateGraphReadout();rebuildGenericGraph();
}
function undoGraphMove(){if(!graphHistoryEdges.length)return;graphHistoryEdges.pop();graphHistory.pop();graphCurrent=graphHistory.at(-1)??0;renderCurrentPlayBoard();updateGraphReadout();rebuildGenericGraph();}
function resetManualExploration(){graphAnimationToken++;graphCurrent=0;graphHistory=[0];graphHistoryEdges=[];playSelectedBlock=null;renderCurrentPlayBoard();updateGraphReadout();rebuildGenericGraph(true);}
function hintManualMove(){if(!genericGraph)return;let best=null;for(const node of genericGraph.nodes)if(node.goal){const route=shortestGraphRoute(graphCurrent,node.id);if(route&&route.length&&(!best||route.length<best.length))best=route;}if(best?.length){playSelectedBlock=best[0].block-1;manualMove(playSelectedBlock,best[0].direction);}else setStatus('limit','当前搜索图中没有可用的目标提示');}

function graphAdjacency() {
  if (genericOutgoing.length === (genericGraph?.nodes.length || 0)) return genericOutgoing;
  genericOutgoing = Array.from({ length: genericGraph?.nodes.length || 0 }, () => []);
  for (const edge of genericGraph?.edges || []) genericOutgoing[edge.source].push(edge);
  return genericOutgoing;
}
function computeGraphLayout() {
  if (!genericGraph) return [];
  const layers = new Map(); for (const node of genericGraph.nodes) { if (!layers.has(node.distance)) layers.set(node.distance, []); layers.get(node.distance).push(node); }
  const maxDepth = Math.max(1, ...layers.keys()), golden = Math.PI * (3 - Math.sqrt(5)), layerIndex = new Map();
  for (const layer of layers.values()) layer.forEach((node,index)=>layerIndex.set(node.id,index));
  return genericGraph.nodes.map(node => { const index=layerIndex.get(node.id), radius=Math.sqrt(index)*.72; return new THREE.Vector3((node.distance-maxDepth/2)*1.8,Math.cos(index*golden)*radius,Math.sin(index*golden)*radius); });
}
function structuralPhaseLabel(phase){
  return {'4D spread':'四维展开','4D -> 3D':'第四维压缩','3D projection':'三维投影'}[phase]||phase;
}
function structuralLayoutLabel(){
  if(!structuralLayoutReady)return '临时 BFS 生长种子';
  const meta=structuralLayoutMeta||{},mirror=[];
  if(meta.mirrorXPairs)mirror.push('横镜像 '+meta.mirrorXPairs);
  if(meta.mirrorYPairs)mirror.push('纵镜像 '+meta.mirrorYPairs);
  return '确定性 4D→3D 结构坐标'+(mirror.length?' · '+mirror.join(' / '):'');
}
function stopStructuralLayout(){
  structuralLayoutRequest++;
  structuralLayoutWorker?.terminate();
  structuralLayoutWorker=null;structuralLayoutReady=false;structuralLayoutMeta=null;
  const button=$('lab-layout-recompute');
  if(button){button.disabled=false;button.classList.remove('running');}
}
function startStructuralLayout(){
  if(!genericGraph)return;
  structuralLayoutWorker?.terminate();
  const request=++structuralLayoutRequest;
  structuralLayoutReady=false;structuralLayoutMeta=null;
  const button=$('lab-layout-recompute');
  button.disabled=true;button.classList.add('running');
  $('lab-graph-summary').textContent='正在构造四维结构布局 · 地标距离与镜像配对';
  const worker=new Worker(new URL('./structural-layout-worker.js',import.meta.url),{type:'module'});
  structuralLayoutWorker=worker;
  const layoutInput=stateGraphToLayoutInput({
    nodes:genericGraph.nodes,
    edges:genericGraph.edges,
    startId:genericGraph.nodes[0]?.id
  },{
    board:boardDimensions(),
    shapes:pieces.map(piece=>({width:piece.width,height:piece.height}))
  });
  worker.onmessage=event=>{
    if(request!==structuralLayoutRequest||worker!==structuralLayoutWorker)return;
    if(event.data.type==='progress'){
      const detail=event.data.detail,percent=Math.round(detail.ratio*100);
      $('lab-graph-summary').textContent='四维结构布局 '+percent+'% · '+structuralPhaseLabel(detail.phase);
      return;
    }
    if(event.data.type==='error'){
      structuralLayoutWorker=null;button.disabled=false;button.classList.remove('running');
      $('lab-graph-summary').textContent='结构布局失败，保留 BFS 生长种子 · '+event.data.message;
      return;
    }
    if(event.data.type!=='result')return;
    const coordinates=new Float32Array(event.data.coordinates);
    let visual;
    try{
      visual=buildVisualStateSpace(layoutInput,{coordinates,meta:event.data.meta});
    }catch(error){
      worker.terminate();structuralLayoutWorker=null;button.disabled=false;button.classList.remove('running');
      $('lab-graph-summary').textContent='结构布局结果无效，保留 BFS 生长种子 · '+error.message;
      return;
    }
    if(visual.nodes.length!==genericGraph.nodes.length){
      worker.terminate();structuralLayoutWorker=null;button.disabled=false;button.classList.remove('running');
      $('lab-graph-summary').textContent='结构布局坐标数量不匹配，保留 BFS 生长种子';
      return;
    }
    graphLayout=visual.nodes.map(node=>new THREE.Vector3(node.x,node.y,node.z));
    structuralLayoutMeta=visual.meta;structuralLayoutReady=true;graphExploreLayout=new Map();
    worker.terminate();structuralLayoutWorker=null;button.disabled=false;button.classList.remove('running');
    disposeLabForceGraph();prepareLabForceGraphData();
    if(graphMode==='force'){ensureLabForceGraph();refreshLabForceGraph(true);}
    else rebuildGenericGraph(true);
  };
  worker.onerror=event=>{
    if(request!==structuralLayoutRequest)return;
    structuralLayoutWorker=null;button.disabled=false;button.classList.remove('running');
    $('lab-graph-summary').textContent='结构布局 Worker 失败，保留 BFS 生长种子 · '+event.message;
  };
  worker.postMessage(layoutInput);
}
function labForceEndpointId(endpoint){return Number(typeof endpoint==='object'&&endpoint!==null?endpoint.id:endpoint);}
function labForceLinkKey(source,target){const a=labForceEndpointId(source),b=labForceEndpointId(target);return Math.min(a,b)+':'+Math.max(a,b);}
function graphKindLabel(){return genericGraph?.complete?'完整可达图':genericGraph?.truncated?'资源截断子图':'A* 解搜索子图';}
function graphMaxDistance(){let maximum=1;for(const node of genericGraph?.nodes||[])maximum=Math.max(maximum,node.distance||0);return maximum;}
function graphDepthColor(distance,maxDistance=graphMaxDistance()){
  const ratio=Math.max(0,Math.min(1,(distance||0)/Math.max(1,maxDistance)));
  const color=new THREE.Color();
  color.setHSL(.6-ratio*.58,.62,document.documentElement.classList.contains('dark')?.61:.4);
  return color;
}
function prepareLabForceGraphData(){
  if(!genericGraph)return;
  const scale=Math.max(1.4,Math.min(6,Math.log2(genericGraph.nodes.length+1)/2));
  labForceNodes=genericGraph.nodes.map((node,id)=>{
    const base=graphLayout[id],rx=base.x*scale,ry=base.y*scale,rz=base.z*scale;
    return {...node,rx,ry,rz,x:rx,y:ry,z:rz,fx:rx,fy:ry,fz:rz};
  });
  const seen=new Set();labForceLinks=[];
  for(const edge of genericGraph.edges){
    if(edge.source===edge.target)continue;
    const key=labForceLinkKey(edge.source,edge.target);if(seen.has(key))continue;seen.add(key);
    const a=labForceNodes[edge.source],b=labForceNodes[edge.target],restLength=Math.hypot(a.rx-b.rx,a.ry-b.ry,a.rz-b.rz);
    labForceLinks.push({source:edge.source,target:edge.target,sourceId:edge.source,targetId:edge.target,restLength:Math.max(.8,Math.min(18,restLength))});
  }
}
function labReferenceAnchorForce(strength=.012){
  let nodes=[];
  function force(alpha){const k=strength*alpha;for(const node of nodes){if(node.fx!=null)continue;node.vx+=(node.rx-node.x)*k;node.vy+=(node.ry-node.y)*k;node.vz+=(node.rz-node.z)*k;}}
  force.initialize=value=>{nodes=value;};return force;
}
function labForceNodeColor(node){
  if(node.id===graphCurrent)return '#9f2d2d';
  if(node.id===graphRouteStart||node.id===graphRouteEnd)return '#c58d34';
  if(node.goal)return '#28736d';
  if(node.id===0)return '#c58d34';
  return '#'+graphDepthColor(node.distance).getHexString();
}
function labForceLinkColor(link){
  if(labForceHighlightedLinks.has(labForceLinkKey(link.source,link.target)))return '#c58d34';
  const source=labForceNodes[labForceEndpointId(link.source)],target=labForceNodes[labForceEndpointId(link.target)];
  return '#'+graphDepthColor(((source?.distance||0)+(target?.distance||0))*.5).getHexString();
}
function labForceNodeValue(node){return node.id===graphCurrent?3:node.goal?2.2:node.id===0||node.id===graphRouteStart||node.id===graphRouteEnd?1.8:1;}
function labForceCameraDistance(){
  if(!labForceGraph)return 0;const position=labForceGraph.cameraPosition(),target=labForceGraph.controls().target||{x:0,y:0,z:0};
  return Math.hypot(position.x-target.x,position.y-target.y,position.z-target.z);
}
function labForceTickBudget(){
  const count=genericGraph?.nodes.length||0;return count<500?90:count<2500?60:count<10000?32:16;
}
function fitLabForceGraph(duration=650){
  if(!labForceGraph)return;
  labForceGraph.zoomToFit(duration,18);
  setTimeout(()=>{
    if(!labForceGraph)return;
    const position=labForceGraph.cameraPosition(),target=labForceGraph.controls().target||{x:0,y:0,z:0};
    const factor=.66;
    labForceGraph.cameraPosition({
      x:target.x+(position.x-target.x)*factor,
      y:target.y+(position.y-target.y)*factor,
      z:target.z+(position.z-target.z)*factor
    },target,260);
  },duration+40);
}
function refreshLabForceGraph(fit=false){
  if(!genericGraph)return;const graph=ensureLabForceGraph();
  labForceHighlightedLinks=new Set([...graphHistoryEdges,...graphRouteEdges].map(edge=>labForceLinkKey(edge.source,edge.target)));
  graph
    .backgroundColor(document.documentElement.classList.contains('dark')?'#1b1f1c':'#f2f3ef')
    .nodeColor(labForceNodeColor)
    .nodeVal(labForceNodeValue)
    .linkColor(labForceLinkColor)
    .linkWidth(link=>labForceHighlightedLinks.has(labForceLinkKey(link.source,link.target))?1.4:genericGraph.nodes.length<1500?.28:0)
    .linkOpacity(genericGraph.nodes.length<1500?.24:.14);
  $('lab-graph-summary').textContent='3d-force-graph · '+structuralLayoutLabel()+' · '+genericGraph.nodes.length.toLocaleString()+' 节点 · '+labForceLinks.length.toLocaleString()+' 条无向连接 · '+graphKindLabel();
  if(fit){labForceNeedsFit=true;setTimeout(()=>fitLabForceGraph(),80);}
}
function ensureLabForceGraph(){
  if(labForceGraph)return labForceGraph;
  if(!window.ForceGraph3D)throw new Error('3d-force-graph runtime unavailable');
  if(!labForceNodes.length)prepareLabForceGraphData();
  const container=$('lab-graph-force'),count=labForceNodes.length;
  labForceWidth=labGraphViewportWidth;labForceHeight=labGraphViewportHeight;
  labForceGraph=new window.ForceGraph3D(container,{controlType:'orbit',rendererConfig:{antialias:count<5000,alpha:false,powerPreference:'high-performance'}})
    .width(labForceWidth)
    .height(labForceHeight)
    .backgroundColor(document.documentElement.classList.contains('dark')?'#1b1f1c':'#f2f3ef')
    .showNavInfo(false)
    .nodeId('id')
    .nodeRelSize(count>10000?.28:count>2500?.42:count>500?.68:1)
    .nodeResolution(3)
    .nodeColor(labForceNodeColor)
    .nodeVal(labForceNodeValue)
    .nodeOpacity(count>10000?.45:count>2500?.58:.82)
    .nodeLabel(node=>'#'+node.id+' · d='+node.distance+(node.goal?' · GOAL':''))
    .linkColor(labForceLinkColor)
    .linkOpacity(count<1500?.24:.14)
    .linkWidth(0)
    .linkDirectionalParticles(0)
    .linkHoverPrecision(0)
    .enableNodeDrag(count<5000)
    .enablePointerInteraction(true)
    .warmupTicks(0)
    .cooldownTicks(labForceTickBudget())
    .cooldownTime(5000)
    .d3AlphaMin(.02)
    .d3AlphaDecay(count>10000?.24:.12)
    .d3VelocityDecay(.58)
    .onNodeClick(node=>selectGraphNode(Number(node.id)))
    .onEngineStop(()=>{if(labForceNeedsFit){labForceNeedsFit=false;requestAnimationFrame(()=>fitLabForceGraph());}$('lab-graph-summary').textContent='3d-force-graph · '+(labForcePinned?'结构坐标已固定':'局部松弛已冷却')+' · '+genericGraph.nodes.length.toLocaleString()+' 节点 · '+graphKindLabel();})
    .graphData({nodes:labForceNodes,links:labForceLinks});
  const linkForce=labForceGraph.d3Force('link');linkForce?.distance(link=>link.restLength).strength(count>10000?.015:.045).iterations(1);
  const chargeForce=labForceGraph.d3Force('charge');chargeForce?.strength(count<500?-10:count<5000?-3:-.7).distanceMax(count<5000?90:48).theta(1.25);
  labForceGraph.d3Force('reference-anchor',labReferenceAnchorForce(count>10000?.02:.012));
  labForceGraph.renderer().setPixelRatio(Math.min(window.devicePixelRatio||1,count>10000?1:1.5));
  labForcePinned=true;
  return labForceGraph;
}
function releaseAndReheatLabForceGraph(){
  const graph=ensureLabForceGraph();labForcePinned=false;
  for(const node of labForceNodes){node.fx=null;node.fy=null;node.fz=null;}
  graph.cooldownTicks(labForceTickBudget()).cooldownTime(5000).d3ReheatSimulation();
  $('lab-graph-summary').textContent='3d-force-graph · 从四维结构坐标释放并进行本地有限松弛 · '+genericGraph.nodes.length.toLocaleString()+' 节点';
}
function restoreLabForceInitialLayout(){
  const graph=ensureLabForceGraph();labForcePinned=true;
  for(const node of labForceNodes){node.x=node.fx=node.rx;node.y=node.fy=node.ry;node.z=node.fz=node.rz;node.vx=node.vy=node.vz=0;}
  graph.cooldownTicks(1).cooldownTime(800).d3ReheatSimulation();refreshLabForceGraph(true);
}
function disposeLabForceGraph(){
  if(labForceGraph){labForceGraph.pauseAnimation?.();labForceGraph.graphData({nodes:[],links:[]});labForceGraph._destructor?.();}
  labForceGraph=null;labForceNodes=[];labForceLinks=[];labForceHighlightedLinks=new Set();labForcePinned=false;labForceNeedsFit=false;labForceWidth=0;labForceHeight=0;
  $('lab-graph-force')?.replaceChildren();
}
function graphVisibleSet() {
  if (graphMode === 'overview') return new Set(genericGraph.nodes.map(node => node.id));
  const visible=new Set(graphHistory),adjacency=graphAdjacency();for(const id of graphHistory)for(const edge of adjacency[id]||[])visible.add(edge.target);for(const edge of graphRouteEdges){visible.add(edge.source);visible.add(edge.target);}return visible;
}
function graphPosition(id){return graphMode==='explore'?(graphExploreLayout.get(id)||graphLayout[id]):graphLayout[id];}
function settleExploreLayout(visible){
  const ids=[...visible],adjacency=graphAdjacency();for(const id of ids)if(!graphExploreLayout.has(id)){const base=graphLayout[id];graphExploreLayout.set(id,new THREE.Vector3(base.x*.22,base.y*.35,base.z*.35));}
  const iterations=ids.length<120?16:ids.length<350?5:0;if(!iterations)return;
  for(let step=0;step<iterations;step++){const forces=new Map(ids.map(id=>[id,new THREE.Vector3()]));
    for(let i=0;i<ids.length;i++)for(let j=i+1;j<ids.length;j++){const a=graphExploreLayout.get(ids[i]),b=graphExploreLayout.get(ids[j]),delta=a.clone().sub(b),d2=Math.max(.08,delta.lengthSq()),push=delta.normalize().multiplyScalar(.055/d2);forces.get(ids[i]).add(push);forces.get(ids[j]).sub(push);}
    for(const id of ids)for(const edge of adjacency[id]||[]){if(!visible.has(edge.target)||edge.source>edge.target)continue;const a=graphExploreLayout.get(edge.source),b=graphExploreLayout.get(edge.target),delta=b.clone().sub(a),distance=Math.max(.01,delta.length()),spring=delta.normalize().multiplyScalar((distance-1.25)*.045);forces.get(edge.source).add(spring);forces.get(edge.target).sub(spring);}
    for(const id of ids){const position=graphExploreLayout.get(id),force=forces.get(id);force.add(position.clone().multiplyScalar(-.018));force.z-=position.z*.04;position.add(force.multiplyScalar(.55));}
  }
}

function disposeThreeObject(object){object.traverse(child=>{child.geometry?.dispose();if(Array.isArray(child.material))child.material.forEach(material=>material.dispose());else child.material?.dispose();});}
function addGraphLine(edges,color,opacity){const data=[];for(const edge of edges){const a=graphPosition(edge.source),b=graphPosition(edge.target);if(a&&b)data.push(a.x,a.y,a.z,b.x,b.y,b.z);}if(!data.length)return;const geometry=new THREE.BufferGeometry();geometry.setAttribute('position',new THREE.Float32BufferAttribute(data,3));labGraphGroup.add(new THREE.LineSegments(geometry,new THREE.LineBasicMaterial({color,transparent:opacity<1,opacity})));}
function addGraphDepthLines(edges,opacity){
  const data=[],colors3=[],maxDistance=graphMaxDistance();
  for(const edge of edges){
    const a=graphPosition(edge.source),b=graphPosition(edge.target);if(!a||!b)continue;
    const source=genericGraph.nodes[edge.source],target=genericGraph.nodes[edge.target];
    const color=graphDepthColor(((source?.distance||0)+(target?.distance||0))*.5,maxDistance);
    data.push(a.x,a.y,a.z,b.x,b.y,b.z);colors3.push(color.r,color.g,color.b,color.r,color.g,color.b);
  }
  if(!data.length)return;
  const geometry=new THREE.BufferGeometry();geometry.setAttribute('position',new THREE.Float32BufferAttribute(data,3));geometry.setAttribute('color',new THREE.Float32BufferAttribute(colors3,3));
  labGraphGroup.add(new THREE.LineSegments(geometry,new THREE.LineBasicMaterial({vertexColors:true,transparent:opacity<1,opacity})));
}
function addGraphMarker(id,color,scale=1){if(id==null||!graphPosition(id))return;const marker=new THREE.Mesh(new THREE.TorusGeometry(.28,.075,8,24),new THREE.MeshBasicMaterial({color,depthTest:false}));marker.position.copy(graphPosition(id));marker.renderOrder=5;marker.userData.pixelDiameter=18*scale;labGraphGroup.add(marker);}
function rebuildGenericGraph(fit=false){
  if(!genericGraph)return;if(graphMode==='force'){refreshLabForceGraph(fit);return;}while(labGraphGroup.children.length){const child=labGraphGroup.children.pop();disposeThreeObject(child);}const visible=graphVisibleSet();if(graphMode==='explore')settleExploreLayout(visible);graphVisibleIds=graphMode==='overview'?genericGraph.nodes.map(node=>node.id):[...visible].sort((a,b)=>a-b);const positions=[],colors3=[];
  const discovered=new Set(graphHistory),maxDistance=graphMaxDistance();
  for(const id of graphVisibleIds){const node=genericGraph.nodes[id],position=graphPosition(id);positions.push(position.x,position.y,position.z);const color=new THREE.Color(node.goal?0x28736d:id===0?0xc58d34:graphMode==='explore'&&!discovered.has(id)?0x65a29a:graphDepthColor(node.distance,maxDistance));colors3.push(color.r,color.g,color.b);}
  const count=graphVisibleIds.length,pointSize=graphMode==='overview'?(count>10000?.65:count>2500?.8:count>500?1.15:2.4):3.5,pointOpacity=graphMode==='overview'?(count>10000?.24:count>2500?.32:count>500?.44:.68):.82;
  const geometry=new THREE.BufferGeometry();geometry.setAttribute('position',new THREE.Float32BufferAttribute(positions,3));geometry.setAttribute('color',new THREE.Float32BufferAttribute(colors3,3));labGraphPoints=new THREE.Points(geometry,new THREE.PointsMaterial({size:pointSize,vertexColors:true,sizeAttenuation:false,transparent:true,opacity:pointOpacity,depthWrite:false}));labGraphPoints.userData.nodeIds=graphVisibleIds;labGraphGroup.add(labGraphPoints);
  const sourceEdges=graphMode==='overview'?genericGraph.edges:graphVisibleIds.flatMap(id=>graphAdjacency()[id]||[]);
  const seen=new Set(),visibleEdges=sourceEdges.filter(edge=>{if(!visible.has(edge.source)||!visible.has(edge.target))return false;if(graphMode!=='overview')return true;const key=Math.min(edge.source,edge.target)+':'+Math.max(edge.source,edge.target);if(seen.has(key))return false;seen.add(key);return true;});
  addGraphDepthLines(visibleEdges,graphMode==='overview'?(count>10000?.3:count>2500?.4:.52):.32);addGraphLine(graphHistoryEdges,0xc58d34,.95);addGraphLine(graphRouteEdges,0x27302b,.85);addGraphMarker(graphRouteStart,0xc58d34,.9);addGraphMarker(graphRouteEnd,0x28736d,.9);addGraphMarker(graphCurrent,0xa83934,1.25);
  labGraphScene.background=new THREE.Color(document.documentElement.classList.contains('dark')?0x1b1f1c:0xf2f3ef);$('lab-graph-summary').textContent=(graphMode==='overview'?'结构全览 · '+structuralLayoutLabel():'局部探索图')+' · '+graphVisibleIds.length.toLocaleString()+' / '+genericGraph.nodes.length.toLocaleString()+' 节点 · '+genericGraph.edges.length.toLocaleString()+' 条有向边 · '+graphKindLabel();if(fit)fitGenericGraph();
}
function fitGenericGraph(){if(!genericGraph||!graphVisibleIds.length)return;const box=new THREE.Box3();for(const id of graphVisibleIds)box.expandByPoint(graphPosition(id));const center=box.getCenter(new THREE.Vector3()),size=Math.max(4,box.getSize(new THREE.Vector3()).length());labGraphControls.target.copy(center);labGraphCamera.position.copy(center).add(new THREE.Vector3(size*.65,size*.45,size*.75));labGraphCamera.near=.05;labGraphCamera.far=Math.max(100,size*15);labGraphCamera.updateProjectionMatrix();labGraphControls.update();}
function shortestGraphRoute(source,target){if(source===target)return[];const adjacency=graphAdjacency(),queue=[source],parent=new Map([[source,null]]),parentEdge=new Map();for(let cursor=0;cursor<queue.length;cursor++){const node=queue[cursor];for(const edge of adjacency[node]||[]){if(parent.has(edge.target))continue;parent.set(edge.target,node);parentEdge.set(edge.target,edge);if(edge.target===target){const path=[];let at=target;while(at!==source){path.push(parentEdge.get(at));at=parent.get(at);}return path.reverse();}queue.push(edge.target);}}return null;}
function applyGraphEdge(edge){graphCurrent=edge.target;graphHistory.push(edge.target);graphHistoryEdges.push(edge);renderCurrentPlayBoard();updateGraphReadout();rebuildGenericGraph();}
function setGraphCurrent(target){const route=shortestGraphRoute(graphCurrent,target);if(!route)return;for(const edge of route)applyGraphEdge(edge);}
function selectGraphNode(id){if(graphSelectionMode==='start'){graphRouteStart=id;graphRouteEnd=null;graphRoutePinned=true;graphSelectionMode='end';$('lab-route-start').classList.remove('active');$('lab-route-end').classList.add('active');}else{if(!graphRoutePinned)graphRouteStart=graphCurrent;graphRouteEnd=id;graphRoutePinned=false;}graphRouteEdges=graphRouteEnd==null?[]:(shortestGraphRoute(graphRouteStart,graphRouteEnd)||[]);$('lab-route-start-id').textContent='#'+graphRouteStart;$('lab-route-end-id').textContent=graphRouteEnd==null?'未选择':'#'+graphRouteEnd;$('lab-route-play').disabled=graphRouteEnd==null;rebuildGenericGraph();}
async function playGraphRoute(){if(graphRouteEnd==null)return;const token=++graphAnimationToken,toStart=shortestGraphRoute(graphCurrent,graphRouteStart)||[],route=shortestGraphRoute(graphRouteStart,graphRouteEnd)||[];$('lab-route-play').disabled=true;for(const edge of [...toStart,...route]){if(token!==graphAnimationToken)return;applyGraphEdge(edge);await new Promise(resolve=>setTimeout(resolve,220));}$('lab-route-play').disabled=false;}
function updateGraphReadout(){if(!genericGraph)return;const node=genericGraph.nodes[graphCurrent],adjacency=graphAdjacency();$('lab-graph-node').textContent='#'+graphCurrent;$('lab-graph-distance').textContent=node.distance;$('lab-graph-degree').textContent=(adjacency[graphCurrent]||[]).length;$('lab-graph-complete').textContent=genericGraph.complete?'完整可达图':genericGraph.truncated?'资源截断子图':'A* 解搜索子图';$('lab-graph-complete').className=genericGraph.complete?'complete':genericGraph.truncated?'truncated':'solution-subgraph';$('lab-graph-claim').textContent='GraphPath spec graph state0 state'+graphCurrent;const constructors=graphHistoryEdges.map((edge,index)=>'GraphPath.cons edge'+(index+1)+' checked'+(index+1)).join('  →  ');$('lab-graph-proof-text').textContent=(constructors||'GraphPath.nil state0')+'  ⇒  Reachable spec state0 state'+graphCurrent;}
function initializeGenericGraph(){if(!genericGraph)return;structuralLayoutReady=false;structuralLayoutMeta=null;graphLayout=computeGraphLayout();graphExploreLayout=new Map();prepareLabForceGraphData();const requestedMode=laboratoryQuery.get('graphMode');if(['overview','force','explore'].includes(requestedMode))graphMode=requestedMode;graphRouteStart=0;graphRouteEnd=null;graphRouteEdges=[];graphRoutePinned=false;renderCurrentPlayBoard();updateGraphReadout();setLabGraphMode(graphMode,true);startStructuralLayout();if(laboratoryQuery.get('autoManual')==='1'){const edge=(graphAdjacency()[0]||[])[0];if(edge){const board=$('lab-play-board'),block=board.querySelector('[data-piece="'+(edge.block-1)+'"]'),rect=block?.getBoundingClientRect(),boardRect=board.getBoundingClientRect(),delta={up:[0,-1],down:[0,1],left:[-1,0],right:[1,0]}[edge.direction];if(block&&rect){const x=rect.left+rect.width/2,y=rect.top+rect.height/2;block.dispatchEvent(new PointerEvent('pointerdown',{bubbles:true,clientX:x,clientY:y}));block.dispatchEvent(new PointerEvent('pointerup',{bubbles:true,clientX:x+delta[0]*boardRect.width/boardDimensions().width*.7,clientY:y+delta[1]*boardRect.height/boardDimensions().height*.7}));document.body.dataset.manualResult=graphCurrent;}}}if(laboratoryQuery.get('autoExplore')==='1'){const target=genericGraph.nodes.find(node=>node.goal)||genericGraph.nodes.at(-1);if(target){selectGraphNode(target.id);playGraphRoute();}$(graphMode==='force'?'lab-graph-force':'lab-graph-canvas').scrollIntoView({block:'center'});}}
function graphNodeAt(event){if(!labGraphPoints)return null;const rect=labGraphRenderer.domElement.getBoundingClientRect();labGraphPointer.x=(event.clientX-rect.left)/rect.width*2-1;labGraphPointer.y=-(event.clientY-rect.top)/rect.height*2+1;labGraphRaycaster.setFromCamera(labGraphPointer,labGraphCamera);labGraphRaycaster.params.Points.threshold=Math.max(.12,labGraphCamera.position.distanceTo(labGraphControls.target)/120);const hit=labGraphRaycaster.intersectObject(labGraphPoints)[0];return hit?labGraphPoints.userData.nodeIds[hit.index]:null;}
function focusGraphNode(id){if(graphMode==='force'){const node=labForceNodes[id];if(!node)return;const position=labForceGraph.cameraPosition(),target=labForceGraph.controls().target||{x:0,y:0,z:0},dx=position.x-target.x,dy=position.y-target.y,dz=position.z-target.z,length=Math.max(1,Math.hypot(dx,dy,dz));labForceGraph.cameraPosition({x:node.x+dx/length*12,y:node.y+dy/length*12,z:node.z+dz/length*12},{x:node.x,y:node.y,z:node.z},550);return;}const target=graphPosition(id);if(!target)return;const direction=labGraphCamera.position.clone().sub(labGraphControls.target).normalize();labGraphControls.target.copy(target);labGraphCamera.position.copy(target).add(direction.multiplyScalar(8));labGraphControls.update();}
function setLabGraphMode(mode,fit=true){
  if(!['overview','force','explore'].includes(mode))return;graphMode=mode;
  document.querySelectorAll('[data-lab-graph-mode]').forEach(item=>item.classList.toggle('active',item.dataset.labGraphMode===mode));
  $('lab-graph-canvas').hidden=mode==='force';$('lab-graph-force').hidden=mode!=='force';$('lab-force-reheat').hidden=mode!=='force';$('lab-force-pin').hidden=mode!=='force';$('lab-graph-tip').hidden=true;
  resizeLabGraphSurfaces();
  if(mode==='force'){ensureLabForceGraph().resumeAnimation();refreshLabForceGraph(fit);}else{labForceGraph?.pauseAnimation();rebuildGenericGraph(fit);}
}
document.querySelectorAll('[data-lab-graph-mode]').forEach(button=>button.onclick=()=>setLabGraphMode(button.dataset.labGraphMode,true));
$('lab-route-start').onclick=()=>{graphSelectionMode='start';$('lab-route-start').classList.add('active');$('lab-route-end').classList.remove('active');};$('lab-route-end').onclick=()=>{graphSelectionMode='end';$('lab-route-end').classList.add('active');$('lab-route-start').classList.remove('active');};$('lab-route-play').onclick=playGraphRoute;$('lab-graph-home').onclick=()=>{graphAnimationToken++;graphCurrent=0;graphHistory=[0];graphHistoryEdges=[];graphRouteStart=0;graphRouteEnd=null;graphRouteEdges=[];graphRoutePinned=false;renderCurrentPlayBoard();updateGraphReadout();rebuildGenericGraph(true);};$('lab-graph-locate').onclick=()=>focusGraphNode(graphCurrent);
$('lab-force-reheat').onclick=releaseAndReheatLabForceGraph;$('lab-force-pin').onclick=restoreLabForceInitialLayout;
$('lab-layout-recompute').onclick=startStructuralLayout;
const labForceSurface=$('lab-graph-force');
labForceSurface.addEventListener('pointerdown',event=>{labForcePointerDown={x:event.clientX,y:event.clientY};labForceDragActive=false;});
labForceSurface.addEventListener('pointermove',event=>{
  if(labForcePointerDown&&!labForceDragActive&&Math.hypot(event.clientX-labForcePointerDown.x,event.clientY-labForcePointerDown.y)>4){
    labForceDragActive=true;labForceGraph?.enablePointerInteraction(false);$('lab-graph-tip').hidden=true;
  }
});
function finishLabForcePointer(){
  labForcePointerDown=null;
  if(labForceDragActive)requestAnimationFrame(()=>labForceGraph?.enablePointerInteraction(true));
  labForceDragActive=false;
}
labForceSurface.addEventListener('pointerup',finishLabForcePointer);
labForceSurface.addEventListener('pointercancel',finishLabForcePointer);
labForceSurface.addEventListener('pointerleave',finishLabForcePointer);
function zoomLabGraph(factor){if(graphMode==='force'){const graph=ensureLabForceGraph(),position=graph.cameraPosition(),target=graph.controls().target||{x:0,y:0,z:0};graph.cameraPosition({x:target.x+(position.x-target.x)*factor,y:target.y+(position.y-target.y)*factor,z:target.z+(position.z-target.z)*factor},target,280);return;}labGraphCamera.position.sub(labGraphControls.target).multiplyScalar(factor).add(labGraphControls.target);}
$('lab-graph-zoom-in').onclick=()=>zoomLabGraph(.55);$('lab-graph-zoom-out').onclick=()=>zoomLabGraph(1.7);
labGraphRenderer.domElement.addEventListener('pointerdown',event=>{
  labGraphPointerDown={x:event.clientX,y:event.clientY};
  labGraphHoverPosition=null;$('lab-graph-tip').hidden=true;
});
labGraphRenderer.domElement.addEventListener('pointerup',event=>{
  const start=labGraphPointerDown;labGraphPointerDown=null;
  if(!start||Math.hypot(event.clientX-start.x,event.clientY-start.y)>5)return;
  const id=graphNodeAt(event);if(id!=null)selectGraphNode(id);
});
function updateLabGraphHover(position){
  if(!position||labGraphPointerDown)return;
  const event={clientX:position.clientX,clientY:position.clientY};
  const id=graphNodeAt(event),tip=$('lab-graph-tip'),rect=labGraphRenderer.domElement.getBoundingClientRect();
  if(id==null){tip.hidden=true;return;}
  const node=genericGraph.nodes[id];tip.hidden=false;
  tip.style.left=(event.clientX-rect.left+12)+'px';tip.style.top=(event.clientY-rect.top+12)+'px';
  tip.textContent='#'+id+' · d='+node.distance+(node.goal?' · GOAL':'');
}
labGraphRenderer.domElement.addEventListener('pointermove',event=>{
  labGraphHoverPosition={clientX:event.clientX,clientY:event.clientY};
  if(labGraphPointerDown||labGraphHoverFrame!==null)return;
  const run=now=>{
    if(now-labGraphLastHoverPick<42){labGraphHoverFrame=requestAnimationFrame(run);return;}
    labGraphHoverFrame=null;labGraphLastHoverPick=now;updateLabGraphHover(labGraphHoverPosition);
  };
  labGraphHoverFrame=requestAnimationFrame(run);
});
function clearLabGraphPointer(){labGraphPointerDown=null;labGraphHoverPosition=null;$('lab-graph-tip').hidden=true;}
labGraphRenderer.domElement.addEventListener('pointercancel',clearLabGraphPointer);
labGraphRenderer.domElement.addEventListener('pointerleave',clearLabGraphPointer);
let labLastZoomText='';
function updateLabZoomLabel(distance){const text=Math.round(distance)+'u';if(text===labLastZoomText)return;labLastZoomText=text;$('lab-graph-zoom').textContent=text;}
function resizeLabGraphSurfaces(){
  const stage=$('lab-graph-canvas').parentElement,rect=stage.getBoundingClientRect();
  const width=Math.max(1,Math.round(rect.width)),height=Math.max(1,Math.round(rect.height));
  if(width===labGraphViewportWidth&&height===labGraphViewportHeight)return;
  labGraphViewportWidth=width;labGraphViewportHeight=height;
  labGraphRenderer.setSize(width,height,false);labGraphCamera.aspect=width/height;labGraphCamera.updateProjectionMatrix();
  if(labForceGraph&&(width!==labForceWidth||height!==labForceHeight)){
    labForceWidth=width;labForceHeight=height;labForceGraph.width(width).height(height);
  }
}
new ResizeObserver(resizeLabGraphSurfaces).observe($('lab-graph-canvas').parentElement);
resizeLabGraphSurfaces();
function animateLabGraph(){requestAnimationFrame(animateLabGraph);if(graphMode==='force'&&labForceGraph){updateLabZoomLabel(labForceCameraDistance());return;}labGraphControls.update();const field=2*Math.tan(THREE.MathUtils.degToRad(labGraphCamera.fov)/2),height=labGraphViewportHeight;labGraphGroup.children.forEach(child=>{if(!child.userData.pixelDiameter)return;const world=child.position.distanceTo(labGraphCamera)*field*child.userData.pixelDiameter/height;child.scale.setScalar(world/.7);});updateLabZoomLabel(labGraphCamera.position.distanceTo(labGraphControls.target));labGraphRenderer.render(labGraphScene,labGraphCamera);}animateLabGraph();

$('lab-prev').onclick=undoGraphMove;$('lab-next').onclick=hintManualMove;$('lab-play-reset').onclick=resetManualExploration;$('lab-play-hint').onclick=hintManualMove;
document.querySelectorAll('[data-lab-move]').forEach(button=>button.onclick=()=>{if(playSelectedBlock==null)setStatus('limit','请先选择一个编号块');else manualMove(playSelectedBlock,button.dataset.labMove);});
$('lab-play-board').addEventListener('keydown',event=>{const direction={ArrowUp:'up',ArrowDown:'down',ArrowLeft:'left',ArrowRight:'right'}[event.key];if(direction&&playSelectedBlock!=null){event.preventDefault();manualMove(playSelectedBlock,direction);}});

loadPreset('tiny');
const laboratoryQuery = new URLSearchParams(location.search);
if (!laboratoryQuery.get('fullSpaceComponent') && laboratoryQuery.get('preset') && presets[laboratoryQuery.get('preset')]) loadPreset(laboratoryQuery.get('preset'));
if (laboratoryQuery.get('mode') === 'lab') switchMode('lab');
if (laboratoryQuery.get('strategy') === 'bfs') document.querySelector('[data-lab-strategy="bfs"]').click();
if (laboratoryQuery.get('shortTimeout') === '1') $('lab-timeout-seconds').value='1';
if (laboratoryQuery.get('badLimits') === '1') { $('lab-max-states').value=''; $('lab-max-depth').value='10000.8'; }
if (laboratoryQuery.get('autoBoardResize') === '1') requestAnimationFrame(()=>{const before=$('lab-width').value+'x'+$('lab-height').value;document.querySelector('[data-board-dimension="width"][data-board-delta="1"]').click();document.body.dataset.boardResizeResult=before+'->'+$('lab-width').value+'x'+$('lab-height').value;});
if (laboratoryQuery.get('autoBoardShrink') === '1') requestAnimationFrame(()=>{document.querySelector('[data-board-dimension="width"][data-board-delta="-1"]').click();document.body.dataset.boardShrinkMessage=$('lab-status').textContent;});
if (laboratoryQuery.get('autoAdd') === '1') requestAnimationFrame(()=>{const before=pieces.length,add=$('lab-initial-board').querySelector('.lab-add-cell');add?.click();document.body.dataset.addResult=before+'->'+pieces.length;});
if (laboratoryQuery.get('autoEdit') === '1') requestAnimationFrame(() => {
  const toggles = document.querySelectorAll('.lab-goal-toggle input'); if (toggles[1]) toggles[1].click();
  const board = $('lab-initial-board'), block = board.querySelector('.lab-block');
  if (block) {
    const rect = board.getBoundingClientRect(), cellX = rect.width / boardDimensions().width, cellY = rect.height / boardDimensions().height;
    block.dispatchEvent(new PointerEvent('pointerdown', { bubbles: true, clientX: rect.left + cellX / 2, clientY: rect.top + cellY / 2 }));
    window.dispatchEvent(new PointerEvent('pointerup', { bubbles: true, clientX: rect.left + cellX / 2, clientY: rect.top + cellY * 1.5 }));
    document.body.dataset.dragResult = pieces[0].x + ',' + pieces[0].y;
    document.body.dataset.constraintResult = pieces[1].goalX + ',' + pieces[1].goalY;
    const resizedBoard = $('lab-initial-board'), resizeHandle = resizedBoard.querySelector('.lab-resize-handle'), resizedRect = resizedBoard.getBoundingClientRect();
    if (resizeHandle) {
      resizeHandle.dispatchEvent(new PointerEvent('pointerdown', { bubbles: true, clientX: resizedRect.left + cellX, clientY: resizedRect.top + cellY * 2 }));
      window.dispatchEvent(new PointerEvent('pointerup', { bubbles: true, clientX: resizedRect.left + cellX * 1.8, clientY: resizedRect.top + cellY * 1.8 }));
      document.body.dataset.resizeResult = pieces[0].width + 'x' + pieces[0].height;
    }
  }
});
if (laboratoryQuery.get('autoSolve') === '1' && !laboratoryQuery.get('fullSpaceComponent')) callSolver(false);
if (/^\d+$/.test(laboratoryQuery.get('fullSpaceComponent') || '')) {
  switchMode('lab');
  loadFullSpaceComponent(Number(laboratoryQuery.get('fullSpaceComponent'))).catch(error => {
    setStatus('invalid', error.message);
    console.error(error);
  });
}
