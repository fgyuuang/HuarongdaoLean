import * as THREE from './vendor/three.module.min.js';
import { OrbitControls } from './vendor/OrbitControls.js';

const DATA_URL = './full-shape-components.json';
const GOLDEN_ANGLE = Math.PI * (3 - Math.sqrt(5));
const SLOT_COORDINATES = [
  [-1, -1],
  [1, -1],
  [-1, 1],
  [1, 1]
];
const COLORS = {
  background: 0xf2f0ea,
  ordinary: new THREE.Color(0x3d6784),
  small: new THREE.Color(0x87908c),
  classic: new THREE.Color(0xa93a32),
  verticalClassic: new THREE.Color(0xd38a2c),
  horizontal: new THREE.Color(0x247f78),
  vertical: new THREE.Color(0xd38a2c),
  rotation: new THREE.Color(0x69599a)
};

const canvas = document.querySelector('#full-space-canvas');
const sceneHost = document.querySelector('#full-scene');
const loading = document.querySelector('#loading');
const hoverTip = document.querySelector('#hover-tip');
const renderer = new THREE.WebGLRenderer({ canvas, antialias: true, alpha: false });
renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
renderer.setClearColor(COLORS.background, 1);
renderer.outputColorSpace = THREE.SRGBColorSpace;

const scene = new THREE.Scene();
scene.fog = new THREE.Fog(COLORS.background, 1050, 2100);
const camera = new THREE.PerspectiveCamera(43, 1, 0.1, 5000);
camera.position.set(0, 180, 1120);
const controls = new OrbitControls(camera, canvas);
controls.enableDamping = true;
controls.dampingFactor = 0.075;
controls.minDistance = 120;
controls.maxDistance = 2400;
controls.target.set(0, 0, 0);

const raycaster = new THREE.Raycaster();
const pointer = new THREE.Vector2(-2, -2);
const nodeGroup = new THREE.Group();
const linkGroup = new THREE.Group();
const highlightGroup = new THREE.Group();
scene.add(linkGroup, nodeGroup, highlightGroup);

let data;
let nodes = [];
let nodesById = new Map();
let nodeMesh;
let selectedId;
let hoveredId;
let pointerDown = null;
let bounds = new THREE.Box3();
const linkObjects = {};

function formatNumber(value) {
  return Number(value).toLocaleString('zh-CN');
}

function orbitGroups(components) {
  const groups = new Map();
  for (const component of components) {
    if (!groups.has(component.kleinOrbit)) groups.set(component.kleinOrbit, []);
    groups.get(component.kleinOrbit).push(component);
  }
  return [...groups.entries()]
    .map(([id, members]) => ({
      id,
      members,
      totalStates: members.reduce((sum, member) => sum + member.stateCount, 0),
      maxStates: Math.max(...members.map(member => member.stateCount))
    }))
    .sort((a, b) => b.maxStates - a.maxStates || b.totalStates - a.totalStates || a.id - b.id);
}

function orbitCenter(rank) {
  if (rank === 0) return new THREE.Vector3(0, 0, 0);
  const ringRank = rank - 1;
  const radius = 74 + 31 * Math.sqrt(ringRank);
  const angle = ringRank * GOLDEN_ANGLE;
  return new THREE.Vector3(
    Math.cos(angle) * radius,
    Math.sin(angle) * radius * 0.7,
    82 * Math.sin(ringRank * 0.61) + 34 * Math.cos(ringRank * 0.19)
  );
}

function memberSlots(representative, membersById) {
  const ids = [
    representative.id,
    representative.horizontalComponent,
    representative.verticalComponent,
    representative.rotationComponent
  ];
  const sums = new Map();
  ids.forEach((id, index) => {
    if (!membersById.has(id)) return;
    const [x, y] = SLOT_COORDINATES[index];
    const value = sums.get(id) || { x: 0, y: 0, count: 0 };
    value.x += x;
    value.y += y;
    value.count += 1;
    sums.set(id, value);
  });
  return sums;
}

function computeLayout(components) {
  const byId = new Map(components.map(component => [component.id, component]));
  const groups = orbitGroups(components);
  const positions = new Map();

  groups.forEach((group, rank) => {
    const center = orbitCenter(rank);
    const representative = byId.get(group.id) || group.members[0];
    const memberIds = new Set(group.members.map(member => member.id));
    const slots = memberSlots(representative, memberIds);
    const localScale = rank === 0 ? 47 : 12 + Math.min(18, Math.log2(group.maxStates + 1) * 1.55);

    group.members.forEach((member, memberIndex) => {
      const slot = slots.get(member.id);
      const fallbackAngle = memberIndex * Math.PI * 2 / group.members.length;
      const localX = slot ? slot.x / slot.count : Math.cos(fallbackAngle);
      const localY = slot ? slot.y / slot.count : Math.sin(fallbackAngle);
      const localZ = group.members.length === 4
        ? (memberIndex % 2 === 0 ? -1 : 1) * localScale * 0.14
        : 0;
      positions.set(member.id, new THREE.Vector3(
        center.x + localX * localScale,
        center.y + localY * localScale,
        center.z + localZ
      ));
    });
  });

  return positions;
}

function nodeRadius(component) {
  return 2.5 + Math.log2(component.stateCount + 1) * 0.72;
}

function nodeColor(component) {
  if (component.id === data.meta.classicComponentId) return COLORS.classic;
  if (component.id === data.meta.verticalClassicComponentId) return COLORS.verticalClassic;
  const t = Math.min(1, Math.log2(component.stateCount + 1) / 15);
  return COLORS.small.clone().lerp(COLORS.ordinary, t);
}

function buildNodes() {
  const positions = computeLayout(data.components);
  nodes = data.components.map(component => ({
    ...component,
    position: positions.get(component.id),
    radius: nodeRadius(component)
  }));
  nodesById = new Map(nodes.map(node => [node.id, node]));

  const geometry = new THREE.SphereGeometry(1, 14, 10);
  const material = new THREE.MeshBasicMaterial({ vertexColors: true });
  nodeMesh = new THREE.InstancedMesh(geometry, material, nodes.length);
  nodeMesh.instanceMatrix.setUsage(THREE.StaticDrawUsage);
  nodeMesh.userData.kind = 'components';
  const matrix = new THREE.Matrix4();

  nodes.forEach((node, index) => {
    matrix.compose(node.position, new THREE.Quaternion(), new THREE.Vector3(node.radius, node.radius, node.radius));
    nodeMesh.setMatrixAt(index, matrix);
    nodeMesh.setColorAt(index, nodeColor(node));
    node.instanceId = index;
  });
  nodeMesh.instanceMatrix.needsUpdate = true;
  nodeMesh.instanceColor.needsUpdate = true;
  nodeGroup.add(nodeMesh);

  bounds = new THREE.Box3();
  nodes.forEach(node => bounds.expandByPoint(node.position));
  addLargeComponentHalos();
}

function addLargeComponentHalos() {
  const geometry = new THREE.TorusGeometry(1, 0.12, 8, 40);
  [
    [data.meta.classicComponentId, COLORS.classic],
    [data.meta.verticalClassicComponentId, COLORS.verticalClassic]
  ].forEach(([id, color]) => {
    const node = nodesById.get(id);
    if (!node) return;
    const ring = new THREE.Mesh(geometry, new THREE.MeshBasicMaterial({ color, transparent: true, opacity: 0.78 }));
    ring.position.copy(node.position);
    ring.scale.setScalar(node.radius * 1.65);
    ring.userData.componentId = id;
    highlightGroup.add(ring);
  });
}

function uniqueSymmetryPairs(field) {
  const pairs = [];
  for (const node of nodes) {
    const target = node[field];
    if (target !== node.id && node.id < target && nodesById.has(target)) pairs.push([node.id, target]);
  }
  return pairs;
}

function buildLineObject(field, color, opacity) {
  const pairs = uniqueSymmetryPairs(field);
  const coordinates = new Float32Array(pairs.length * 6);
  pairs.forEach(([sourceId, targetId], index) => {
    const source = nodesById.get(sourceId).position;
    const target = nodesById.get(targetId).position;
    coordinates.set([source.x, source.y, source.z, target.x, target.y, target.z], index * 6);
  });
  const geometry = new THREE.BufferGeometry();
  geometry.setAttribute('position', new THREE.BufferAttribute(coordinates, 3));
  const material = new THREE.LineBasicMaterial({ color, transparent: true, opacity, depthWrite: false });
  const lines = new THREE.LineSegments(geometry, material);
  lines.renderOrder = -1;
  linkGroup.add(lines);
  return { lines, count: pairs.length };
}

function buildLinks() {
  linkObjects.horizontal = buildLineObject('horizontalComponent', COLORS.horizontal, 0.42);
  linkObjects.vertical = buildLineObject('verticalComponent', COLORS.vertical, 0.48);
  linkObjects.rotation = buildLineObject('rotationComponent', COLORS.rotation, 0.32);
  linkObjects.rotation.lines.visible = false;
}

function boardPieces(component) {
  const definitions = [
    { name: '曹操', width: 2, height: 2, className: 'cao' },
    { name: '关羽', width: 2, height: 1, className: 'guan' },
    { name: '将', width: 1, height: 2, className: 'vertical' },
    { name: '将', width: 1, height: 2, className: 'vertical' },
    { name: '将', width: 1, height: 2, className: 'vertical' },
    { name: '将', width: 1, height: 2, className: 'vertical' },
    { name: '兵', width: 1, height: 1, className: 'soldier' },
    { name: '兵', width: 1, height: 1, className: 'soldier' },
    { name: '兵', width: 1, height: 1, className: 'soldier' },
    { name: '兵', width: 1, height: 1, className: 'soldier' }
  ];
  return definitions.map((definition, index) => ({ ...definition, position: component.positions[index] }));
}

function renderBoard(component) {
  const board = document.querySelector('#representative-board');
  board.replaceChildren();
  boardPieces(component).forEach(piece => {
    const element = document.createElement('div');
    element.className = `representative-piece ${piece.className}`;
    element.textContent = piece.name;
    element.style.left = `${piece.position[0] * 25}%`;
    element.style.top = `${piece.position[1] * 20}%`;
    element.style.width = `${piece.width * 25}%`;
    element.style.height = `${piece.height * 20}%`;
    board.appendChild(element);
  });
}

function componentLabel(component) {
  if (component.id === data.meta.classicComponentId) return ['传统初态', 'classic'];
  if (component.id === data.meta.verticalClassicComponentId) return ['上下翻转', 'vertical-classic'];
  if (component.horizontalFixed || component.verticalFixed) return ['对称固定', 'fixed'];
  return ['连续分量', 'ordinary'];
}

function selectComponent(id, moveCamera = false) {
  const component = nodesById.get(Number(id));
  if (!component) return false;
  selectedId = component.id;
  const [label, className] = componentLabel(component);
  document.querySelector('#component-title').textContent = `分量 #${component.id}`;
  const kind = document.querySelector('#component-kind');
  kind.textContent = label;
  kind.className = `component-kind ${className}`;
  document.querySelector('#component-states').textContent = formatNumber(component.stateCount);
  document.querySelector('#component-edges').textContent = formatNumber(component.directedEdgeCount / 2);
  document.querySelector('#component-orbit').textContent = `#${component.kleinOrbit}`;
  document.querySelector('#component-key').textContent = component.key;
  document.querySelector('#horizontal-id').textContent = `#${component.horizontalComponent}`;
  document.querySelector('#vertical-id').textContent = `#${component.verticalComponent}`;
  document.querySelector('#rotation-id').textContent = `#${component.rotationComponent}`;
  const fixed = [];
  if (component.horizontalFixed) fixed.push('左右固定');
  if (component.verticalFixed) fixed.push('上下固定');
  if (component.rotationFixed) fixed.push('旋转固定');
  document.querySelector('#fixed-summary').textContent = fixed.join(' · ') || '无对称固定';
  renderBoard(component);
  refreshNodeColors();
  if (moveCamera) focusNode(component);
  return true;
}

function openSelectedComponentInLaboratory() {
  const component = nodesById.get(selectedId);
  if (!component) return;
  const next = new URL('./index.html', location.href);
  next.searchParams.set('mode', 'lab');
  next.searchParams.set('fullSpaceComponent', String(component.id));
  location.href = next.href;
}

function refreshNodeColors() {
  if (!nodeMesh) return;
  nodes.forEach(node => {
    let color = nodeColor(node);
    if (node.id === selectedId) color = new THREE.Color(0x151817);
    else if (node.id === hoveredId) color = color.clone().lerp(new THREE.Color(0xffffff), 0.45);
    nodeMesh.setColorAt(node.instanceId, color);
  });
  nodeMesh.instanceColor.needsUpdate = true;
}

function fitView(duration = 0) {
  const center = bounds.getCenter(new THREE.Vector3());
  const size = bounds.getSize(new THREE.Vector3());
  const radius = Math.max(size.x, size.y, size.z) * 0.56;
  const distance = radius / Math.tan(THREE.MathUtils.degToRad(camera.fov * 0.5)) * 1.06;
  const destination = center.clone().add(new THREE.Vector3(0, distance * 0.17, distance));
  if (duration === 0) {
    camera.position.copy(destination);
    controls.target.copy(center);
    controls.update();
    return;
  }
  animateCamera(destination, center, duration);
}

function focusNode(node) {
  const direction = camera.position.clone().sub(controls.target).normalize();
  const destination = node.position.clone().add(direction.multiplyScalar(Math.max(95, node.radius * 13)));
  animateCamera(destination, node.position, 520);
}

function animateCamera(destination, target, duration) {
  const startPosition = camera.position.clone();
  const startTarget = controls.target.clone();
  const started = performance.now();
  function frame(now) {
    const t = Math.min(1, (now - started) / duration);
    const eased = 1 - Math.pow(1 - t, 3);
    camera.position.lerpVectors(startPosition, destination, eased);
    controls.target.lerpVectors(startTarget, target, eased);
    if (t < 1) requestAnimationFrame(frame);
  }
  requestAnimationFrame(frame);
}

function pointerFromEvent(event) {
  const rect = canvas.getBoundingClientRect();
  pointer.x = (event.clientX - rect.left) / rect.width * 2 - 1;
  pointer.y = -(event.clientY - rect.top) / rect.height * 2 + 1;
}

function hitTest(event) {
  pointerFromEvent(event);
  raycaster.setFromCamera(pointer, camera);
  const hit = raycaster.intersectObject(nodeMesh, false)[0];
  return hit ? nodes[hit.instanceId] : null;
}

function showHover(component, event) {
  hoveredId = component?.id;
  refreshNodeColors();
  if (!component) {
    hoverTip.classList.remove('visible');
    return;
  }
  hoverTip.textContent = `#${component.id} · ${formatNumber(component.stateCount)} 状态 · 轨道 #${component.kleinOrbit}`;
  const rect = sceneHost.getBoundingClientRect();
  hoverTip.style.left = `${Math.min(rect.width - hoverTip.offsetWidth - 12, event.clientX - rect.left + 12)}px`;
  hoverTip.style.top = `${Math.min(rect.height - hoverTip.offsetHeight - 34, event.clientY - rect.top + 12)}px`;
  hoverTip.classList.add('visible');
}

function updateMetrics() {
  const { meta } = data;
  document.querySelector('#state-count').textContent = formatNumber(meta.shapeStateCount);
  document.querySelector('#component-count').textContent = formatNumber(meta.componentCount);
  document.querySelector('#orbit-count').textContent = formatNumber(meta.kleinComponentOrbitCount);
  document.querySelector('#summary-states').textContent = formatNumber(meta.shapeStateCount);
  document.querySelector('#summary-edges').textContent = formatNumber(meta.directedEdgeCount / 2);
  document.querySelector('#summary-orbits').textContent = formatNumber(meta.kleinComponentOrbitCount);
  document.querySelector('#space-status').textContent =
    `${formatNumber(meta.componentCount)} 分量 · 左右 ${linkObjects.horizontal.count} 对 · 上下 ${linkObjects.vertical.count} 对 · 旋转 ${linkObjects.rotation.count} 对`;
}

function configureReturnLink() {
  const link = document.querySelector('#return-link');
  if (!link) return;
  const source = new URLSearchParams(location.search).get('from');
  if (source === 'lab') {
    link.href = './index.html?mode=lab';
    link.textContent = '返回关卡实验室';
    link.title = '返回关卡实验室';
  } else {
    link.href = './index.html';
    link.textContent = '返回任务图';
    link.title = '返回经典任务图';
  }
}

function bindUi() {
  document.querySelector('#show-horizontal').addEventListener('change', event => {
    linkObjects.horizontal.lines.visible = event.target.checked;
  });
  document.querySelector('#show-vertical').addEventListener('change', event => {
    linkObjects.vertical.lines.visible = event.target.checked;
  });
  document.querySelector('#show-rotation').addEventListener('change', event => {
    linkObjects.rotation.lines.visible = event.target.checked;
  });
  document.querySelector('#fit-view').addEventListener('click', () => fitView(520));

  const search = document.querySelector('#component-search');
  function submitSearch() {
    const query = search.value.trim();
    if (!query) return;
    const numeric = query.replace(/^#/, '');
    const exactId = /^\d+$/.test(numeric) ? Number(numeric) : null;
    const match = exactId != null
      ? nodesById.get(exactId)
      : nodes.find(node => node.key.includes(query));
    if (match) {
      selectComponent(match.id, true);
      search.setCustomValidity('');
    } else {
      search.setCustomValidity('没有匹配的连续分量');
      search.reportValidity();
    }
  }
  document.querySelector('#search-submit').addEventListener('click', submitSearch);
  search.addEventListener('keydown', event => {
    if (event.key === 'Enter') submitSearch();
    else search.setCustomValidity('');
  });

  document.querySelectorAll('[data-symmetry]').forEach(button => {
    button.addEventListener('click', () => {
      const current = nodesById.get(selectedId);
      if (!current) return;
      const fields = {
        horizontal: 'horizontalComponent',
        vertical: 'verticalComponent',
        rotation: 'rotationComponent'
      };
      selectComponent(current[fields[button.dataset.symmetry]], true);
    });
  });
  document.querySelector('#use-component').addEventListener('click', openSelectedComponentInLaboratory);

  canvas.addEventListener('pointerdown', event => {
    pointerDown = { x: event.clientX, y: event.clientY };
  });
  canvas.addEventListener('pointermove', event => {
    showHover(hitTest(event), event);
  });
  canvas.addEventListener('pointerleave', () => showHover(null));
  canvas.addEventListener('pointerup', event => {
    if (!pointerDown || Math.hypot(event.clientX - pointerDown.x, event.clientY - pointerDown.y) > 5) return;
    const hit = hitTest(event);
    if (hit) selectComponent(hit.id);
  });
  canvas.addEventListener('dblclick', event => {
    const hit = hitTest(event);
    if (hit) selectComponent(hit.id, true);
  });
}

function resize() {
  const width = sceneHost.clientWidth;
  const height = sceneHost.clientHeight;
  renderer.setSize(width, height, false);
  camera.aspect = width / Math.max(1, height);
  camera.updateProjectionMatrix();
}

function animate() {
  controls.update();
  highlightGroup.children.forEach(ring => ring.lookAt(camera.position));
  renderer.render(scene, camera);
  requestAnimationFrame(animate);
}

async function initialize() {
  configureReturnLink();
  const response = await fetch(DATA_URL);
  if (!response.ok) throw new Error(`全空间数据加载失败：HTTP ${response.status}`);
  data = await response.json();
  if (!Array.isArray(data.components) || data.components.length !== data.meta.componentCount) {
    throw new Error('全空间分量数据与元数据不一致');
  }
  buildNodes();
  buildLinks();
  updateMetrics();
  bindUi();
  resize();
  fitView();
  selectComponent(data.meta.classicComponentId);
  loading.hidden = true;
  animate();
}

window.addEventListener('resize', resize);
initialize().catch(error => {
  loading.innerHTML = `<strong>${error.message}</strong>`;
  console.error(error);
});
