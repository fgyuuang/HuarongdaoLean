import {
  evidenceLevels,
  formalStages,
  formalizationStats,
  modelFormalization,
  kernelComponents,
  researchContinuations,
  sourceFiles,
  theoremDependencyEdges,
  theoremById,
  theoremRecords
} from './formalization-data.js';

const root = document.getElementById('formalization-workspace');
const content = document.getElementById('formal-content');
const nav = document.getElementById('formal-nav');
const modeClassic = document.getElementById('mode-classic');
const modeLab = document.getElementById('mode-lab');
const modeFormalization = document.getElementById('mode-formalization');
const escapeHtml = value => String(value ?? '').replace(/[&<>"']/g, char => ({
  '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'
}[char]));

let currentView = 'overview';
let selectedStage = 'model';
let selectedTheorem = 'classic116Play_minimal';
let evidenceFilter = 'all';
let sourceCache = new Map();
let sourceExpanded = false;

const majorTheoremIds = [
  'classic116Play_minimal',
  'classic_solution_uses_guanYu_yield',
  'continuousClass_card_eq_898',
  'classic_shortest_path_not_unique',
  'concreteWalk_projectsToMirror',
  'classic_solutionGate_guanYuClearsCaoSweep'
];

function setMode(mode) {
  const formal = mode === 'formalization';
  const lab = mode === 'lab';
  document.body.classList.toggle('formalization-mode', formal);
  root.hidden = !formal;
  document.getElementById('classic-workspace').hidden = formal || lab;
  document.getElementById('laboratory').hidden = formal || !lab;
  modeClassic.classList.toggle('active', !formal && !lab);
  modeLab.classList.toggle('active', lab);
  modeFormalization.classList.toggle('active', formal);
  if (formal) {
    const nextUrl = new URL(location.href);
    nextUrl.searchParams.set('mode', 'formalization');
    history.replaceState(history.state, '', nextUrl);
    renderFormalization();
  } else {
    const nextUrl = new URL(location.href);
    if (lab) nextUrl.searchParams.set('mode', 'lab');
    else nextUrl.searchParams.delete('mode');
    history.replaceState(history.state, '', nextUrl);
  }
}

function metricMarkup() {
  return `<section class="formal-stat-strip">${formalizationStats.map(stat => `
    <div class="formal-stat ${stat.accent}">
      <strong>${stat.value}</strong><span>${stat.label}</span><small>${stat.note}</small>
    </div>`).join('')}</section>`;
}

function evidenceBadge(level) {
  const labels = { kernel: '内核定理', checked: '证书检查', conditional: '条件接口' };
  return `<span class="evidence-badge ${level}">${labels[level] || level}</span>`;
}

function stageCard(stage, compact = false) {
  const active = stage.id === selectedStage ? ' active' : '';
  return `<button class="stage-card${active}${compact ? ' compact' : ''}" data-stage="${stage.id}">
    <span class="stage-index">${stage.index}</span>
    <span class="stage-color ${stage.color}"></span>
    <span class="stage-copy"><b>${stage.title}</b><small>${stage.lean}</small></span>
    <code>${stage.symbol}</code>
  </button>`;
}

function theoremCard(record) {
  return `<button class="theorem-card${record.id === selectedTheorem ? ' active' : ''}${record.featured ? ' featured' : ''}" data-theorem="${record.id}">
    <span class="theorem-card-top"><b>${record.title}</b>${evidenceBadge(record.evidence)}</span>
    <code>${record.id}</code>
    <small>${record.category} · ${record.tags.slice(0, 3).join(' · ')}</small>
  </button>`;
}

function stageDetail(stage) {
  const linked = theoremRecords.filter(record => record.file === stage.file || record.id === stage.symbol);
  return `<aside class="stage-detail">
    <div class="section-kicker">SELECTED STAGE · ${stage.index}</div>
    <h3>${stage.title}</h3>
    <p>${stage.description}</p>
    <code class="formula-block">${escapeHtml(stage.formula)}</code>
    <div class="stage-detail-meta"><span>Lean 类型 / API</span><strong>${stage.lean}</strong></div>
    <div class="stage-detail-meta"><span>源文件</span><code>${stage.file}</code></div>
    <div class="stage-output-list">${stage.outputs.map(output => `<span><i>✓</i>${output}</span>`).join('')}</div>
    ${linked.length ? `<div class="stage-linked"><span>相关定理</span>${linked.slice(0, 3).map(record => `<button data-theorem="${record.id}">${record.id}</button>`).join('')}</div>` : ''}
  </aside>`;
}

const theoremGraphPositions = {
  tryMove_preserves_validity: { x: 32, y: 42 },
  valid_goal_caoBelowGuanYu: { x: 268, y: 42 },
  fullSpace_semantic_complete: { x: 504, y: 42 },
  Path_toReachable: { x: 740, y: 42 },
  tryMove_reverse: { x: 32, y: 202 },
  shapePresentation_successorsComplete: { x: 268, y: 202 },
  checkClosedGraph_sound: { x: 504, y: 202 },
  continuousClass_card_eq_898: { x: 740, y: 202 },
  classic_solutionGate_guanYuClearsCaoSweep: { x: 32, y: 362 },
  concreteWalk_projectsToMirror: { x: 268, y: 362 },
  shortest_of_verified_path_and_lower_bound: { x: 504, y: 362 },
  corridorWalk_liftToConcreteWithCost: { x: 740, y: 362 },
  classic_solution_uses_guanYu_yield: { x: 268, y: 522 },
  classic_shortest_path_not_unique: { x: 740, y: 522 },
  classic116Play_minimal: { x: 504, y: 522 }
};

function theoremGraphBoundaryPoint(source, target, fromSource) {
  const width = 190;
  const height = 92;
  const sourceCenter = { x: source.x + width / 2, y: source.y + height / 2 };
  const targetCenter = { x: target.x + width / 2, y: target.y + height / 2 };
  const dx = targetCenter.x - sourceCenter.x;
  const dy = targetCenter.y - sourceCenter.y;
  const scale = Math.min(
    Math.abs(dx) > 0 ? width / 2 / Math.abs(dx) : Number.POSITIVE_INFINITY,
    Math.abs(dy) > 0 ? height / 2 / Math.abs(dy) : Number.POSITIVE_INFINITY
  );
  const point = fromSource ? sourceCenter : targetCenter;
  const direction = fromSource ? 1 : -1;
  return {
    x: point.x + direction * dx * scale,
    y: point.y + direction * dy * scale
  };
}

function theoremGraphPath(edge, recordsById) {
  const source = theoremGraphPositions[edge.from];
  const target = theoremGraphPositions[edge.to];
  if (!source || !target) return '';
  const start = theoremGraphBoundaryPoint(source, target, true);
  const end = theoremGraphBoundaryPoint(source, target, false);
  const bend = Math.max(28, Math.abs(end.x - start.x) * 0.32);
  const control1 = { x: start.x + (end.x >= start.x ? bend : -bend), y: start.y };
  const control2 = { x: end.x - (end.x >= start.x ? bend : -bend), y: end.y };
  const selected = selectedTheorem === edge.from || selectedTheorem === edge.to;
  const title = `${recordsById.get(edge.from)?.title || edge.from} → ${recordsById.get(edge.to)?.title || edge.to}`;
  return `<g class="theorem-graph-edge${selected ? ' selected' : ''}">
    <title>${escapeHtml(title)} · ${escapeHtml(edge.label)}</title>
    <path d="M ${start.x.toFixed(1)} ${start.y.toFixed(1)} C ${control1.x.toFixed(1)} ${control1.y.toFixed(1)}, ${control2.x.toFixed(1)} ${control2.y.toFixed(1)}, ${end.x.toFixed(1)} ${end.y.toFixed(1)}"></path>
  </g>`;
}

function theoremDependencyGraph() {
  const recordsById = new Map(theoremRecords.map(record => [record.id, record]));
  const selected = theoremById(selectedTheorem);
  const incoming = theoremDependencyEdges.filter(edge => edge.to === selected.id);
  const outgoing = theoremDependencyEdges.filter(edge => edge.from === selected.id);
  const graphNodes = theoremRecords.map(record => {
    const position = theoremGraphPositions[record.id];
    const active = record.id === selectedTheorem ? ' active' : '';
    return `<button class="theorem-graph-node ${record.evidence}${active}" data-graph-theorem="${record.id}" style="left:${position.x}px;top:${position.y}px" aria-label="选择定理 ${escapeHtml(record.title)}">
      <span class="theorem-graph-node-top"><i>${record.category}</i>${evidenceBadge(record.evidence)}</span>
      <strong>${escapeHtml(record.title)}</strong>
      <code>${record.id}</code>
    </button>`;
  }).join('');
  const dependencyList = (edges, direction) => edges.length
    ? edges.map(edge => {
      const id = direction === 'in' ? edge.from : edge.to;
      return `<button data-theorem="${id}"><code>${id}</code><small>${edge.label}</small></button>`;
    }).join('')
    : '<span class="dependency-empty">暂无直接连接</span>';

  return `<section class="formal-section theorem-dependency-section" data-formal-section="dependency-graph">
    <header class="formal-section-heading">
      <div><span class="section-kicker">THEOREM-LEVEL DEPENDENCY GRAPH</span><h2>定理之间如何相互依赖</h2><p class="section-subtitle">节点是定理，箭头表示主要证明依赖和语义桥接。点击节点，右侧会显示它需要什么、又支撑了什么。</p></div>
      <div class="theorem-graph-legend"><span><i class="graph-legend-dot kernel"></i>内核定理</span><span><i class="graph-legend-dot checked"></i>证书检查</span><span><i class="graph-legend-dot conditional"></i>条件接口</span></div>
    </header>
    <div class="theorem-dependency-layout">
      <div class="theorem-dependency-viewport">
        <div class="theorem-dependency-map">
          <div class="theorem-graph-lane lane-foundation">基础语义与几何</div>
          <div class="theorem-graph-lane lane-bridge">可达性、商与证书</div>
          <div class="theorem-graph-lane lane-result">大结论</div>
          <svg class="theorem-graph-svg" viewBox="0 0 1080 680" role="img" aria-label="${theoremRecords.length} 条 Lean 定理的有向依赖图">
            <defs><marker id="theorem-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z"></path></marker></defs>
            ${theoremDependencyEdges.map(edge => theoremGraphPath(edge, recordsById)).join('')}
          </svg>
          ${graphNodes}
        </div>
      </div>
      <aside class="theorem-dependency-detail">
        <div class="theorem-dependency-summary">
          <span class="section-kicker">SELECTED THEOREM</span>
          <h3>${escapeHtml(selected.title)}</h3>
          ${evidenceBadge(selected.evidence)}
          <code class="theorem-dependency-id">${selected.id}</code>
          <p>${selected.plain}</p>
        </div>
        <div class="dependency-detail-block"><b>它依赖</b><div class="dependency-link-list">${dependencyList(incoming, 'in')}</div></div>
        <div class="dependency-detail-block"><b>它支撑</b><div class="dependency-link-list">${dependencyList(outgoing, 'out')}</div></div>
        <button class="primary-action theorem-graph-source" data-open-source="${selected.id}">打开源码与 statement <span>→</span></button>
      </aside>
    </div>
    <footer class="theorem-dependency-note"><span><i></i>这是面向汇报的主要证明链摘要，不替代 Lean elaborator 的完整 declaration 依赖图；原始 statement 和证明项以源码阅读器为准。</span><strong>${theoremRecords.length} 个定理 · ${theoremDependencyEdges.length} 条主要依赖</strong></footer>
  </section>`;
}

function modelFormalizationSection() {
  return `<section class="formal-section model-formalization-section" data-formal-section="model-rules">
    <header class="formal-section-heading">
      <div><span class="section-kicker">RULES → LEAN DEFINITIONS → FINITE STATE SYSTEM</span><h2>规则的形式化</h2><p class="section-subtitle">先把游戏规则写成可计算定义，再让证明对象复用这些定义。</p></div>
      <span class="model-source-label"><i></i>${modelFormalization.source}</span>
    </header>
    <div class="model-formalization-body">
      <div class="model-formalization-prose">${modelFormalization.paragraphs.map(paragraph => `<p>${paragraph}</p>`).join('')}</div>
      <div class="model-formalization-anchors" aria-label="规则形式化对应的 Lean 对象">${modelFormalization.anchors.map(anchor => `
        <div class="model-anchor">
          <span class="model-anchor-index">${anchor.index}</span>
          <div><b>${anchor.title}</b><code>${anchor.lean}</code><p>${anchor.detail}</p></div>
        </div>`).join('')}</div>
    </div>
    <footer class="model-formalization-footer"><span><i class="status-dot"></i>模型层已接入证明链</span><strong>Model → Transition → Quotient → Search</strong></footer>
  </section>`;
}

function researchContinuationSection() {
  return `<section class="formal-section research-continuation-section" data-formal-section="research-after-shortest">
    <header class="formal-section-heading">
      <div><span class="section-kicker">AFTER SHORTEST PATH</span><h2>116 步之后，项目继续研究什么</h2><p class="section-subtitle">最短性给出一个闭合结论，但它只回答“最少需要多少步”。状态空间里还有商结构、分量、局部几何和不同最短解之间的关系。</p></div>
      <button class="text-action" data-formal-view="chain">查看依赖图 ↗</button>
    </header>
    <div class="research-continuation-grid">${researchContinuations.map((item, index) => `
      <article class="research-continuation-item">
        <span>${String(index + 1).padStart(2, '0')}</span>
        <div><h3>${item.title}</h3><code>${item.lean}</code><p>${item.detail}</p></div>
      </article>`).join('')}</div>
  </section>`;
}

function overviewView() {
  return `${metricMarkup()}
    <section class="formal-summary-banner">
      <div class="summary-seal">∴</div>
      <div><span class="section-kicker">CURRENT FORMALIZATION RESULT</span>
        <h2>116 步最短性已闭合，研究没有停在终点</h2>
        <p><code>classic116Play_minimal</code> 把一条 116 步通关路径和完整商图下界接在一起。随后，项目继续研究同形商、镜像商、898 个 DFS 分量、关羽让路和最短路环岛；这些结论的证据类型并不相同，页面会逐项标明。</p>
      </div>
      <button class="inline-action" data-formal-view="theorems">查看大定理 <span>→</span></button>
    </section>
    ${modelFormalizationSection()}
    ${researchContinuationSection()}
    <section class="formal-section" data-formal-section="overview">
      <header class="formal-section-heading"><div><span class="section-kicker">MATHEMATICAL MODEL → KERNEL OBJECTS</span><h2>形式化主链</h2></div><button class="text-action" data-formal-view="chain">展开依赖图 ↗</button></header>
      <div class="stage-rail">${formalStages.map(stage => stageCard(stage)).join('')}</div>
      <div class="stage-detail-wrap">${stageDetail(formalStages.find(stage => stage.id === selectedStage) || formalStages[0])}</div>
    </section>
    <section class="formal-two-column">
      <section class="formal-section theorem-highlight">
        <header class="formal-section-heading"><div><span class="section-kicker">THEOREM OF THE PROJECT</span><h2>值得在汇报中讲清楚的定理</h2></div><button class="text-action" data-formal-view="theorems">全部定理</button></header>
        <div class="feature-theorem-grid">${theoremRecords.filter(record => record.featured).slice(0, 4).map(theoremCard).join('')}</div>
      </section>
      <section class="formal-section boundary-panel">
        <header class="formal-section-heading"><div><span class="section-kicker">EVIDENCE BOUNDARY</span><h2>当前结果如何理解</h2></div></header>
        <div class="boundary-row"><i class="boundary-icon kernel">K</i><div><b>内核定理</b><span>定义、归纳证明、等价与最短性定理由 Lean kernel 检查。</span></div></div>
        <div class="boundary-row"><i class="boundary-icon checked">C</i><div><b>有限证书</b><span><code>native_decide</code> / checker 验证可计算事实，再由 soundness 定理解释。</span></div></div>
        <div class="boundary-row"><i class="boundary-icon conditional">?</i><div><b>条件接口</b><span><code>continuousClass_card_eq_898</code> 保留 <code>Lawful</code> 前提，未把待聚合的最终证书隐藏掉。</span></div></div>
        <div class="boundary-row"><i class="boundary-icon visual">V</i><div><b>可视化</b><span>Three.js 坐标、动画和布局帮助理解结构，但不是证明数据。</span></div></div>
      </section>
    </section>`;
}

function chainView() {
  const chain = formalStages.slice(0, 6);
  return `${metricMarkup()}
    <section class="formal-summary-banner chain-banner">
      <div class="summary-seal">→</div>
      <div><span class="section-kicker">DEPENDENCY READING</span><h2>一条路径怎样变成一个 Lean 定理？</h2><p>从状态定义开始，先得到合法动作，再构造路径和可达性。商空间需要路径提升，有限搜索则要经过 checker 和 soundness 定理。116 步最短性闭合后，依赖图还会继续分叉到关羽让路、连续等价类和最短路拓扑。</p></div>
    </section>
    <section class="formal-section" data-formal-section="proof-chain">
      <header class="formal-section-heading"><div><span class="section-kicker">PROOF PIPELINE</span><h2>从棋盘到全局结论</h2></div><span class="legend-note"><i class="dot red"></i>语义 <i class="dot teal"></i>商与图 <i class="dot gold"></i>证书</span></header>
      <div class="proof-pipeline">${chain.map((stage, index) => `
        <div class="pipeline-node ${stage.color}" data-stage="${stage.id}">
          <span>${stage.index}</span><b>${stage.title}</b><code>${stage.symbol}</code>
          <p>${stage.description}</p>
          <button data-stage="${stage.id}">查看该层</button>
        </div>${index < chain.length - 1 ? '<i class="pipeline-arrow">→</i>' : ''}`).join('')}</div>
    </section>
    ${theoremDependencyGraph()}
    <section class="formal-two-column chain-detail-grid" data-formal-section="object-dependency">
      <section class="formal-section">
        <header class="formal-section-heading"><div><span class="section-kicker">TYPE-LEVEL DEPENDENCY GRAPH</span><h2>类型与证明对象如何相互依赖</h2></div></header>
        <div class="dependency-graph" role="img" aria-label="Lean 形式化对象依赖关系">
          <div class="dependency-row"><span class="dependency-label">状态语义</span><div class="dep-node red">State<small>positions : Array Pos</small></div><i>→</i><div class="dep-node red">ValidState<small>valid s = true</small></div><i>→</i><div class="dep-node teal">tryMove<small>Option State</small></div></div>
          <div class="dependency-row"><span class="dependency-label">证明对象</span><div class="dep-node gold">Step<small>∃ action, ...</small></div><i>→</i><div class="dep-node gold">Path<small>cons / nil</small></div><i>→</i><div class="dep-node teal">Reachable<small>∃ Task.Walk</small></div></div>
          <div class="dependency-row"><span class="dependency-label">商与图</span><div class="dep-node purple">ShapeState<small>same-shape quotient</small></div><i>→</i><div class="dep-node purple">MirrorShapeState<small>horizontal quotient</small></div><i>→</i><div class="dep-node blue">SimpleGraph<small>connected component</small></div></div>
          <div class="dependency-row"><span class="dependency-label">证书结论</span><div class="dep-node red wide">VerifiedPath + LowerBoundCertificate<small>upper bound + lower bound</small></div><i>→</i><div class="dep-node red wide">IsShortestSolution<small>global minimality</small></div></div>
        </div>
      </section>
      <aside class="formal-section chain-aside">
        <header class="formal-section-heading"><div><span class="section-kicker">READING GUIDE</span><h2>读证明链时抓住三点</h2></div></header>
        <ol class="reading-list">
          <li><b>先定义对象</b><span>先看 <code>valid</code>、<code>tryMove</code> 和 <code>goal</code>，再看 <code>Step</code>、<code>Path</code> 与 <code>Reachable</code>。</span></li>
          <li><b>计算还要有语义解释</b><span>数组、HashMap 和 BFS 只负责运行；<code>check..._sound</code> 把结果写成命题。</span></li>
          <li><b>商图要能回到原图</b><span>合并节点还不够。<code>liftStepFrom</code> 和等长 <code>mapWalk</code> 负责把路径带回具体棋盘。</span></li>
        </ol>
        <code class="large-equation">classic116Play_minimal<br>:= upperBound(116) + lowerBound(116)</code>
      </aside>
    </section>`;
}

function theoremDetail(record) {
  return `<article class="theorem-detail">
    <header class="theorem-detail-header"><div><span class="section-kicker">${record.category.toUpperCase()} · ${record.id}</span><h2>${record.title}</h2></div>${evidenceBadge(record.evidence)}</header>
    <code class="theorem-statement">${escapeHtml(record.statement)}</code>
    <p class="theorem-plain">${record.plain}</p>
    <div class="theorem-detail-grid">
      <section><span class="detail-label">证明链中的位置</span><div class="chain-chips">${record.chain.map((item, index) => `<span><b>${index + 1}</b><code>${item}</code></span>`).join('')}</div></section>
      <section><span class="detail-label">相互依赖 / 后续接口</span><div class="related-list">${record.related.map(item => `<button data-theorem="${theoremRecords.find(candidate => candidate.id === item) ? item : ''}">${item}</button>`).join('')}</div></section>
    </div>
    <footer class="theorem-detail-footer"><span><i class="source-dot"></i>${record.file}</span><button class="primary-action" data-open-source="${record.id}">打开原文与解释 <span>→</span></button></footer>
  </article>`;
}

function majorTheoremsSection() {
  const record = theoremById(selectedTheorem);
  const majorRecords = majorTheoremIds.map(theoremById);
  return `<section class="formal-section major-theorems-section" data-formal-section="theorems">
    <header class="formal-section-heading">
      <div><span class="section-kicker">MAJOR RESULTS</span><h2>重点定理</h2><p class="section-subtitle">选择一条结论，查看正式陈述、主要依赖和证据类型。</p></div>
    </header>
    <div class="major-theorems-layout">
      <aside class="major-theorem-list">${majorRecords.map(recordItem => `<button class="${recordItem.id === selectedTheorem ? 'active' : ''}" data-major-theorem="${recordItem.id}">
        <span>${evidenceBadge(recordItem.evidence)}</span><b>${recordItem.title}</b><code>${recordItem.id}</code>
      </button>`).join('')}</aside>
      <article class="major-theorem-detail">
        <div class="major-theorem-heading"><div><span class="section-kicker">${record.category}</span><h3>${record.title}</h3></div>${evidenceBadge(record.evidence)}</div>
        <code class="major-theorem-statement">${escapeHtml(record.statement)}</code>
        <p>${record.plain}</p>
        <div class="major-theorem-chain"><b>主要依赖</b><span>${record.chain.map(item => `<code>${item}</code>`).join('<i>→</i>')}</span></div>
        <footer><span>${record.file}</span><button class="primary-action" data-open-source="${record.id}">查看 Lean 源码 <span>→</span></button></footer>
      </article>
    </div>
  </section>`;
}

function evidenceBoundarySection() {
  return `<section class="formal-section compact-evidence-section" data-formal-section="evidence">
    <header class="formal-section-heading"><div><span class="section-kicker">EVIDENCE BOUNDARY</span><h2>结论的证据边界</h2></div></header>
    <div class="compact-evidence-grid">
      <div><i class="boundary-icon kernel">K</i><b>内核定理</b><p>定义、归纳证明、等价和最短性由 Lean kernel 检查。</p></div>
      <div><i class="boundary-icon checked">C</i><b>有限证书</b><p>checker 或 <code>native_decide</code> 先验证数据，再由 soundness 定理解释。</p></div>
      <div><i class="boundary-icon conditional">?</i><b>条件接口</b><p><code>continuousClass_card_eq_898</code> 仍保留 <code>Lawful</code> 前提，898 尚未作为无条件定理编译闭合。</p></div>
    </div>
  </section>`;
}

function compactSourceSection() {
  if (!sourceExpanded) return '';
  const record = theoremById(selectedTheorem);
  return `<section class="formal-section compact-source-section" data-formal-section="source">
    <header class="formal-section-heading">
      <div><span class="section-kicker">LEAN SOURCE</span><h2>${record.title}</h2><p class="section-subtitle">${record.file}</p></div>
      <button class="text-action" data-close-source>收起源码</button>
    </header>
    <div class="source-explanation compact-source-explanation">
      <div><b>定理说明</b><p>${record.plain}</p></div>
      <div><b>正式陈述</b><span><code>${escapeHtml(record.statement)}</code></span></div>
    </div>
    <div id="formal-source-code" class="formal-source-code"><div class="source-loading"><i></i><span>正在读取 ${record.file}</span></div></div>
  </section>`;
}

function theoremView() {
  const filtered = evidenceFilter === 'all' ? theoremRecords : theoremRecords.filter(record => record.evidence === evidenceFilter);
  const record = theoremById(selectedTheorem);
  return `${metricMarkup()}
    <section class="formal-section theorem-atlas" data-formal-section="theorems">
      <header class="formal-section-heading"><div><span class="section-kicker">THEOREM ATLAS · ${filtered.length} RESULTS</span><h2>定理图谱</h2><p class="section-subtitle">这里列出项目中的 ${theoremRecords.length} 条定理。点击一条，可以同时查看 statement、证明链、源码位置和相关结果。</p></div></header>
      <div class="evidence-filter">${evidenceLevels.map(level => `<button class="${evidenceFilter === level.id ? 'active' : ''}" data-evidence="${level.id}">${level.label}<small>${level.description}</small></button>`).join('')}</div>
      <div class="theorem-atlas-layout"><aside class="theorem-list">${filtered.map(theoremCard).join('')}</aside><div>${theoremDetail(record)}</div></div>
    </section>`;
}

function sourceView() {
  const record = theoremById(selectedTheorem);
  const fileMeta = sourceFiles.find(file => file.path === record.file) || sourceFiles[0];
  return `${metricMarkup()}
    <section class="formal-section source-workbench" data-formal-section="source">
      <header class="formal-section-heading"><div><span class="section-kicker">SOURCE EXPLORER · EXACT LEAN FILES</span><h2>Lean 源码阅读器</h2><p class="section-subtitle">窗口会围绕当前定理显示，并保留文件中的真实行号；源码由同源只读接口提供。</p></div><span class="source-route-status"><i></i>/api/source · read-only</span></header>
      <div class="source-layout"><aside class="source-file-list"><header><b>项目模块</b><small>${sourceFiles.length} files</small></header>${sourceFiles.map(file => `<button class="${file.path === fileMeta.path ? 'active' : ''}" data-source-file="${file.path}"><span>${file.layer}</span><b>${file.path.split('/').at(-1)}</b><small>${file.summary}</small></button>`).join('')}</aside><section class="source-panel"><header class="source-panel-header"><div><span class="section-kicker">SELECTED DECLARATION</span><h3>${record.id}</h3><code>${record.file}</code></div><button class="text-action" data-formal-view="theorems">回到定理图谱 ↗</button></header><div class="source-explanation"><div><b>这段代码在做什么</b><p>${record.plain}</p></div><div><b>Lean 关注点</b><span><code>${record.statement}</code></span><span>依赖：${record.chain.slice(0, 3).join(' → ')}</span></div></div><div id="formal-source-code" class="formal-source-code"><div class="source-loading"><i></i><span>正在读取 ${record.file}</span></div></div></section></div>
    </section>`;
}

function kernelView() {
  return `${metricMarkup()}
    <section class="formal-summary-banner kernel-banner" data-formal-section="kernel">
      <div class="summary-seal">λ</div>
      <div><span class="section-kicker">LEAN KERNEL LENS</span><h2>前端展示对象，内核检查证明项</h2><p>这里把项目用到的 Lean 组件放在一起看：数据类型描述棋盘，归纳类型描述路径，checker 重放有限数据，定理把结果接回数学语义。</p></div>
    </section>
    <section class="formal-section">
      <header class="formal-section-heading"><div><span class="section-kicker">LEAN 4 COMPONENTS</span><h2>项目使用到的核心组件</h2></div></header>
      <div class="kernel-component-grid">${kernelComponents.map((component, index) => `<article class="kernel-component"><span class="component-index">0${index + 1}</span><span class="component-kind">${component.name}</span><h3>${component.symbol}</h3><p>${component.meaning}</p><code>${component.example}</code></article>`).join('')}</div>
    </section>
    <section class="formal-two-column">
      <section class="formal-section kernel-code-card"><header class="formal-section-heading"><div><span class="section-kicker">PROOF TERM SHAPE</span><h2>路径为什么是证明</h2></div><button class="text-action" data-open-source="Path_toReachable">看原文 ↗</button></header><pre><code>inductive Path : State → State → Type where
  | nil (s : State) : Path s s
  | cons (action : Action)
      (step : tryMove s action.piece action.direction = some u)
      (tail : Path u t) : Path s t

theorem Path.toReachable (path : Path s t) :
    Reachable s t := by
  induction path with
  | nil => exact .refl _
  | cons action step _ ih =>
      exact .tail ⟨action, step⟩ ih</code></pre></section>
      <section class="formal-section kernel-code-card"><header class="formal-section-heading"><div><span class="section-kicker">SEMANTIC BOUNDARY</span><h2>执行层如何回到语义层</h2></div><button class="text-action" data-open-source="checkClosedGraph_sound">看证书 ↗</button></header><pre><code>checkClosedGraph spec graph = true
  → ClosedUnderMoves spec graph
  → reachable_mem
  → every reachable state is listed

VerifiedPath actions
  + LowerBoundCertificate actions.length
  → IsShortestSolution actions</code></pre></section>
    </section>
    <section class="formal-section kernel-boundary-table"><header class="formal-section-heading"><div><span class="section-kicker">WHAT IS PROVED?</span><h2>结论与证据边界</h2></div></header><div class="boundary-table"><div class="boundary-table-head"><span>对象</span><span>Lean 责任</span><span>当前状态</span></div>
      <div><span><code>tryMove</code> / <code>Step</code></span><span>合法动作与保持合法性</span><strong class="state-done">已闭合</strong></div>
      <div><span><code>Reachable</code> / <code>Reversible</code></span><span>路径、逆元、连通分量</span><strong class="state-done">已闭合</strong></div>
      <div><span><code>classic116Play_minimal</code></span><span>完整图下界 + 116 步见证</span><strong class="state-done">大定理已闭合</strong></div>
      <div><span><code>Fintype.card ContinuousClass = 898</code></span><span>有限 DFS 分割到语义商的基数桥</span><strong class="state-open">Lawful 前提仍显式</strong></div>
      <div><span>Three.js / layout.json</span><span>坐标、动画、交互</span><strong class="state-visual">展示层</strong></div>
    </div></section>`;
}

function withoutMetrics(markup) {
  const prefix = metricMarkup();
  return markup.startsWith(prefix) ? markup.slice(prefix.length) : markup;
}

function dashboardView() {
  return `${metricMarkup()}
    <section class="formal-summary-banner" data-formal-section="overview">
      <div class="summary-seal">∴</div>
      <div><span class="section-kicker">PROJECT SUMMARY</span>
        <h2>当前形式化结果</h2>
        <p><code>classic116Play_minimal</code> 已闭合经典华容道 116 步的全局最短性。项目还证明了关羽让路的必然性，并继续研究商空间、全空间分量和最短解之间的结构。898 个连续分量目前是带 <code>Lawful</code> 前提的条件结论。</p>
      </div>
      <span class="summary-status">主定理已闭合 · 898 保留前提</span>
    </section>
    ${modelFormalizationSection()}
    ${researchContinuationSection()}
    ${theoremDependencyGraph()}
    ${majorTheoremsSection()}
    ${evidenceBoundarySection()}
    ${compactSourceSection()}`;
}

function renderFormalization() {
  nav.querySelectorAll('[data-formal-view]').forEach(button => button.classList.toggle('active', button.dataset.formalView === currentView));
  content.innerHTML = dashboardView();
  bindContentEvents();
  loadSource(theoremById(selectedTheorem));
}

function navigateFormalSection(view) {
  currentView = view;
  if (view === 'source') sourceExpanded = true;
  renderFormalization();
  requestAnimationFrame(() => {
    const targets = {
      overview: 'overview',
      model: 'model-rules',
      chain: 'dependency-graph',
      theorems: 'theorems',
      source: 'source',
      kernel: 'evidence'
    };
    const target = targets[view] || 'overview';
    document.querySelector(`[data-formal-section="${target}"]`)?.scrollIntoView({ behavior: 'smooth', block: 'start' });
  });
}

function selectTheorem(id) {
  if (!id || !theoremRecords.some(record => record.id === id)) return;
  selectedTheorem = id;
  renderFormalization();
}

function selectStage(id) {
  selectedStage = id;
  renderFormalization();
}

function bindContentEvents() {
  content.querySelectorAll('[data-stage]').forEach(node => node.addEventListener('click', () => selectStage(node.dataset.stage)));
  content.querySelectorAll('[data-theorem]').forEach(node => node.addEventListener('click', () => {
    if (node.dataset.theorem) {
      selectedTheorem = node.dataset.theorem;
      navigateFormalSection('theorems');
    }
  }));
  content.querySelectorAll('[data-graph-theorem]').forEach(node => node.addEventListener('click', () => {
    selectTheorem(node.dataset.graphTheorem);
  }));
  content.querySelectorAll('[data-major-theorem]').forEach(node => node.addEventListener('click', () => {
    selectedTheorem = node.dataset.majorTheorem;
    renderFormalization();
    requestAnimationFrame(() => document.querySelector('[data-formal-section="theorems"]')?.scrollIntoView({ block: 'start' }));
  }));
  content.querySelectorAll('[data-formal-view]').forEach(node => node.addEventListener('click', () => {
    navigateFormalSection(node.dataset.formalView);
  }));
  content.querySelectorAll('[data-evidence]').forEach(node => node.addEventListener('click', () => {
    evidenceFilter = node.dataset.evidence;
    renderFormalization();
  }));
  content.querySelectorAll('[data-open-source]').forEach(node => node.addEventListener('click', () => {
    const id = node.dataset.openSource;
    if (id && theoremRecords.some(record => record.id === id)) selectedTheorem = id;
    navigateFormalSection('source');
  }));
  content.querySelectorAll('[data-close-source]').forEach(node => node.addEventListener('click', () => {
    sourceExpanded = false;
    currentView = 'theorems';
    renderFormalization();
    requestAnimationFrame(() => document.querySelector('[data-formal-section="theorems"]')?.scrollIntoView({ block: 'start' }));
  }));
  content.querySelectorAll('[data-source-file]').forEach(node => node.addEventListener('click', () => {
    const file = sourceFiles.find(item => item.path === node.dataset.sourceFile);
    const matching = theoremRecords.find(record => record.file === file?.path);
    if (matching) selectedTheorem = matching.id;
    navigateFormalSection('source');
  }));
}

function extractSourceWindow(contentText, anchor, before = 8, after = 22) {
  const lines = contentText.split(/\r?\n/);
  let index = lines.findIndex(line => line.includes(anchor));
  if (index < 0) index = 0;
  const start = Math.max(0, index - before);
  const end = Math.min(lines.length, index + after);
  return { lines: lines.slice(start, end), start: start + 1 };
}

function renderSourceCode(sourceText, record) {
  const window = extractSourceWindow(sourceText, record.anchor, 7, record.sourceWindow || 22);
  const lineMarkup = window.lines.map((line, index) => {
    const lineNumber = window.start + index;
    const active = line.includes(record.anchor) || (lineNumber === window.start && record.id === 'classic116Play_minimal') ? ' active' : '';
    return `<span class="source-line${active}"><b>${String(lineNumber).padStart(4, '0')}</b><code>${escapeHtml(line) || ' '}</code></span>`;
  }).join('');
  document.getElementById('formal-source-code').innerHTML = `<div class="source-code-toolbar"><span><i></i>原始仓库源码 · ${window.start}–${window.start + window.lines.length - 1}</span><button id="formal-copy-source">复制片段</button></div><pre>${lineMarkup}</pre>`;
  document.getElementById('formal-copy-source').addEventListener('click', async () => {
    await navigator.clipboard.writeText(window.lines.join('\n'));
    document.getElementById('formal-copy-source').textContent = '已复制';
    setTimeout(() => { const button = document.getElementById('formal-copy-source'); if (button) button.textContent = '复制片段'; }, 1100);
  });
}

async function loadSource(record) {
  const target = document.getElementById('formal-source-code');
  if (!target) return;
  if (sourceCache.has(record.file)) {
    renderSourceCode(sourceCache.get(record.file), record);
    return;
  }
  try {
    const response = await fetch(`/api/source?path=${encodeURIComponent(record.file)}`);
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    const sourceText = await response.text();
    sourceCache.set(record.file, sourceText);
    renderSourceCode(sourceText, record);
  } catch (error) {
    renderSourceCode(record.fallback || `// ${record.file}\n// source unavailable: ${error.message}`, record);
    const status = document.querySelector('.source-route-status');
    if (status) status.innerHTML = '<i class="warning"></i>fallback snippet';
  }
}

nav.querySelectorAll('[data-formal-view]').forEach(button => button.addEventListener('click', () => {
  navigateFormalSection(button.dataset.formalView);
}));

modeFormalization.addEventListener('click', () => setMode('formalization'));
modeClassic.addEventListener('click', () => setMode('classic'));
modeLab.addEventListener('click', () => setMode('lab'));
document.getElementById('formal-copy-link').addEventListener('click', async () => {
  const url = new URL(location.href);
  url.searchParams.set('mode', 'formalization');
  url.searchParams.set('view', currentView);
  await navigator.clipboard.writeText(url.toString());
  const button = document.getElementById('formal-copy-link');
  button.textContent = '✓';
  setTimeout(() => { button.textContent = '⧉'; }, 1000);
});

const requestedMode = new URLSearchParams(location.search).get('mode');
const requestedView = new URLSearchParams(location.search).get('view');
if (['overview', 'model', 'chain', 'theorems', 'source', 'kernel'].includes(requestedView)) currentView = requestedView;
if (requestedMode === 'formalization') {
  if (requestedView === 'source') sourceExpanded = true;
  setMode('formalization');
  if (requestedView) requestAnimationFrame(() => {
    const targets = { overview: 'overview', model: 'model-rules', chain: 'dependency-graph', theorems: 'theorems', source: 'source', kernel: 'evidence' };
    const target = targets[requestedView] || 'overview';
    document.querySelector(`[data-formal-section="${target}"]`)?.scrollIntoView({ block: 'start' });
  });
}
