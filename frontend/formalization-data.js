export const formalizationStats = [
  { value: '116', label: '经典最短步数', note: '有限图证书已检查', accent: 'red' },
  { value: '25,955', label: '经典同形商状态', note: '经典初态所在分量', accent: 'teal' },
  { value: '83,896', label: 'Lean 导出的有向边', note: '逐条通过 QStep 检查', accent: 'gold' },
  { value: '65,880', label: '全形状候选布局', note: '4,392 × C(6,4)', accent: 'ink' },
  { value: '898', label: 'DFS 连续分量', note: '语义桥仍需 Lawful 实例', accent: 'amber' }
];

export const formalStages = [
  {
    id: 'model',
    index: '01',
    title: '数学模型',
    lean: 'Piece · Shape · Pos · State',
    file: 'Huarongdao/Model.lean',
    symbol: 'valid / ValidState',
    color: 'red',
    description: '把棋盘写成可计算的对象：每个木块有矩形形状和左上角坐标，合法性检查越界与重叠。',
    formula: 'ValidState s := valid s = true',
    outputs: ['合法状态', '目标谓词 goal', '棋盘坐标']
  },
  {
    id: 'transition',
    index: '02',
    title: '合法转换',
    lean: 'tryMove · Step',
    file: 'Huarongdao/Transition.lean',
    symbol: 'tryMove_preserves_validity',
    color: 'teal',
    description: '动作先生成候选位置，再检查新棋盘是否合法。`Step` 记录动作以及它确实把起点变成终点的等式。',
    formula: 'Step s t := ∃ a, tryMove s a = some t',
    outputs: ['一步证明', '后继状态', '合法动作枚举']
  },
  {
    id: 'path',
    index: '03',
    title: '路径见证',
    lean: 'Path · Walk · CertifiedPlay',
    file: 'Huarongdao/Paths.lean',
    symbol: 'Path.cons / Path.toReachable',
    color: 'gold',
    description: '路径是带执行等式的归纳数据。每个 `cons` 都保存一个动作、一步执行证明和后续路径。',
    formula: 'Path.cons action executed tail',
    outputs: ['有限路径', '动作列表', '可达性见证']
  },
  {
    id: 'reachability',
    index: '04',
    title: '可达性',
    lean: 'Reachable · Reversible',
    file: 'Huarongdao/StateSpaceConnectivity.lean',
    symbol: 'reachable_symm / componentOf',
    color: 'blue',
    description: '用有限合法路径定义可达关系。移动可逆，所以可达关系具有对称性，并能对应到 Mathlib 的连通分量。',
    formula: 'Reachable := ∃ walk : Task.Walk s t',
    outputs: ['连通分量', 'Mathlib SimpleGraph', '不变量']
  },
  {
    id: 'quotient',
    index: '05',
    title: '商空间提升',
    lean: 'concrete → shape → mirror',
    file: 'Huarongdao/StateSpaceKernel.lean',
    symbol: 'concreteWalk_projectsToMirror',
    color: 'purple',
    description: '先忘记同形棋子的编号，再合并水平镜像代表。路径可以投影，也可以提升回具体棋盘，原子步数保持不变。',
    formula: 'concreteToMirror.mapWalk walk',
    outputs: ['25,955 同形节点', '13,011 镜像节点', '等长提升']
  },
  {
    id: 'certificate',
    index: '06',
    title: '有限证书',
    lean: 'BFS · checkClosedGraph · LowerBoundCertificate',
    file: 'Huarongdao/Generic/Certificates.lean',
    symbol: 'shortest_of_verified_path_and_lower_bound',
    color: 'red',
    description: '搜索器只生成候选数据。checker 重新播放动作并检查闭包；上界来自已验证路径，下界来自 rank 的增长限制。',
    formula: 'verified path + lower bound ⇒ IsShortestSolution',
    outputs: ['116 步最短性', '不可达证书接口', '闭包 soundness']
  },
  {
    id: 'geometry',
    index: '07',
    title: '离散几何',
    lean: 'SolutionGate · GuanYuYield',
    file: 'Huarongdao/GuanYuYield.lean',
    symbol: 'classic_solution_uses_guanYu_yield_of_finite_certificate',
    color: 'amber',
    description: '在状态图上定义门区、曹操下降扫掠区和关羽让路事件。定理说明所有解都要经过这类让路步骤。',
    formula: '∀ solution, solution.path.UsesTransition GuanYuYield',
    outputs: ['门区必经性', '几何位置命题', '操作机制解释']
  },
  {
    id: 'fullspace',
    index: '08',
    title: '全形状空间',
    lean: '65,880 → 898 → ContinuousClass',
    file: 'Huarongdao/ClassicContinuousClassCard.lean',
    symbol: 'continuousClass_card_eq_898',
    color: 'teal',
    description: '枚举所有合法同形布局，再用 DFS 分割得到 898 个分量。语义桥已经写好，但最终仍需要一个 `Lawful` 实例。',
    formula: 'lawful + roots.size = 898 ⇒ Fintype.card ContinuousClass = 898',
    outputs: ['全空间枚举', 'DFS 分量证书', '连续等价类基数']
  }
];

export const theoremRecords = [
  {
    id: 'classic116Play_minimal',
    title: '经典 116 步全局最短性',
    category: '大定理',
    evidence: 'kernel',
    featured: true,
    file: 'Huarongdao/ClassicCertificate.lean',
    anchor: 'theorem classic116Play_minimal',
    tags: ['最短性', '有限证书', '经典任务'],
    statement: 'classic116Play.Minimal',
    plain: '这组 116 步动作可以到达目标；完整经典商图又排除了更短的通关路径。两部分合在一起，得到全局最短性。',
    chain: ['classic116_length', 'classic116_runs', 'classicQuotientLowerBound_checked', 'classic116Play_minimal'],
    related: ['classicTask_solution_lower_bound', 'shortest_of_verified_path_and_lower_bound'],
    sourceWindow: 18,
    fallback: `theorem classic116Play_minimal :\n    classic116Play.Minimal := by\n  intro other\n  rw [classic116Play_length]\n  exact\n    classicQuotientLowerBoundCertificate.play_lower_bound other.length`
  },
  {
    id: 'tryMove_preserves_validity',
    title: '成功移动保持合法性',
    category: '基础语义',
    evidence: 'kernel',
    file: 'Huarongdao/Transition.lean',
    anchor: 'theorem tryMove_preserves_validity',
    tags: ['validity', 'tryMove'],
    statement: 'tryMove s p d = some t → ValidState t',
    plain: '`tryMove` 只有在候选棋盘通过 `valid` 检查后才返回 `some`。因此，成功移动的结果天然带有合法状态证明。',
    chain: ['valid', 'tryMove', 'tryMove_preserves_validity'],
    related: ['step_preserves_validity', 'reachable_preserves_validity'],
    sourceWindow: 24,
    fallback: `theorem tryMove_preserves_validity\n    {s t : State} {p : Piece} {d : Direction}\n    (h : tryMove s p d = some t) : ValidState t := by\n  cases hm : moveUnchecked s p d with\n  | none => simp [tryMove, hm] at h\n  | some next =>\n      by_cases hv : valid next = true\n      · simp [tryMove, hm, hv] at h\n        cases h\n        exact hv`
  },
  {
    id: 'Path_toReachable',
    title: '证明项推出可达性',
    category: '路径与逻辑',
    evidence: 'kernel',
    file: 'Huarongdao/Paths.lean',
    anchor: 'theorem toReachable',
    tags: ['Path', 'Reachable', 'induction'],
    statement: 'Path s t → Reachable s t',
    plain: '对路径归纳。空路径对应 `Reachable.refl`；非空路径把当前的 `tryMove` 等式包装成一步，再接上尾路径。',
    chain: ['Path.nil', 'Path.cons', 'Reachable.refl', 'Reachable.tail'],
    related: ['Path.runMoves_eq', 'reachable_preserves_validity'],
    sourceWindow: 18,
    fallback: `theorem toReachable (path : Path s t) : Reachable s t := by\n  induction path with\n  | nil => exact .refl _\n  | cons action step _ ih =>\n      exact .tail ⟨action, step⟩ ih`
  },
  {
    id: 'tryMove_reverse',
    title: '合法移动可逆',
    category: '连通性',
    evidence: 'kernel',
    file: 'Huarongdao/Reversibility.lean',
    anchor: 'theorem tryMove_reverse',
    tags: ['reversible', 'inverse'],
    statement: 'tryMove s p d = some t → tryMove t p d.reverse = some s',
    plain: '利用方向逆元、合法性保持和位置数组重建，可以证明同一个棋子反向移动后回到原状态。',
    chain: ['translated_reverse', 'moveUnchecked_reverse', 'tryMove_reverse', 'step_symm_of_valid'],
    related: ['concreteReversible', 'shapeReversible', 'mirrorReversible'],
    sourceWindow: 22,
    fallback: `theorem tryMove_reverse {s t : State} {p : Piece} {d : Direction}\n    (sourceValid : ValidState s)\n    (executed : tryMove s p d = some t) :\n    tryMove t p d.reverse = some s := by\n  ...`
  },
  {
    id: 'concreteWalk_projectsToMirror',
    title: '两层商保持原子步长度',
    category: '商空间',
    evidence: 'kernel',
    featured: true,
    file: 'Huarongdao/StateSpaceKernel.lean',
    anchor: 'theorem concreteWalk_projectsToMirror',
    tags: ['concrete', 'shape', 'mirror', 'length'],
    statement: '(concreteToMirror.mapWalk walk).length = walk.length',
    plain: '从带编号状态到同形商，再到水平镜像商，投影都不改变路径长度。因此商图中的原子步距离可以提升回具体棋盘。',
    chain: ['concreteToShape', 'shapeToMirror', 'Task.Hom.mapWalk', 'concreteWalk_projectsToMirror'],
    related: ['shapePresentation_successorsComplete', 'corridorWalk_liftToConcreteWithCost'],
    sourceWindow: 18,
    fallback: `theorem concreteWalk_projectsToMirror\n    (walk : concrete.Walk source target) :\n    (concreteToMirror.mapWalk walk).length = walk.length :=\n  concreteToMirror.mapWalk_length walk`
  },
  {
    id: 'corridorWalk_liftToConcreteWithCost',
    title: '决策骨架宏步可展开',
    category: '商空间',
    evidence: 'kernel',
    file: 'Huarongdao/CorridorCompression.lean',
    anchor: 'theorem corridorWalk_liftToConcreteWithCost',
    tags: ['corridor', 'macro', 'expand'],
    statement: 'corridor walk → concrete walk with equal primitive cost',
    plain: '决策骨架保留分岔、目标和初态等锚点，把二度走廊压成带权宏边。每条宏边都保存一条可展开的底层 walk，权重总和等于原子步数。',
    chain: ['CorridorMacroStep.toWalk', 'corridorWalkExpand_length', 'mirrorShapeTask_liftToConcreteWithLength', 'corridorWalk_liftToConcreteWithCost'],
    related: ['corridorWalk_compressWithCost', 'corridorWalk_compress_expand_length'],
    sourceWindow: 24,
    fallback: `theorem corridorWalk_liftToConcreteWithCost\n    (walk : corridorTask.Walk source target)\n    (sourceRepresentative : ValidClassicState)\n    (source_eq : MirrorShapeState.ofState sourceRepresentative = source.1) :\n    ∃ targetRepresentative,\n      ∃ concreteWalk : validClassicTask.Walk\n          sourceRepresentative targetRepresentative,\n        concreteWalk.length = walk.actions.sum ∧\n        MirrorShapeState.ofState targetRepresentative = target.1 := by\n  ...`
  },
  {
    id: 'classic_solutionGate_guanYuClearsCaoSweep',
    title: '所有解必须经过关羽清扫门区',
    category: '离散几何',
    evidence: 'kernel',
    featured: true,
    file: 'Huarongdao/Bottleneck.lean',
    anchor: 'theorem classic_solutionGate_guanYuClearsCaoSweep',
    tags: ['gate', 'Guan Yu', 'Cao Cao'],
    statement: 'SolutionGate classic GuanYuClearsCaoSweep',
    plain: '曹操要从底部出口离开，路径中必须出现一次向下移动。移动发生前，关羽必须先清空曹操下降所需的扫掠区。',
    chain: ['classic_solution_uses_cao_down', 'successful_move_clears_sweep', 'visits_of_usesEdge_source', 'classic_solutionGate_guanYuClearsCaoSweep'],
    related: ['classic_solutionGate_caoCanDescend', 'GuanYuYield'],
    sourceWindow: 18,
    fallback: `theorem classic_solutionGate_guanYuClearsCaoSweep :\n    SolutionGate classic GuanYuClearsCaoSweep := by\n  intro solution\n  apply solution.path.visits_of_usesEdge_source\n    CaoDownStep GuanYuClearsCaoSweep\n  · intro source target move\n    refine ⟨target, move, ?_⟩\n    exact successful_move_clears_sweep move (by decide)\n  · exact classic_solution_uses_cao_down solution`
  },
  {
    id: 'valid_goal_caoBelowGuanYu',
    title: '目标态中曹操位于关羽下方',
    category: '离散几何',
    evidence: 'kernel',
    file: 'Huarongdao/CaoGuanGeometry.lean',
    anchor: 'theorem valid_goal_caoBelowGuanYu',
    tags: ['geometry', 'goal', 'Cao Cao'],
    statement: 'ValidState state ∧ goal state → CaoBelowGuanYu state',
    plain: '由曹操的目标坐标、边界约束和不重叠约束可得：终局时曹操位于关羽下方，且两者的水平投影相交。',
    chain: ['goal_eq_true_iff', 'inBounds', 'noOverlap', 'valid_goal_caoBelowGuanYu'],
    related: ['solution_visits_caoBelowGuanYu', 'classic116Goal_caoBelowGuanYu'],
    sourceWindow: 26,
    fallback: `theorem valid_goal_caoBelowGuanYu {state : State}\n    (validState : ValidState state) (goalState : goal state = true) :\n    CaoBelowGuanYu state := by\n  ...`
  },
  {
    id: 'checkClosedGraph_sound',
    title: '闭包检查推出可达状态完备',
    category: '有限证书',
    evidence: 'checked',
    file: 'Huarongdao/Generic/Certificates.lean',
    anchor: 'theorem checkClosedGraph_sound',
    tags: ['checker', 'closure', 'soundness'],
    statement: 'checkClosedGraph = true → every reachable state is listed',
    plain: 'checker 重新确认初态在节点集内，并逐个检查每个节点的全部合法后继。对 `Reachable` 做归纳后，可得所有可达状态都已列入有限节点集。',
    chain: ['checkClosedGraph_closed', 'ClosedUnderMoves.reachable_mem', 'checkClosedGraph_sound'],
    related: ['no_reachable_goal_of_closed_graph', 'unreachable_verified_sound'],
    sourceWindow: 23,
    fallback: `theorem checkClosedGraph_sound\n    {spec : PuzzleSpec} {graph : StateGraph}\n    (checked : graph.checkClosedGraph spec = true) :\n    ∀ state, Reachable spec spec.initial state →\n      state ∈ graph.states.toList := by\n  intro state reachable\n  have closed := graph.checkClosedGraph_closed checked\n  exact closed.reachable_mem closed.1 reachable`
  },
  {
    id: 'shortest_of_verified_path_and_lower_bound',
    title: '上界与下界合成全局最短性',
    category: '有限证书',
    evidence: 'kernel',
    featured: true,
    file: 'Huarongdao/Generic/Certificates.lean',
    anchor: 'theorem shortest_of_verified_path_and_lower_bound',
    tags: ['certificate', 'minimality', 'generic'],
    statement: 'VerifiedPath actions ∧ LowerBoundCertificate → IsShortestSolution',
    plain: '`checkSolution` 给出一条确实通关的路径，`LowerBoundCertificate` 说明任何通关路径都至少需要同样多的步数。二者合成 `IsShortestSolution`。',
    chain: ['checkSolution_sound', 'LowerBoundCertificate.solves_lower_bound', 'shortest_of_verified_path_and_lower_bound'],
    related: ['classic116Play_minimal', 'Solution.minimal_of_lower_bound'],
    sourceWindow: 24,
    fallback: `theorem shortest_of_verified_path_and_lower_bound\n    {spec : PuzzleSpec} {actions : List Action}\n    (verified : VerifiedPath spec actions)\n    (certificate : LowerBoundCertificate spec actions.length) :\n    IsShortestSolution spec actions := by\n  constructor\n  · exact checkSolution_sound verified\n  · intro other otherSolves\n    exact certificate.solves_lower_bound otherSolves`
  },
  {
    id: 'fullSpace_semantic_complete',
    title: '全形状生成器覆盖所有同形状态',
    category: '全空间',
    evidence: 'kernel',
    file: 'Huarongdao/ClassicContinuousClassCard.lean',
    anchor: 'theorem fullSpace_semantic_complete',
    tags: ['enumeration', 'coverage', 'ContinuousClass'],
    statement: '∀ node : ShapeState, ∃ index, representative index = node',
    plain: '生成器按曹操、关羽、竖块和小兵的位置枚举，再用规范代表覆盖任意合法 `ShapeState`。因此，程序中的数组可以对应到数学上的全部同形商状态。',
    chain: ['EnumerationComplete', 'enumerationComplete_quotient_cover', 'fullSpace_semantic_complete'],
    related: ['fullSpace_stateInjective', 'fullSpaceRun_lawful_of_checked'],
    sourceWindow: 20,
    fallback: `theorem fullSpace_semantic_complete :\n    ∀ node : ShapeState,\n      ∃ index : Fin allShapeStates.size,\n        ShapeState.ofState ... = node :=\n  enumerationComplete_quotient_cover ... enumerationComplete`
  },
  {
    id: 'continuousClass_card_eq_898',
    title: '连续等价类基数 = 898（条件语义定理）',
    category: '全空间',
    evidence: 'conditional',
    featured: true,
    file: 'Huarongdao/ClassicContinuousClassCard.lean',
    anchor: 'theorem continuousClass_card_eq_898',
    tags: ['898', 'cardinality', 'open boundary'],
    statement: 'Lawful fullSpaceRun → Fintype.card ContinuousClass = 898',
    plain: '只要 DFS 运行满足 `Lawful`，根集合就与语义连续等价类等势，从而得到 898。当前定理保留这个前提。',
    chain: ['fullSpace_semanticCertificate', 'fullSpaceRun_lawful_of_checked', 'continuousClass_card_eq_898'],
    related: ['fullSpaceRun_roots_size', 'continuousClass_card_eq_898_of_certificate'],
    sourceWindow: 18,
    fallback: `theorem continuousClass_card_eq_898\n    (lawful : fullSpaceRun.Lawful allShapeStates) :\n    @Fintype.card ContinuousClass\n      (VerifiedShapePartition.continuousClassFintype\n        lawful.toVerifiedShapePartition) = 898 :=\n  ComponentRun.Lawful.continuousClass_card_eq_898_of_lawful\n    lawful fullSpaceRun_roots_size`
  },
  {
    id: 'shapePresentation_successorsComplete',
    title: '同形商的后继枚举完备',
    category: '商空间',
    evidence: 'kernel',
    file: 'Huarongdao/StateSpaceBfs.lean',
    anchor: 'theorem shapePresentation_successorsComplete',
    tags: ['BFS', 'bisimulation', 'quotient'],
    statement: 'shape task step → an executable representative successor exists',
    plain: '通用 BFS 引擎只更换 presentation，具体层、同形层和镜像层共用队列与距离算法。每层的 `successorsComplete` 负责确认枚举器没有漏掉语义边。',
    chain: ['concreteShapeQuotient.liftStepFrom', 'validSuccessors_complete', 'shapePresentation_successorsComplete'],
    related: ['mirrorPresentation_successorsComplete', 'enumerateBfs'],
    sourceWindow: 32,
    fallback: `theorem shapePresentation_successorsComplete :\n    shapePresentation.SuccessorsComplete := by\n  intro source action target step\n  rcases concreteShapeQuotient.liftStepFrom\n      step source rfl with\n    ⟨concreteAction, concreteTarget, concreteStep, targetEq⟩\n  ...`
  }
];

export const theoremDependencyEdges = [
  { from: 'tryMove_preserves_validity', to: 'tryMove_reverse', label: '合法性' },
  { from: 'tryMove_preserves_validity', to: 'shapePresentation_successorsComplete', label: '后继语义' },
  { from: 'tryMove_reverse', to: 'shapePresentation_successorsComplete', label: '可逆性' },
  { from: 'Path_toReachable', to: 'checkClosedGraph_sound', label: 'Reachable' },
  { from: 'tryMove_preserves_validity', to: 'checkClosedGraph_sound', label: 'Step' },
  { from: 'shapePresentation_successorsComplete', to: 'concreteWalk_projectsToMirror', label: '商步' },
  { from: 'concreteWalk_projectsToMirror', to: 'corridorWalk_liftToConcreteWithCost', label: '等长提升' },
  { from: 'checkClosedGraph_sound', to: 'shortest_of_verified_path_and_lower_bound', label: '闭包' },
  { from: 'concreteWalk_projectsToMirror', to: 'shortest_of_verified_path_and_lower_bound', label: '距离' },
  { from: 'shortest_of_verified_path_and_lower_bound', to: 'classic116Play_minimal', label: '最短性' },
  { from: 'valid_goal_caoBelowGuanYu', to: 'classic_solutionGate_guanYuClearsCaoSweep', label: '目标几何' },
  { from: 'fullSpace_semantic_complete', to: 'continuousClass_card_eq_898', label: '完备性' }
];

export const kernelComponents = [
  { name: 'inductive', symbol: 'Reachable / Path / Task.Walk', meaning: '构造器把每一步放进证明对象里，递归和归纳都能沿着这棵证明树展开。', example: 'Path.nil · Path.cons' },
  { name: 'structure', symbol: 'State / PuzzleSpec / Certificate', meaning: '数据、规格和证书字段放在同一个结构中，状态是否合法、边是否检查都有明确位置。', example: 'ValidState s := valid s = true' },
  { name: 'def', symbol: 'tryMove / goal / componentOf', meaning: '这些定义可以被 `decide`、BFS 和导出器计算，也能在定理证明中展开。', example: 'tryMove : ... → Option State' },
  { name: 'theorem', symbol: 'soundness / minimality / lift', meaning: '定理把计算结果写成语义命题，证明项最后由 Lean kernel 检查。', example: 'classic116Play_minimal' },
  { name: 'quotient', symbol: 'ShapeState / ContinuousClass', meaning: '等价状态共享一个代表。要让商图结论回到具体棋盘，还需要路径投影和提升。', example: 'continuousClassOf' },
  { name: 'certificate', symbol: 'checkClosedGraph / LowerBoundCertificate', meaning: '有限数据先被重新播放，再通过 soundness 定理进入数学结论。', example: 'checked → proof' },
  { name: 'native_decide', symbol: 'classic116_runs / fullSpace facts', meaning: '对封闭的可计算命题做原生求值，生成 Lean 可以接受的证明，不把 JavaScript 输出直接当作定理。', example: 'by native_decide' },
  { name: 'Mathlib', symbol: 'SimpleGraph / ConnectedComponent', meaning: '把项目里的可达关系接到标准图论对象上，直接使用已有的连通分量接口。', example: 'componentEquivConnectedComponent' }
];

export const evidenceLevels = [
  { id: 'all', label: '全部', description: '显示完整定理图谱' },
  { id: 'kernel', label: '内核定理', description: '无额外运行时前提的 Lean 命题' },
  { id: 'checked', label: '证书检查', description: '由 native_decide 或 checker 输入支撑' },
  { id: 'conditional', label: '条件接口', description: '数学桥已完成，但仍显式保留证书前提' }
];

export const sourceFiles = [
  { path: 'Huarongdao/Model.lean', layer: '模型', summary: '棋子、坐标、形状、合法状态和经典初态' },
  { path: 'Huarongdao/Transition.lean', layer: '语义', summary: 'tryMove、Step、Reachable 和合法性保持' },
  { path: 'Huarongdao/Paths.lean', layer: '路径', summary: 'Path、Solution、CertifiedPlay 和证明项构造' },
  { path: 'Huarongdao/Reversibility.lean', layer: '连通性', summary: '移动逆元与 Step 对称' },
  { path: 'Huarongdao/StateSpaceKernel.lean', layer: '内核 API', summary: 'concrete / shape / mirror / corridor 任务塔' },
  { path: 'Huarongdao/StateSpaceBfs.lean', layer: '执行', summary: '统一的 presentation 与 BFS 引擎' },
  { path: 'Huarongdao/Generic/Certificates.lean', layer: '证书', summary: '闭包、不可达、下界和最短性合成' },
  { path: 'Huarongdao/ClassicCertificate.lean', layer: '经典大定理', summary: '116 步动作、下界证书和 minimality' },
  { path: 'Huarongdao/CorridorCompression.lean', layer: '决策骨架', summary: '宏步压缩、展开和等成本提升' },
  { path: 'Huarongdao/Bottleneck.lean', layer: '离散几何', summary: 'SolutionGate、扫掠区和必经门区' },
  { path: 'Huarongdao/CaoGuanGeometry.lean', layer: '离散几何', summary: '目标态的曹操/关羽位置关系' },
  { path: 'Huarongdao/ClassicContinuousClassCard.lean', layer: '全空间', summary: '65,880、898 与 ContinuousClass 基数桥' }
];

export function theoremById(id) {
  return theoremRecords.find(record => record.id === id) || theoremRecords[0];
}

export function stageById(id) {
  return formalStages.find(stage => stage.id === id) || formalStages[0];
}
