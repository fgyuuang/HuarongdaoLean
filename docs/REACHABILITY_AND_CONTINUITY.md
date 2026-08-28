# 华容道的可达性、连续滑动与连通分支

本文给出项目中“只能在棋盘内连续滑动，不能拆出木块后重新摆放”的严格数学解释，并说明它与 Mathlib 图论、对称商和后续拓扑研究的关系。对应 Lean 实现位于：

```text
Huarongdao/StateSpaceConnectivity.lean
```

## 1. 基本对象

一个华容道任务被建模为带根、带目标谓词、带动作标签的状态转移系统：

```lean
structure Task (State : Type u) (Action : Type v) where
  initial : State
  goal : State → Prop
  step : State → Action → State → Prop
```

其中：

- `State` 是完整棋盘局面；
- `Action` 是一次原子动作，例如移动某一块及其方向；
- `task.step s a t` 表示动作 `a` 能把 `s` 合法地变成 `t`；
- 非法穿越、重叠、越界和取出木块重排都不是 `step`。

有限合法移动序列由依赖类型 `Task.Walk` 表示。它同时保存动作、每一步合法性证明和首尾状态：

```lean
task.Walk source target
```

可达性定义为存在一条这样的有限路径：

```lean
def Task.Reachable (task) (source target) : Prop :=
  Nonempty (task.Walk source target)
```

因此，“可达”不是搜索器返回的布尔标志，而是 Lean 内核可以检查的路径存在命题。

## 2. 可逆性与连续滑动

华容道的一次合法滑动可以由同一块的反方向滑动撤销。抽象接口为：

```lean
structure Task.Reversible (task : Task State Action) : Prop where
  reverse_step :
    task.step source action target →
    ∃ reverseAction, task.step target reverseAction source
```

项目已经证明：

```lean
Task.Reversible.reverseWalk
Task.Reversible.reachable_symm
```

因此每条合法路径都可以反向执行。再结合空路径和路径拼接，得到：

```lean
Task.reachable_refl
Task.reachable_trans
Task.Reversible.reachable_symm
```

所以在可逆任务上，`Reachable` 是等价关系。

这里应使用“局部可逆变换”而不是“全局自同构”：

- 一次合法移动只在满足前置条件的状态上定义，是局部可逆箭头；
- 一串合法移动是一条路径；
- 一条从状态回到自身的路径是闭路；
- 镜像或棋子重标号保持整个任务结构时，才是任务的全局自同构。

若后续需要严格的群胚语言，可以把状态作为对象、合法路径作为态射、反向路径作为逆。当前 `Task.Reversible` 已提供建立该结构所需的路径逆，但尚未把路径按回退消去关系再取商。

## 3. 最小等价关系

`reachable_minimal` 证明 `Reachable` 是包含所有合法一步移动的最小自反传递关系。对可逆任务，进一步有：

```lean
Task.Reversible.reachable_le_equivalence
```

其数学内容是：

> 对任意等价关系 `R`，只要每个合法一步移动都满足 `R source target`，那么所有可达状态也满足 `R source target`。

因此，合法滑动生成的可达关系就是规则所生成的最小等价关系。这个结论严格表达了“只能滑动，不能拆板重排”：

- 合法滑动只能在同一个可达等价类内部运动；
- 外部重排可以任意改变状态，但它不是由 `step` 生成的；
- 若重排前后的状态属于不同可达类，就不存在任何合法滑动序列实现该重排。

对一个具体重排，要证明它无法通过合法移动实现，可以使用两类证书：

1. 证明两个状态的可达分支不同；
2. 构造一个合法一步保持的不变量，而两个状态的不变量值不同。

## 4. 可达商与连通分支

项目定义：

```lean
Task.reachabilitySetoid
Task.Component
Task.componentOf
```

其中：

```lean
Task.Component task reversible
```

是所有状态按可达关系取商后的类型。核心定理是：

```lean
Task.componentOf_eq_iff_reachable :
  componentOf source = componentOf target ↔
  task.Reachable source target
```

这给出一个精确判据：

> 两个状态可以只通过合法滑动互相到达，当且仅当它们属于同一个可达连通分支。

每个合法原子移动保持分支：

```lean
Task.componentOf_eq_of_step
```

分支不同也等价于不可达：

```lean
Task.not_reachable_iff_componentOf_ne
```

这类分支就是视频中出现的互不连通“状态岛”。BFS 从一个初态穷举时，只会枚举初态所在的一个分支，而不会自动枚举所有可能合法摆放形成的其他分支。

## 5. 与 Mathlib 连通分支一致

对任意可逆 `Task`，模块构造无向简单图：

```lean
Task.simpleGraph task reversible
```

图的顶点是状态，边是忘记动作标签后的合法一步移动。任务可达性与 Mathlib 图可达性严格等价：

```lean
Task.Reversible.task_reachable_iff_simpleGraph
```

项目的可达分支商还与 Mathlib 的 `SimpleGraph.ConnectedComponent` 典范等价：

```lean
Task.Reversible.componentEquivConnectedComponent :
  Task.Component task reversible ≃
  (Task.simpleGraph task reversible).ConnectedComponent
```

因此可以直接使用 Mathlib 关于连通分支、图距离、割点、桥、诱导子图和有限图的理论，而不需要另造一套“华容道连通性”定义。

对于任意 `PuzzleSpec`，已有：

```lean
SlidingPuzzle.validStateSpaceTask
SlidingPuzzle.validStateSpaceTaskReversible
SlidingPuzzle.validStateSpaceTask_simpleGraph_eq
SlidingPuzzle.same_component_iff_mathlib
```

这证明通用合法状态任务的底层图正是已有的 `puzzleSimpleGraph`。

## 6. 可达商与对称商不同

项目中现在存在两种数学意义不同的商。

### 6.1 对称商

```text
concrete → shape → mirror
```

它忘记同形棋子的标签，再忘记左右镜像差异。它回答：

> 哪些状态在指定观察或群作用下被认为相同？

### 6.2 可达商

```text
State → Component
```

它把所有能通过合法路径互达的状态压成一个分支。它回答：

> 哪些状态属于同一个合法运动世界？

二者不能混淆。两个镜像状态可能在对称观察下相同，但在原具体任务中不一定存在一条合法路径把一个变成另一个。对称商可以合并可达分支。

任务同态会诱导分支映射：

```lean
Task.Hom.mapComponent
```

该映射总是良定义，因为同态把合法路径映成合法路径，但它不一定单射。要证明商图没有错误地合并某些具体分支，需要额外的路径提升或轨道可达性定理。

经典项目的三层已经分别获得可逆实例：

```lean
ClassicStateSpaceKernel.concreteReversible
ClassicStateSpaceKernel.shapeReversible
ClassicStateSpaceKernel.mirrorReversible
```

所以每层都可以独立研究自己的可达分支和 Mathlib 连通分支。

## 7. 不变量与不可达证明

一步不变量定义为：

```lean
def Task.StepInvariant (task) (observable : State → Observable) : Prop :=
  ∀ {source action target},
    task.step source action target →
    observable source = observable target
```

模块证明：

```lean
Task.StepInvariant.eq_of_walk
Task.StepInvariant.eq_of_reachable
Task.StepInvariant.not_reachable_of_ne
Task.StepInvariant.descend
```

因此每个一步不变量都会下降为分支商上的函数。适合研究的不变量包括：

- 某些棋子在狭窄通道中的相对顺序；
- 不能交换的同轨道块的排列类型；
- 某种棋子或空位配置的奇偶量；
- 删除特定门区后所在的连通侧；
- 由对称群轨道得到、且被所有合法移动保持的离散标签。

不是每个直观量都真的是不变量。Lean 的优势在于必须逐条证明它被所有 `step` 保持，或者由有限图证书检查器验证。

## 8. “关公必须放过曹操”的形式化

这类陈述通常不是全局不变量，而是必经门或割集定理。现有框架可以定义：

```lean
side : State → Bool
gate : State → Prop
```

其中 `side` 表示曹操位于障碍结构的哪一侧，`gate` 表示关公处于允许曹操通过的关键姿态。然后证明：

```lean
∀ {u v action},
  task.step u action v →
  side u ≠ side v →
  gate u ∨ gate v
```

结合初态和目标态位于不同侧，已有：

```lean
Task.Walk.visits_of_side_change
Task.GoalSeparatorCertificate.solutionGate
```

即可得到：

> 每一条从初态到目标的合法路径都必须访问 `gate`。

如果 `gate` 是单个节点，就是割点候选；若是若干节点，就是顶点割集；若侧的改变只能经过某条边族，就是边割或桥证书。这比口头说“必须让路”更精确，因为它量化了所有可能解法。

## 9. “连续”的拓扑版本

当前已经形式化的是组合路径连续性，即有限图中的路径连通性。这是滑块谜题最直接、计算上也最有用的定义。

不能直接把有限状态类型赋予离散拓扑后，把非平凡滑动写成连续映射 `[0,1] → State`。从连通区间到离散空间的连续映射只能是常值，因此这种模型会丢掉每条移动的中间过程。

若要进入真正的拓扑空间，应构造状态图的几何实现：

- 每个合法状态实现为一个顶点；
- 每条合法一步边实现为一个闭区间；
- 区间端点粘到对应状态顶点；
- 一串滑动实现为几何图中的连续路径。

期望证明的主结论是：

```text
组合 Reachable source target
↔
几何实现中 source 与 target 路径连通
```

在此基础上才适合研究：

- 连通分支与路径分支；
- 环路和基本群；
- 图的同调或循环空间；
- 对称群作用在几何实现上的商；
- 割点、桥与拓扑分离性质之间的对应。

几何实现尚未加入当前版本。现阶段应以 `Task.Reachable` 和 `SimpleGraph.ConnectedComponent` 作为严格基础。

## 10. 下一批可证明结论

建议按以下顺序推进：

1. 为完整枚举图建立“所有合法摆放的分支分类”证书，而不只枚举初态分支。
2. 找到经典华容道不可达岛的可计算不变量，并证明它沿每一步保持。
3. 为“关公让路”定义具体 `side` 与 `gate`，生成 `GoalSeparatorCertificate`。
4. 在镜像商上计算割点、桥和最小割集，再通过投影定理拉回具体层。
5. 定义状态图的几何实现，证明组合可达与路径连通等价。
6. 将闭路按立即回退消去关系取商，建立路径群胚和顶点处环路群。

这些问题同时使用可执行枚举和内核证明，能够体现 Lean 4 的核心优势：搜索负责发现结构，证书负责压缩计算结果，定理负责把局部检查提升为全局数学结论。
