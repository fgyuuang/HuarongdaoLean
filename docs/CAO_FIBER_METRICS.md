# 曹操固定纤维的距离研究

## 研究对象

曹操左上角位置按

```text
(0,0) (1,0) (2,0)
(0,1) (1,1) (2,1)
(0,2) (1,2) (2,2)
(0,3) (1,3) (2,3)
```

排列。有限数值报告使用 `allShapeStates` 中曹操初态所在的等形连通分支，
并在这个有限枚举上重新构造数组邻接和 BFS 距离：

```text
全几何状态数：65880
连通分支数：898
经典初态所在分支：25955
```

因此，下面的矩阵不是把 898 个分支混合后的全语义 Hausdorff 距离，而是
有限枚举数组图模型中的经典分支纤维距离。报告 JSON 中的模型标识为：

```text
stateModel = finite-enumeration/allShapeStates/classic-component/array-graph
distanceModel = finite-array-BFS-and-Hausdorff
```

这里的“经典分支”是 `componentSummariesOf allShapeStates` 对数组索引执行的
可执行分量划分；“数组图”是由 `locallyLegalMove`、`placementIndex` 和对称化
邻接表生成的图。当前没有在 Lean 中证明该数组图与所有合法带标签状态上的
`concreteStateGraph` 同构，也没有证明数组代表的纤维集合与语义纤维逐点对应。

## 纤维规模

按上述位置顺序，12 个固定曹操位置纤维的状态数为：

```text
5563, 4861, 5563,
 692,  626,  692,
1514, 1570, 1514,
1198,  964, 1198
```

## 纤维最小距离

矩阵项为

```text
d_min(F_p,F_q) = min { d(s,t) | s in F_p, t in F_q }
```

其中 `d` 是有限数组图经典分支的最短路距离，而不是已经证明等于
`concreteStateGraph.edist` 的语义距离。

```text
 0  1 10  1  7 14 14 14 20 27 47 29
 1  0  1  7  1  7 17 11 17 25 42 25
10  1  0 14  7  1 20 14 14 29 47 27
 1  7 14  0  1 18  1  7 13 12 33 22
 7  1  7  1  0  1  7  1  7 13 30 13
14  7  1 18  1  0 13  7  1 22 33 12
14 17 20  1  7 13  0  1 10  1  9 17
14 11 14  7  1  7  1  0  1  7  1  7
20 17 14 13  7  1 10  1  0 17  9  1
27 25 29 12 13 22  1  7 17  0  1 12
47 42 47 33 30 33  9  1  9  1  0  1
29 25 27 22 13 12 17  7  1 12  1  0
```

它是对称的，但不满足三角不等式。这个结果符合一般集合最小距离的数学性质：中间纤维的两个最优配对不必经过同一个中间状态。

## Hausdorff 距离

矩阵项为

```text
d_H(F_p,F_q) = max(
  max_{s in F_p} min_{t in F_q} d(s,t),
  max_{t in F_q} min_{s in F_p} d(s,t)
)
```

```text
  0 61 72 98 82 79 101 103  97 110 126 110
 61  0 61 86 67 86  97  91  97 106 126 106
 72 61  0 79 82 98  97 103 101 110 126 110
 98 86 79  0 62 87  80  94  96  99 112 104
 82 67 82 62  0 62  82  76  82  91 120  91
 79 86 98 87 62  0  96  94  80 104 112  99
101 97 97 80 82 96   0  71  46  78  95  76
103 91 103 94 76 94  71   0  71  75  95  75
 97 97 101 96 82 80  46  71   0  76  95  78
110 106 110 99 91 104  78  75  76   0  63  52
126 126 126 112 120 112  95  95  95  63   0  63
110 106 110 104 91 99  76  75  78  52  63   0
```

该矩阵在有限数组图的经典分支内全为有限值，且程序核验得到：

```text
finite=true
Hausdorff-symmetric=true
Hausdorff-triangle=true
```

## 与 Lean 语义定义的关系

`Huarongdao.CaoFiberMetrics` 中的 `caoPositionHausdorffEDist` 是具体带标签
状态图上的语义定义：

```text
graphHausdorffEDist concreteStateGraph
  (caoFiber left) (caoFiber right)
```

它的值域是 `ℝ≥0∞`，因此不连通时保留 `∞`；其对称性和三角不等式由图诱导的
扩展度量与 Mathlib 的 Hausdorff 定理证明。

同一 Lean 文件还定义了
`concreteClassicComponentCaoPositionHausdorffEDist`。它把语义纤维限制到
`concreteStateGraph.Reachable classicValid` 所定义的**语义具体图连通分支**，
因此是一个严格的语义 restriction：

```text
graphHausdorffEDist concreteStateGraph
  (caoFiber left ∩ concreteClassicComponent)
  (caoFiber right ∩ concreteClassicComponent)
```

但是，目前没有证明 `allShapeStates` 的可执行经典分支等于这个语义具体图分支，
也没有证明有限数组邻接与 `concreteStateGraph` 的边集完全一致。因此，下面的
12×12 数值矩阵不能写成 `caoPositionHausdorffEDist` 或
`concreteClassicComponentCaoPositionHausdorffEDist` 的已经验证的 restriction；
它应当被称为有限枚举数组图上的独立计算结果。

## 关羽让路强命题

`Huarongdao.GuanYuYield` 中新增了如下证明接口：

```lean
structure YieldAvoidanceCertificate (start : State) where
  inside : State -> Prop
  start_inside : inside start
  closed :
    inside source ->
    legal source action target ->
    not (GuanYuYield source action target) ->
    inside target
  goal_excluded :
    inside target ->
    goal target = true ->
    False
```

由此得到：

```lean
classic_solution_uses_guanYu_yield_of_certificate
```

它的逻辑含义是：只要有一个“禁止让路边”闭包证书，并且证书内部不含目标状态，那么所有解都必须使用 `GuanYuYield`。

当前有限商搜索的本身也已经是 Lean 的 `native_decide` 定理：

```lean
avoidYieldBfs_none : avoidYieldBfs = none
```

有限节点版本已经形式化为：

```lean
FiniteYieldAvoidanceCertificate
classic_solution_uses_guanYu_yield_of_finite_certificate
```

该结构要求节点表示关系、初始节点、禁止让路边闭包以及内部无目标；因此它是把有限 BFS 结果升级为路径级定理的正式证书接口，而不是仅仅输出一行搜索日志。

它证实了当前有限搜索器中的禁止让路搜索没有找到目标。具体路径到等形规范路径的提升桥接已经在
`Huarongdao.GuanYuYieldBridge` 中完成：

```lean
QPath.UsesTransition_ofPath_iff
liftNoYieldStep
liftNoYieldPath
liftNoYieldSolution
liftNoYieldSolution_goal
```

其证明链是：

```text
具体合法一步且非 GuanYuYield
  -> 用 sameShapeRelabeling 将源状态送到任意等形代表
  -> 用 tryMove_relabel_some 得到代表上的合法动作
  -> 用 GuanYuYield.relabel_iff 保持“非让路”
  -> 得到目标的等形代表
```

逐步对路径归纳，即得到：

```text
具体路径无 GuanYuYield
  -> 从任意等形代表出发的 QPath 无 GuanYuYield
  -> 若原终态是目标态，则代表终态也是目标态
```

最后一层有限证书已经在
`Huarongdao.GuanYuYieldFiniteCertificate` 中完成。其节点是禁止让路 BFS
实际访问到的有限规范状态索引，证书验证了：

```lean
avoidYieldQueue_no_goal
avoidYieldQueue_closed
```

其中闭包检查对每个规范状态的每个合法非让路动作，要求目标状态与访问队列中的
某个规范状态满足可判定的 `SameShape`；因此没有把 `State.key` 的字符串相等未经
证明地当作状态相等。由此正式推出最终强命题：

```lean
classic_solution_uses_guanYu_yield
```

即：

```lean
forall solution : Solution classic,
  solution.path.UsesTransition GuanYuYield
```

当前代码已经完成从有限计算证书、等形重标记不变性、具体路径提升，到所有具体带标签解路径的内核定理闭环。
