# 局部拓扑研究：同形商节点 #1409

## 1. 对象与验证边界

本案例研究 `enumerate classic` 导出的同形商节点 `#1409`。前端取其半径 2 诱导子图，并把每个 `SquareAt` 交换方形作为二维胞腔填入。

项目刻意区分三种结论：

- Lean 内核定理：合法动作、动作交换、Link 边、孤立动作、局部维数与镜像键。
- 有限图自动检查：半径 2 子图、同调、局部切分和全图绕行反例。
- Three.js 展示：节点位置、颜色与三维排布，不属于证明数据。

## 2. Lean 已验证的动作 Link

`classicLocal1409` 有且仅有五个合法带标签动作：

```text
马超下  黄忠左  兵二右  兵三上  兵四右
```

四条交换边为：

```text
马超下 -- 兵二右
   |          |
兵三上 -- 兵四右

黄忠左          （孤立点）
```

因此选定动作 Link 同构于 `C4 ⊔ {point}`。四边形的两条对角线不是 Link 边，不存在三个两两可交换的合法动作，故局部交换维数为 2，而不是 3。

关键声明位于 `Huarongdao/ClassicLocalTopology.lean`：

```lean
classicLocal1409_legal_actions
classicLocal1409_link_cycle
classicLocal1409_link_diagonals_absent
classicLocal1409_huangZhong_isolated
classicLocal1409_no_commuting_triple_checked
classicLocal1409_mirror_key
```

`#1409` 的水平镜像规范键对应导出节点 `#1442`。

## 3. 方形复形的有限计算

半径 2 诱导子图包含：

```text
V = 18, E = 23, F = 4
χ = V - E + F = -1
```

把四个交换方形填作 2-胞腔后，`scripts/check-local-topology.mjs` 在 `F2` 上对边界矩阵做高斯消元，得到：

```text
(β0, β1, β2) = (1, 2, 0)
H1(F2) ≅ F2²
```

含义是复形整体连通；交换方形消去四个交换型操作环后，仍保留两个独立的一维同调类；没有二维闭合空腔。该结果目前是自动检查的有限数据结论，还没有提升为 Lean 同调定理。

## 4. 局部瓶颈不是全局分离点

在半径 2 子图中移除 `#1409` 后，节点分成大小 14 和 3 的两个连通分支。但是完整同形商图中存在绕开中心的路径：

```text
#1261 -> #1329 -> #1408
```

它在截断邻域之外重新连接两侧。因此：

```text
localCutComponents > 1 不能推出 VertexSeparator
```

这是项目中重要的反例边界。若要得到“所有解必经”的定理，仍需构造 `GoalSeparatorCertificate` 或在完整闭图上检查分离证书。

## 5. 与最短解的关系

节点 `#1409` 的初态距离为 36，目标距离为 86，总和 122，大于全局最短值 116。因此它是局部离散几何的代表案例，但不位于任何 116 步最短路径上。

后续应增加第二个对照样本，例如 `#551`：它满足 `distance(initial,#551) + distance(#551,goal) = 116`，可用于研究最短路径上的交换结构，并与 `#1409` 的拓扑丰富但非最优区域比较。
