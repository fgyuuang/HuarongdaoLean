# 经典华容道全拼法空间与连续等价类

本文记录 2026-08-28 版本对经典 `4 x 5` 华容道全体合法同形拼法的构造、连通分量计算、Lean 证书边界和下一阶段形式化目标。

## 1. 两个不同的状态空间

经典页面的 `frontend/graph.json` 只包含传统初态可达的同形商分量：

```text
25,955 个状态
83,896 条有向动作边
41,948 条无向连接
```

全拼法空间允许先把给定形状的木块取出并重新摆成任意合法布局，再研究这些布局之间能否只靠单格滑动互达。构造计数为：

```text
曹操、关羽和四个竖块的无重叠骨架：4,392
每个骨架剩余 6 格，选择 4 格放置小兵：C(6,4) = 15
候选同形布局：4,392 * 15 = 65,880
```

带编号状态还要乘以四个竖块和四个小兵的重标号：

```text
65,880 * 4! * 4! = 37,946,880
```

## 2. 连续等价关系

对 `ShapeState` 定义：

```lean
def ContinuousEquivalent (source target : ShapeState) : Prop :=
  ClassicStateSpaceKernel.shape.Reachable source target
```

一次原子变化只能是棋盘内的合法单格滑动。可逆性给出对称性，空路径给出自反性，路径拼接给出传递性，因此：

```lean
continuousEquivalent_equivalence : Equivalence ContinuousEquivalent
ContinuousClass := shape.Component shapeReversible
continuousClassOf_eq_iff :
  continuousClassOf source = continuousClassOf target <->
  ContinuousEquivalent source target
```

这里的“连续”是有限状态图中的组合路径连通，不是给有限离散状态类型直接赋普通拓扑后的连续映射。

## 3. 可执行构造

`Huarongdao/ClassicFullSpace.lean` 按固定顺序放置曹操、关羽、四个竖块和四个小兵。相同形状的块按棋盘位置排序，得到确定性的带标签代表。

每个状态用十个位置码的 base-20 编码索引。全局 DFS 只展开每个生成状态一次：

```text
建立 placementCode -> state index
  -> 对每个未访问状态开始 DFS
  -> 用 legalMoves 枚举全部合法一步
  -> 后继按同形 placementCode 回查
  -> 累积分量大小、动作边数和经典初态标记
```

时间复杂度为 `O(|V| + |E|)` 次状态/边处理，另加每步固定大小的编码、排序和哈希开销。当前机器上导出约需 9 秒。

确定性代表策略是：取构造枚举顺序中该 DFS 分量遇到的第一个状态。

## 4. 精确计算结果

Lean 导出和独立 Python 复算一致：

```text
生成状态数：65,880
无向边数：103,390
有向动作边数：206,780
DFS 分量数：898
最小分量：2
最大分量：25,955，共 2 个
经典初态所在分量：25,955
```

分量大小分布：

```text
2:36, 4:292, 6:112, 8:100, 9:4, 10:28, 11:4, 12:56,
14:8, 16:64, 18:4, 19:4, 20:8, 21:4, 24:42, 25:4,
26:30, 27:4, 28:4, 29:12, 30:8, 32:4, 33:8, 36:8,
45:4, 47:4, 52:2, 55:2, 73:4, 75:4, 92:4, 98:4,
99:4, 118:4, 181:4, 201:4, 248:4, 25955:2
```

这说明传统 `25,955` 节点全览图只是两个最大连续世界之一，不是全部合法拼法空间。

## 5. 对称作用的探索结果

左右镜像作用于 65,880 个状态和 898 个 DFS 分量：

```text
状态镜像轨道：33,030
镜像不动状态：180
镜像固定分量：20
互换分量对：439
分量镜像轨道：459
```

两个最大分量都被左右镜像保持，并各含 67 个镜像不动状态，所以各自的镜像商大小为：

```text
(25,955 + 67) / 2 = 13,011
```

这与现有经典镜像商 `frontend/graph.mirror.json` 的节点数一致。

若暂时忘记“曹操从底部离开”的目标谓词，全棋盘图还具有上下镜像和 180 度旋转。它们与左右镜像形成 Klein 四元群。独立复算得到：

```text
状态轨道：16,515
分量轨道：230
水平固定分量：20
垂直固定分量：2
旋转固定分量：0
```

上下镜像不保持当前出口目标，因此它是无目标布局图的自同构，不是当前带目标任务的对称。传统初态属于分量 `#15`，其上下镜像属于分量 `#0`；两者都含 `25,955` 个状态，垂直反射交换这两个分量：

```text
verticalComponent(15) = 0
verticalComponent(0) = 15
```

所以“允许把整块棋盘上下翻转”增加的是一条离散对称识别，不是新的单格滑动。它把两个原本不同的 `ContinuousEquivalent` 类放入同一个 Klein 轨道，但不会在原状态图中添加合法边。

## 6. 全空间总览页面

本地服务启动后打开：

```text
http://127.0.0.1:4173/full-space.html
```

页面直接读取 `frontend/full-shape-components.json`，不访问在线服务。可视对象的含义为：

```text
一个球体 = 一个 DFS 连续分量
球体大小 = log(分量状态数)
青色线 = 左右镜像的分量像
金色线 = 上下镜像的分量像
紫色线 = 180° 旋转的分量像
```

坐标不是随机力导向结果。首先按 Klein 四元群把 898 个分量归成 230 个轨道；每个轨道内部用 `1, H, V, HV` 四个群元素的方形槽位放置成员。若一个分量被某个对称固定，重复槽位取平均。230 个轨道中心再按确定性螺旋排列，因此刷新不会改变位置。

传统初态分量 `#15` 和上下翻转分量 `#0` 被放在中央并分别突出显示。点击节点显示该分量的确定性代表棋盘、状态数、内部无向边数和三种对称像。对称连线可以独立开关，但它们始终不是 `Step` 或 `ContinuousEquivalent` 的见证。

点击“接入当前任务”会跳转到：

```text
index.html?mode=lab&fullSpaceComponent=<component-id>
```

`frontend/laboratory.js` 从同一份 JSON 读取十个代表位置，构造经典 `4×5`、`2×2 + 2×1 + 4×(1×2) + 4×(1×1)` 任务，并保留曹操目标 `(1,3)`。该任务可继续编辑、验证、A* 求解或用 BFS 枚举其可达分量。这个入口不会把任意规范代表误称为传统初态；分量 `#15` 才包含传统“横刀立马”布局。

## 7. 当前 Lean 证书证明了什么

`Huarongdao/ClassicFullSpaceCertificate.lean` 用一次隔离的 `native_decide` 检查：

```text
生成数组大小 = 65,880
全部生成状态 valid = true
同形键唯一
全部 legalMoves 后继仍能在生成数组中找到
DFS 摘要数 = 898
摘要大小之和 = 65,880
经典摘要大小 = 25,955
```

严格证书约需数分钟，因此不进入默认 `lake build`。按需运行：

```powershell
lake env lean Huarongdao\ClassicFullSpaceCertificate.lean
lake build export-full-space
.\.lake\build\bin\export-full-space.exe frontend\full-shape-components.json
```

`Huarongdao/ClassicComponentSymmetry.lean` 另外已经形式化：

- 水平和垂直反射保持合法状态，并把一步合法移动映到一步合法移动；
- 水平反射下降为 `ContinuousClass` 上的群作用；
- 垂直反射下降为连续分量上的对合，并交换传统初态与其上下镜像；
- 用棋子锚点坐标和的奇偶性给整个语义形状图构造二着色，因此不存在奇长度闭游走。

`Huarongdao/ClassicComponentSymmetryCertificate.lean` 将有限计算结果连接到上述语义层，包括水平分量轨道数 `459`、水平固定分量数 `20`、两个最大分量各有 `25,955` 个状态，以及：

```lean
not_continuousEquivalent_classic_verticalMirror :
  ¬ContinuousEquivalent classicShapeState verticalClassicShapeState
```

## 8. 语义桥与必须保留的证明边界

`ClassicFullSpaceSoundness.lean` 已经证明：在 `ComponentRun.Lawful` 条件下，DFS 标签相同当且仅当语义上的 `shape.Reachable`，父边和闭包 checker 也具有 soundness。现在还补上了从有限分割到连续等价类基数的通用桥：

```lean
VerifiedShapePartition.component_eq_iff_reachable
VerifiedShapePartition.componentEquivContinuousClass
VerifiedShapePartition.fintypeCard_continuousClass_eq
ComponentRun.Lawful.continuousClass_card_eq_898_of_certificate
```

因此，在给定一个满足 `ComponentRun.Lawful` 的有限分割，并证明其分量类型的基数为 `898` 时，`Fintype.card ContinuousClass = 898` 的数学推导已经闭合。当前仍不能无条件把“DFS 返回 898”写成该基数定理，主要还缺少：

1. `EnumerationComplete`：任意合法经典状态都与生成数组中的某个状态 `SameShape`。
2. canonical representative 唯一性：需要把当前 `uniqueKeys` 哈希去重检查提升为 `SameShape` 相等代表的索引唯一性定理。
3. 将当前原生计算的 `ComponentRun.Lawful`、精确根数组和分量计数打包成最终基数证书。

第一个目标已经作为 Lean 命题显式定义：

```lean
def EnumerationComplete : Prop :=
  forall source : ValidClassicState,
    exists representative in allShapeStatesList,
      SameShape source.1 representative
```

`EnumerationComplete` 到有限数组覆盖的第一步也已经形式化为：

```lean
enumerationComplete_quotient_cover
```

下一步仍需让 DFS 的所有索引级事实（标签范围、根标签、父边、闭包和规范代表唯一性）聚合为 `ComponentRun.Lawful`。完成后即可严格得到：

```text
Fintype.card ContinuousClass = 898
```

## 9. 后续数学问题

1. 完成 `EnumerationComplete` 的结构性证明。
2. 完成 canonical representative 唯一性和哈希证书 soundness。
3. 将已认证 DFS 分类推出为 `Fintype.card ContinuousClass = 898`。
4. 认证 Klein 四元群在连续分量集合上的 `230` 个轨道，而不只在导出程序中计算。
5. 对 25,955 大分量认证桥、割点、双连通块和“关羽让路”必经门。
6. 把可交换动作形成的正方形补成 cubical complex，研究局部维数、循环空间和基本群。
