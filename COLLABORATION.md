# HuarongdaoLean 三人协作规范

> 生效日期：2026-08-28
> 仓库：`fgyuuang/HuarongdaoLean`
> 协作者：`@fgyuuang`、`@tang0805-em`、`@10231510`

这份文件是仓库协作的权威规则。`TEAM_START.md` 负责环境安装和项目启动；本文件负责分支、同步、审查和合并。

## 1. 核心模型

三个人使用同一个私有仓库，不需要 Fork：

```text
feature/tang0805-em-<topic> ── PR ──┐
                                    │
feature/10231510-<topic> ───── PR ──┼──> 任一轮值集成人审查并合并 ──> main
                                    │
feature/fgyuuang-<topic> ───── PR ──┘
```

必须始终满足：

1. `main` 只保存已经审查、验证和集成的版本。
2. 所有开发都在个人功能分支中进行。
3. 所有进入 `main` 的修改都必须通过 Pull Request。
4. 三位协作者都可以担任 PR 的轮值集成人并执行最终合并。
5. 禁止对 `main` 使用普通 push、force push、网页直接编辑或本地合并后推送。
6. 一项任务对应一个分支、一个 PR；不要在同一个分支混入无关任务。
7. 每个 PR 只指定一位合并负责人，避免两个人同时处理同一项合并。

## 2. 任务先登记

开始工作前先创建 GitHub Issue，使用“开发任务”模板，至少写明：

- 负责人；
- 本 PR 的合并负责人；
- 目标和验收条件；
- 预计修改的文件或模块；
- 是否依赖其他 PR；
- 是否涉及 Lean 证明、前端、生成状态空间或布局数据。

如果两项任务可能修改同一个核心文件，例如：

```text
Huarongdao/StateSpace.lean
Huarongdao/Search.lean
frontend/app.js
README.md
package.json
```

两位开发者应先在 Issue 中确定边界或合并顺序。不要等到完成后才发现两边重写了同一模块。

## 3. 每项任务使用独立工作树

推荐让每个任务在独立 Git worktree 中运行。这样即使主目录有未提交工作，Agent 也不会覆盖它。

新任务：

```powershell
Set-Location 'D:\work\HuarongdaoLean'
git fetch origin --prune

$Branch = 'feature/<GitHub用户名>-<任务名>'
$Worktree = '..\HuarongdaoLean-<任务名>'

git worktree add -b $Branch $Worktree origin/main
Set-Location $Worktree
.\scripts\setup-git-collaboration.ps1
npm ci
lake exe cache get
```

例如：

```powershell
$Branch = 'feature/tang0805-em-launcher-test'
$Worktree = '..\HuarongdaoLean-launcher-test'
git worktree add -b $Branch $Worktree origin/main
```

恢复已经推送的远程分支：

```powershell
git fetch origin --prune
git branch --track feature/<用户名>-<任务名> origin/feature/<用户名>-<任务名>
git worktree add '..\HuarongdaoLean-<任务名>' feature/<用户名>-<任务名>
```

不要在已有未提交改动的目录中运行 `git switch main`、`git pull` 或复制整份队友目录。

## 4. 分支命名

允许的长期开发前缀：

```text
feature/<用户名>-<主题>
fix/<用户名>-<主题>
research/<用户名>-<主题>
docs/<用户名>-<主题>
chore/<用户名>-<主题>
```

临时保全分支：

```text
wip/<用户名>-YYYYMMDD-<主题>
```

示例：

```text
feature/tang0805-em-health-check
research/10231510-mirror-quotient
fix/fgyuuang-layout-selection
```

禁止使用只有 `test`、`new`、`update`、`final` 等无法追踪责任和目标的分支名。

## 5. 日常提交与推送

开发期间：

```powershell
git status --short
git diff
git add <本次任务实际修改的文件>
git commit -m "feat: describe one coherent change"
git push -u origin HEAD
```

规则：

1. 不使用 `git add .` 随手收集整个工作区。
2. 不提交 `.lake/`、`node_modules/`、日志、临时文档或调试输出。
3. 不覆盖队友已经修改的文件来“解决冲突”。
4. 不对个人共享分支使用 `git push --force`。
5. 仅当分支只有本人使用且完成 rebase 后，才允许 `git push --force-with-lease`。
6. 提交应按可审查的逻辑单元拆分，不要把数天工作压成一个无法解释的大提交。

## 6. 与最新 main 同步

个人独占的功能分支使用 rebase：

```powershell
git fetch origin --prune
git rebase origin/main
```

解决冲突后：

```powershell
git status
git add <已经人工确认的文件>
git rebase --continue
npm run check
git push --force-with-lease
```

如果一个功能分支由多人共同使用，不要 rebase。改为：

```powershell
git fetch origin --prune
git merge origin/main
npm run check
git push
```

遇到冲突时必须理解两边语义。禁止使用“全部接受当前版本”或“全部接受传入版本”处理核心 Lean、前端和生成数据文件。

## 7. Pull Request 合同

PR 必须：

1. 目标分支为 `main`；
2. 标题描述单一目标；
3. 关联对应 Issue；
4. 列出实际改动和未改动边界；
5. 列出运行过的验证命令及结果；
6. 标记冲突敏感文件；
7. 请求至少一位队友审查，并明确本 PR 的合并负责人；
8. 在合并前更新到最新 `origin/main`。

PR 可以尽早以 Draft 形式创建，让另外两人看到文件占用和接口变化。

通常由非作者队友担任合并负责人。对于只改文档、注释或其他低风险且不与开放
PR 重叠的修改，作者可以在 CI 通过、PR 合同完整并确认没有队友正在合并后自行
Squash 合并。涉及共享 Lean 内核、前端主入口、生成状态空间或冲突解决的 PR，
应由非作者队友合并。

## 8. 验证矩阵

所有 PR 至少运行：

```powershell
lake exe cache get
npm run check
```

修改经典状态、移动规则、商空间或导出逻辑时，额外运行：

```powershell
npm run export
npm run build:mirror
npm run build:corridor
npm run check:state-spaces
```

修改证书或最短性证明时，确认：

```powershell
npm run check:certificates
```

修改前端交互或布局时，除自动检查外，还要在桌面和移动视口做一次实际浏览器验收。

PR 中不得用“应该可以”“未运行但改动很小”代替验证结果。无法运行的检查必须明确写出原因和剩余风险。

## 9. 生成文件和高冲突文件

以下内容分为三类：

### 不提交

```text
.lake/
node_modules/
frontend/graph.json
*.log
本地临时输出
```

### 受控生成并提交

```text
frontend/graph.mirror.json
frontend/graph.corridor.json
frontend/layout.mirror.json
frontend/layout.corridor.json
frontend/*-summary.json
```

受控生成文件只能由负责对应生成管线的 PR 更新。PR 必须同时包含生成器修改、生成命令和一致性检查结果，禁止手工修改大型 JSON。

### 需要提前协调

```text
README.md
Huarongdao.lean
package.json
package-lock.json
frontend/app.js
Huarongdao/StateSpace.lean
Huarongdao/Search.lean
```

如果两项任务都需要这些文件，应在 Issue 中确定谁先合并，后合并者负责基于最新 `main` 重放自己的修改。

## 10. 轮值集成人合并流程

本 PR 中指定的合并负责人按以下顺序处理：

```powershell
gh pr checkout <PR编号>
git fetch origin --prune
git log --oneline origin/main..HEAD
git diff --stat origin/main...HEAD
npm ci
npm run check
```

审查重点：

1. 是否覆盖或删除了其他人的工作；
2. 是否包含与 Issue 无关的文件；
3. Lean 定理、JSON 和前端展示之间的语义是否一致；
4. 生成文件是否来自对应生成器；
5. CI 和本地验证是否通过；
6. 后续开放 PR 是否需要重新同步。

合并方式统一使用 **Squash and merge**。合并一个 PR 后：

1. 删除远程功能分支；
2. 通知其他开放 PR 更新到最新 `main`；
3. 冲突由该 PR 作者在自己的分支解决；
4. 重新运行 CI 后才继续合并。

为了避免两个 PR 同时通过检查后竞速合并，合并负责人开始操作时应在 PR 留言：

```text
我正在集成此 PR；完成前请暂缓合并其他会修改相同模块的 PR。
```

合并结束后再在受影响的其他 PR 留言要求同步最新 `main`。

## 11. 当前 GitHub 套餐限制

截至 2026-08-28，此私有仓库的 GitHub API 返回：

```text
Upgrade to GitHub Pro or make this repository public to enable this feature.
```

因此当前无法启用服务端分支保护和 Ruleset。现阶段使用以下替代措施：

- `.githooks/pre-push` 在本地阻止直接 push `main`；
- `.github/CODEOWNERS` 将三位协作者列为默认审阅人；
- GitHub Actions 对每个 PR 运行完整检查；
- GitHub Actions 在 `main` 更新不关联已合并 PR 时失败并留下审计记录；
- 仓库只允许 Squash 合并；
- 合并后自动删除功能分支；
- 每个 PR 明确一位轮值合并负责人。

本地 Hook 可以被 `--no-verify` 绕过，因此它不是安全边界。升级 GitHub Pro 后应立即启用：

```text
Require a pull request before merging
Required approvals: 1
Require status checks to pass
Require branches to be up to date
Block force pushes
Do not allow bypassing
```

## 12. 事故处理

### 在 main 上产生了未提交改动

不要 pull，不要 reset：

```powershell
git switch -c wip/<用户名>-YYYYMMDD-<主题>
git status
```

然后只提交属于该任务的文件并创建 PR。

### 在 main 上产生了本地提交

先保全：

```powershell
git branch wip/<用户名>-YYYYMMDD-main-recovery
```

由任一队友协助确认如何转成 PR。禁止 force push。

### 错误直接推送了 main

立即停止后续推送，在 GitHub Issue 中记录提交 SHA，由一位非操作人选择 `git revert` 或保留。不要通过历史重写掩盖事故。

### 两个 PR 修改同一区域

先合并依赖更少、接口更基础的 PR。另一个作者 rebase 最新 `main`，逐块解决冲突并重新验证。合并负责人不替作者猜测业务语义。

## 13. 每人最小清单

开发者：

```text
[ ] Issue 已登记并写明文件范围
[ ] 独立 worktree + 个人分支
[ ] 没有直接修改或推送 main
[ ] 只暂存本任务文件
[ ] npm run check 通过
[ ] PR 已关联 Issue、请求队友审查并指定合并负责人
[ ] 合并前已同步最新 main
```

轮值集成人：

```text
[ ] PR 范围与 Issue 一致
[ ] 无覆盖、无临时文件、无手改生成数据
[ ] CI 与必要的本地检查通过
[ ] 合并顺序已考虑其他开放 PR
[ ] 使用 Squash and merge
[ ] 合并后通知其他 PR 更新
```
