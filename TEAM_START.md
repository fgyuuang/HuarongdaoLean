# HuarongdaoLean 团队启动与同步指南

> 三人分支、PR、统一合并和 Agent 使用规则见
> [`COLLABORATION.md`](COLLABORATION.md) 与
> [`TEAM_AGENT_PROMPTS.md`](TEAM_AGENT_PROMPTS.md)。如果本文件中的旧同步示例
> 与 `COLLABORATION.md` 冲突，以 `COLLABORATION.md` 为准。

这份文档给第一次加入项目的队友使用，也适用于之前直接拿到旧版文件夹、没有通过 `git clone` 获取项目的队友。

项目仓库：

```text
https://github.com/fgyuuang/HuarongdaoLean
```

仓库是 Private。只有仓库所有者已经添加、并且队友接受邀请后，才能 clone、push 分支和提交 Pull Request。

## 0. 快速开始

新队友按下面的顺序执行：

```powershell
Set-Location 'D:\work'
git clone https://github.com/fgyuuang/HuarongdaoLean.git
Set-Location '.\HuarongdaoLean'

# 第一次安装前端依赖
npm ci

# 编译 Lean、检查前端脚本和通用求解器回归测试
npm run check

# 生成浏览器需要的 Lean 状态图数据
npm run export

# 启动本地网页和关卡实验室
npm run serve
```

浏览器打开：

```text
http://127.0.0.1:4173
```

停止服务时，在运行 `npm run serve` 的终端按 `Ctrl+C`。

## 1. 环境要求

安装以下工具：

- Git
- Lean 4.33.1 和 Lake
- Node.js 20 或更高版本，以及 npm
- 一个可以访问 GitHub Private 仓库的 GitHub 账号

项目根目录中的 `lean-toolchain` 固定了 Lean 版本。安装好 Lean 后，在项目目录检查：

```powershell
git --version
lean --version
lake --version
node --version
npm --version
```

如果 `lean --version` 不是 `4.33.1`，先修复 Lean/Elan 的工具链，再运行构建。不要为了绕过版本错误直接修改 `lean-toolchain`。

## 2. 第一次通过 Git 获取项目

### 2.1 认证并 clone

建议使用 HTTPS 地址：

```powershell
git clone https://github.com/fgyuuang/HuarongdaoLean.git
```

如果 GitHub 提示登录，请使用已经被添加为仓库协作者的 GitHub 账号。遇到 `Repository not found`，通常是以下原因之一：

- 邀请还没有被接受；
- 当前 Git 凭据登录的是另一个 GitHub 账号；
- clone 地址写错；
- 账号还没有仓库权限。

检查当前目录的远程地址：

```powershell
git remote -v
```

应当看到：

```text
https://github.com/fgyuuang/HuarongdaoLean.git
```

### 2.2 安装和验证

进入仓库后：

```powershell
npm ci
npm run check
npm run export
```

`npm run check` 会执行：

- `lake build`；
- `frontend/app.js`、`frontend/laboratory.js` 和 `scripts/serve.mjs` 的 JavaScript 语法检查；
- 通用求解器的 `solved`、`invalid`、`limit`、`unreachable` 和 `astar` 回归测试。

`npm run export` 会调用 Lean 生成 `frontend/graph.json`。这个文件属于本地生成物，已经被 `.gitignore` 忽略，不会从 GitHub 下载。

然后启动网页：

```powershell
npm run serve
```

### 2.3 为什么必须运行 `npm run export`

经典模式启动时会同时读取：

```text
frontend/graph.json
frontend/layout.json
```

其中：

- `frontend/graph.json` 由 Lean 根据当前源码生成；
- `frontend/layout.json` 是项目中保留的参考三维布局。

因此，刚 clone 的目录即使代码完整，也要先执行一次：

```powershell
npm run export
```

如果修改了经典华容道的状态模型、移动规则或图导出逻辑，也要重新执行这个命令。通常不需要手工编辑 `frontend/graph.json`。

## 3. 之前直接拿到旧版本文件夹的队友

### 3.1 没有个人改动：推荐重新 clone

如果旧文件夹只是最开始版本，没有需要保留的个人代码，最安全的方式是保留旧目录，然后重新 clone。不要在旧目录中直接 `git init`、`git pull` 或覆盖文件。

PowerShell 示例：

```powershell
Set-Location 'D:\work'

# 只改名，不删除旧目录
Rename-Item -LiteralPath '.\HuarongdaoLean' -NewName 'HuarongdaoLean-old'

# 获取当前 GitHub 最新版本
git clone https://github.com/fgyuuang/HuarongdaoLean.git '.\HuarongdaoLean'
Set-Location '.\HuarongdaoLean'

npm ci
npm run check
npm run export
npm run serve
```

确认新版本能够正常运行后，旧目录可以继续保留一段时间，确认没有遗漏个人文件后再由队友自行删除。

### 3.2 有个人改动：新目录迁移改动

如果旧文件夹中有队友自己的代码或文档，不要把整个旧文件夹直接复制覆盖新 clone 的目录。推荐按下面的流程：

1. 保留旧目录作为备份；
2. 把 GitHub 仓库 clone 到一个新目录；
3. 用编辑器的文件比较功能查看旧目录和新目录；
4. 只把自己真正修改过的源文件复制到新 clone；
5. 不要复制旧目录中的 `.git`、`.lake`、`node_modules` 或 `frontend/graph.json`；
6. 在新 clone 中检查差异，再放到迁移分支。

示例：

```powershell
Set-Location 'D:\work'
git clone https://github.com/fgyuuang/HuarongdaoLean.git '.\HuarongdaoLean-github'
Set-Location '.\HuarongdaoLean-github'

npm ci
npm run check
npm run export

# 创建迁移分支
git switch -c migrate/<自己的名字>-old-version

# 此时再从旧目录复制自己修改过的源文件
# 复制完成后检查：
git status
git diff
```

确认差异只包含自己的改动后：

```powershell
npm run check
npm run export
git add <实际修改的文件>
git commit -m "chore: migrate local changes from initial version"
git push -u origin migrate/<自己的名字>-old-version
```

然后在 GitHub 上创建 Pull Request，由项目负责人检查旧版本改动与当前版本的冲突。

### 3.3 旧目录本身已经有 `.git`

先检查，不要直接强制合并：

```powershell
git status --short
git remote -v
git log --oneline --decorate -5
```

如果旧目录的 Git 历史与 GitHub 仓库不是同一条历史，仍然采用“保留旧目录、重新 clone、新建迁移分支”的方式。不要使用以下高风险操作：

```text
git push --force
git reset --hard
```

除非项目负责人明确要求并确认目标分支。

## 4. 日常同步流程

> `main` 只作为集成分支。日常开发应按 `COLLABORATION.md` 在独立 worktree
> 和个人功能分支中进行，并通过 PR 交给本 PR 指定的轮值集成人合并。

开始当天工作前，先更新 `main`：

```powershell
Set-Location 'D:\work\HuarongdaoLean'
git switch main
git pull --ff-only origin main
```

`--ff-only` 会避免 Git 在不了解本地分叉时自动制造一个难以整理的合并提交。

如果 `package.json` 或 `package-lock.json` 有变化，再执行：

```powershell
npm ci
```

如果 Lean 源码或图导出相关代码有变化，重新构建并生成图：

```powershell
npm run check
npm run export
```

如果只是前端样式或交互修改，通常至少运行：

```powershell
npm run check
```

## 5. 分支和 Pull Request 流程

不要直接在 `main` 上开发。每项工作创建一个分支：

```powershell
git switch main
git pull --ff-only origin main
git switch -c feature/<名字>-<主题>
```

例如：

```powershell
git switch -c feature/zhangsan-laboratory-ui
```

开发过程中可以查看状态：

```powershell
git status
git diff
```

提交前至少运行：

```powershell
npm run check
```

涉及 Lean 移动规则、状态模型或图导出时，再运行：

```powershell
npm run export
```

确认无误后提交并推送：

```powershell
git add <实际修改的文件>
git commit -m "feat: describe the change"
git push -u origin feature/<名字>-<主题>
```

最后在 GitHub 上创建 Pull Request，目标分支选择 `main`。Pull Request 合并后，队友应当回到本地 `main`，再开始下一项工作。

## 6. 有本地改动时如何同步

先查看状态：

```powershell
git status
```

### 情况 A：工作区干净

直接同步：

```powershell
git pull --ff-only origin main
```

### 情况 B：改动还没有提交

推荐先提交到自己的功能分支。如果暂时还不能提交，可以临时保存：

```powershell
git stash push -u -m "wip before sync"
git pull --ff-only origin main
git stash pop
```

`git stash pop` 后如果出现冲突，先不要继续提交，打开冲突文件逐个处理，然后运行：

```powershell
git status
git diff
npm run check
```

### 情况 C：已经在 `main` 上做了本地提交

不要直接强制推送。先保留当前提交，再把远程更新整理进来：

```powershell
git branch backup-before-sync
git pull --rebase origin main
```

如果出现冲突，解决后执行：

```powershell
git add <已解决的文件>
git rebase --continue
```

如果不确定如何处理，保留 `backup-before-sync` 分支并联系项目负责人。

## 7. 常见问题

### `npm run serve` 显示 `graph.json unavailable`

先执行：

```powershell
npm run check
npm run export
npm run serve
```

### `lake` 或 `lean` 找不到

说明 Lean 4 或 Elan 没有正确安装，或者没有把对应命令加入 PATH。先确认：

```powershell
lean --version
lake --version
```

项目要求 Lean 4.33.1。

### `npm` 找不到

安装 Node.js 20 或更高版本，然后重新打开 PowerShell，再检查：

```powershell
node --version
npm --version
```

### 端口 4173 已经被占用

可以在当前 PowerShell 临时使用其他端口：

```powershell
$env:PORT = '4174'
npm run serve
```

然后打开：

```text
http://127.0.0.1:4174
```

### `git pull --ff-only` 失败

先看本地是否有未提交改动：

```powershell
git status
```

不要立刻使用 `reset --hard`。把改动提交到功能分支，或者按照本文“有本地改动时如何同步”处理。

## 8. 不要提交的文件

以下文件或目录属于本地构建、依赖或生成物：

```text
.lake/
node_modules/
frontend/graph.json
.server*.log
```

它们已经写入 `.gitignore`。`frontend/layout.json` 是项目中保留的参考布局文件，只有在确认重新生成确实必要时才修改并提交。

## 9. 最小工作检查清单

开始开发：

```powershell
git switch main
git pull --ff-only origin main
git switch -c feature/<名字>-<主题>
```

提交前：

```powershell
npm run check
git status
git diff
```

推送：

```powershell
git add <实际修改的文件>
git commit -m "describe the change"
git push -u origin feature/<名字>-<主题>
```
