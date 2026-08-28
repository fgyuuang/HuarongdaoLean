[CmdletBinding()]
param()

$ErrorActionPreference = 'Stop'

$root = git rev-parse --show-toplevel
if ($LASTEXITCODE -ne 0) {
  throw 'Run this script inside the HuarongdaoLean Git repository.'
}

Set-Location -LiteralPath $root

git config --local pull.ff only
git config --local fetch.prune true
git config --local push.default simple
git config --local core.hooksPath .githooks

Write-Host 'Configured repository-local collaboration settings:'
Write-Host '  pull.ff = only'
Write-Host '  fetch.prune = true'
Write-Host '  push.default = simple'
Write-Host '  core.hooksPath = .githooks'
Write-Host ''
Write-Host 'Direct pushes to main are now blocked by the local pre-push hook.'
