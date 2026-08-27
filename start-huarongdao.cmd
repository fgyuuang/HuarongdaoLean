@echo off
setlocal EnableExtensions

cd /d "%~dp0"
title HuarongdaoLean local server
set "APP_URL=http://127.0.0.1:4173/"

echo [HuarongdaoLean] Project root: %CD%
echo [HuarongdaoLean] Checking prerequisites...

where node >nul 2>&1
if errorlevel 1 (
  echo [ERROR] Node.js was not found in PATH.
  echo         Install Node.js 20 or newer, then run this script again.
  pause
  exit /b 1
)

if not exist "node_modules\3d-force-graph" (
  where npm >nul 2>&1
  if errorlevel 1 (
    echo [ERROR] npm was not found in PATH.
    echo         Install Node.js 20 or newer, then run this script again.
    pause
    exit /b 1
  )
  echo [HuarongdaoLean] node_modules is incomplete; installing npm dependencies...
  call npm ci
  if errorlevel 1 (
    echo [ERROR] npm ci failed.
    pause
    exit /b 1
  )
)

if not exist ".lake\build\bin\solve-puzzle.exe" (
  call :require_lake || exit /b 1
  echo [HuarongdaoLean] Lean solver is missing; building the project...
  call lake build
  if errorlevel 1 (
    echo [ERROR] lake build failed.
    pause
    exit /b 1
  )
)

if not exist "frontend\graph.json" (
  call :require_lake || exit /b 1
  echo [HuarongdaoLean] Classic graph export is missing; exporting it now...
  call lake exe export-graph frontend/graph.json
  if errorlevel 1 (
    echo [ERROR] Classic graph export failed.
    pause
    exit /b 1
  )
)

call :server_ready
if not errorlevel 1 (
  echo [HuarongdaoLean] The local server is already running.
  goto open_browser
)

for /f "tokens=5" %%P in ('netstat -ano ^| findstr /R /C:"127.0.0.1:4173 .*LISTENING"') do set "SERVER_PID=%%P"
if defined SERVER_PID (
  echo [ERROR] Port 4173 is occupied by another program ^(PID %SERVER_PID%^).
  echo         Stop that program, then run this script again.
  pause
  exit /b 1
)

echo [HuarongdaoLean] Starting local server at %APP_URL% ...
start "HuarongdaoLean server" /D "%CD%" node scripts\serve.mjs

for /L %%I in (1,1,20) do (
  call :server_ready
  if not errorlevel 1 goto server_started
  >nul ping 127.0.0.1 -n 2
)

echo [ERROR] The local server did not become ready.
echo         Check the HuarongdaoLean server window for details.
pause
exit /b 1

:server_started
echo [HuarongdaoLean] Local server is ready.

:open_browser
echo [HuarongdaoLean] Opening the puzzle laboratory...
start "" "%APP_URL%?mode=lab"
echo [HuarongdaoLean] Ready. Keep the server window open while using the app.
exit /b 0

:require_lake
where lake >nul 2>&1
if not errorlevel 1 exit /b 0
echo [ERROR] Lean Lake was not found in PATH.
echo         Install elan/Lean 4.33.1, then run this script again.
pause
exit /b 1

:server_ready
powershell -NoProfile -Command ^
  "try { $result = Invoke-RestMethod -Uri '%APP_URL%api/health' -TimeoutSec 1; if ($result.app -eq 'huarongdao-lean-visualizer' -and $result.status -eq 'ok') { exit 0 } } catch {}; try { $page = Invoke-WebRequest -UseBasicParsing -Uri '%APP_URL%' -TimeoutSec 1; if ($page.Content -match 'id=.mode-lab.' -and $page.Content -match 'id=.board.') { exit 0 } } catch {}; exit 1" >nul 2>&1
exit /b %errorlevel%
