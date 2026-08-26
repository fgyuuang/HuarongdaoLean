@echo off
setlocal EnableExtensions

cd /d "%~dp0"
title HuarongdaoLean local server

echo [HuarongdaoLean] Project root: %CD%
echo [HuarongdaoLean] Checking Node.js and Lean...

where node >nul 2>&1
if errorlevel 1 (
  echo [ERROR] Node.js was not found in PATH.
  echo         Install Node.js 20 or newer, then run this script again.
  pause
  exit /b 1
)

where lake >nul 2>&1
if errorlevel 1 (
  echo [ERROR] Lean Lake was not found in PATH.
  echo         Install elan/Lean 4.33.1, then run this script again.
  pause
  exit /b 1
)

if not exist "node_modules\3d-force-graph" (
  echo [HuarongdaoLean] node_modules is incomplete; installing npm dependencies...
  call npm ci
  if errorlevel 1 (
    echo [ERROR] npm ci failed.
    pause
    exit /b 1
  )
)

if not exist ".lake\build\bin\solve-puzzle.exe" (
  echo [HuarongdaoLean] Lean solver is missing; building the project...
  call lake build
  if errorlevel 1 (
    echo [ERROR] lake build failed.
    pause
    exit /b 1
  )
)

if not exist "frontend\graph.json" (
  echo [HuarongdaoLean] Classic graph export is missing; exporting it now...
  call lake exe export-graph frontend/graph.json
  if errorlevel 1 (
    echo [ERROR] Classic graph export failed.
    pause
    exit /b 1
  )
)

for /f "tokens=5" %%P in ('netstat -ano ^| findstr /R /C:":4173 .*LISTENING"') do set "SERVER_PID=%%P"
if defined SERVER_PID (
  echo [HuarongdaoLean] Port 4173 is already in use by PID %SERVER_PID%.
  echo [HuarongdaoLean] Opening the existing local server.
) else (
  echo [HuarongdaoLean] Starting local server at http://127.0.0.1:4173 ...
  start "HuarongdaoLean server" /D "%CD%" node scripts\serve.mjs
  timeout /t 2 /nobreak >nul
)

echo [HuarongdaoLean] Opening the puzzle laboratory...
start "" "http://127.0.0.1:4173/?mode=lab"
echo [HuarongdaoLean] Ready. Keep the server window open while using the app.
exit /b 0
