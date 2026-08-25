import { createServer } from 'node:http';
import { readFile, stat } from 'node:fs/promises';
import { execFile } from 'node:child_process';
import { extname, join, normalize } from 'node:path';

const projectRoot = new URL('../', import.meta.url).pathname.replace(/^\/([A-Za-z]:)/, '$1');
const root = normalize(join(projectRoot, 'frontend'));
const solver = normalize(join(projectRoot, '.lake', 'build', 'bin', 'solve-puzzle.exe'));
const port = Number(process.env.PORT || 4173);
const types = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8', '.css': 'text/css; charset=utf-8', '.json': 'application/json; charset=utf-8' };

function sendJson(response, status, payload) {
  response.writeHead(status, { 'content-type': 'application/json; charset=utf-8', 'cache-control': 'no-store' });
  response.end(JSON.stringify(payload));
}

async function readJson(request) {
  if (!String(request.headers['content-type'] || '').startsWith('application/json')) throw Object.assign(new Error('Content-Type must be application/json'), { status: 415 });
  const chunks = []; let size = 0;
  for await (const chunk of request) {
    size += chunk.length;
    if (size > 1024 * 1024) throw Object.assign(new Error('Request body exceeds 1 MB'), { status: 413 });
    chunks.push(chunk);
  }
  try { return JSON.parse(Buffer.concat(chunks).toString('utf8')); }
  catch { throw Object.assign(new Error('Request body is not valid JSON'), { status: 400 }); }
}

function integer(value, name, min, max) {
  if (!Number.isInteger(value) || value < min || value > max) throw Object.assign(new Error(name + ' must be an integer in [' + min + ', ' + max + ']'), { status: 400 });
  return value;
}

function solverArgs(payload) {
  const width = integer(payload?.board?.width, 'board.width', 1, 16);
  const height = integer(payload?.board?.height, 'board.height', 1, 16);
  if (!Array.isArray(payload.pieces) || payload.pieces.length < 1 || payload.pieces.length > 64) throw Object.assign(new Error('pieces must contain 1 to 64 numbered blocks'), { status: 400 });
  const maxStates = integer(payload.options?.maxStates ?? 100000, 'options.maxStates', 1, 2000000);
  const maxDepth = integer(payload.options?.maxDepth ?? 500, 'options.maxDepth', 0, 10000);
  const args = [width, height, maxStates, maxDepth, payload.pieces.length].map(String);
  const strategy = payload.options?.strategy ?? 'astar';
  if (strategy !== 'astar' && strategy !== 'bfs') throw Object.assign(new Error('options.strategy must be astar or bfs'), { status: 400 });
  payload.pieces.forEach((piece, index) => {
    if (piece.id !== index + 1) throw Object.assign(new Error('piece ids must be consecutive integers 1, 2, 3, ...'), { status: 400 });
    const w = integer(piece.width, 'piece ' + piece.id + ' width', 1, width);
    const h = integer(piece.height, 'piece ' + piece.id + ' height', 1, height);
    const x = integer(piece.x, 'piece ' + piece.id + ' x', 0, width - 1);
    const y = integer(piece.y, 'piece ' + piece.id + ' y', 0, height - 1);
    let gx = '*', gy = '*';
    if (piece.goalX != null || piece.goalY != null) {
      gx = integer(piece.goalX, 'piece ' + piece.id + ' goalX', 0, width - 1);
      gy = integer(piece.goalY, 'piece ' + piece.id + ' goalY', 0, height - 1);
    }
    args.push(String(w), String(h), String(x), String(y), String(gx), String(gy));
  });
  args.push(strategy);
  return { args, timeoutMs: integer(payload.options?.timeoutMs ?? 120000, 'options.timeoutMs', 1000, 600000) };
}

function runSolver(args, timeoutMs) {
  return new Promise((resolve, reject) => execFile(solver, args, { timeout: timeoutMs, maxBuffer: 32 * 1024 * 1024, windowsHide: true }, (error, stdout, stderr) => {
    if (error) return reject(Object.assign(new Error(error.killed ? 'Lean solver timed out' : (stderr || error.message)), { status: error.killed ? 408 : 500 }));
    try { resolve(JSON.parse(stdout)); }
    catch { reject(Object.assign(new Error('Lean solver returned invalid JSON'), { status: 500 })); }
  }));
}

createServer(async (request, response) => {
  try {
    const url = new URL(request.url, 'http://localhost');
    if (request.method === 'POST' && url.pathname === '/api/puzzle/solve') {
      const payload = await readJson(request);
      const { args, timeoutMs } = solverArgs(payload);
      return sendJson(response, 200, await runSolver(args, timeoutMs));
    }
    if (request.method !== 'GET' && request.method !== 'HEAD') return sendJson(response, 405, { error: { code: 'METHOD_NOT_ALLOWED', message: 'Only GET, HEAD and POST /api/puzzle/solve are supported' } });
    const relative = url.pathname === '/' ? 'index.html' : decodeURIComponent(url.pathname.slice(1));
    const file = normalize(join(root, relative));
    if (!file.startsWith(root)) throw Object.assign(new Error('invalid path'), { status: 404 });
    const info = await stat(file);
    if (!info.isFile()) throw Object.assign(new Error('not a file'), { status: 404 });
    response.writeHead(200, { 'content-type': types[extname(file)] || 'application/octet-stream', 'cache-control': 'no-cache' });
    if (request.method === 'HEAD') return response.end();
    response.end(await readFile(file));
  } catch (error) {
    sendJson(response, error.status || 404, { error: { code: error.status === 408 ? 'SOLVER_TIMEOUT' : error.status >= 500 ? 'SOLVER_FAILURE' : 'INVALID_REQUEST', message: error.message || 'Not found' } });
  }
}).listen(port, '127.0.0.1', () => console.log('Huarongdao visualizer: http://127.0.0.1:' + port));
