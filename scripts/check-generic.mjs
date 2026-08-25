import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { resolve } from 'node:path';

const run = promisify(execFile), solver = resolve('.lake/build/bin/solve-puzzle.exe');
async function solve(args) { const { stdout } = await run(solver, args.map(String)); return JSON.parse(stdout); }
const cases = {
  solved: [3,2,1000,20,2, 1,1,0,0,2,0, 1,1,1,0,'*','*'],
  invalid: [2,2,100,10,2, 1,1,0,0,1,1, 1,1,0,0,'*','*'],
  limit: [3,2,1,0,2, 1,1,0,0,2,0, 1,1,1,0,'*','*'],
  unreachable: [2,1,100,10,2, 1,1,0,0,1,0, 1,1,1,0,'*','*']
};
for (const [expected, args] of Object.entries(cases)) {
  const result = await solve(args);
  if (result.status !== expected) throw new Error(expected + ': received ' + result.status);
  if (expected === 'solved' && (!result.proof?.verified || result.stats.shortestLength !== 3)) throw new Error('solved certificate mismatch');
  if (expected === 'solved' && (result.schemaVersion !== '2' || !result.graph?.edgesVerified)) throw new Error('graph certificate mismatch');
  if (expected === 'solved' && (result.graph.nodes.length !== 30 || result.graph.edges.length !== 112 || !result.graph.complete)) throw new Error('graph enumeration mismatch');
  if (expected === 'limit' && result.graph.complete) throw new Error('limited graph marked complete');
  console.log(expected + ': ok');
}

const astar = await solve([...cases.solved, 'astar']);
if (astar.status !== 'solved' || !astar.proof?.verified) throw new Error('astar solution certificate mismatch');
if (astar.stats.algorithm !== 'astar' || astar.graph.kind !== 'solution-subgraph' || astar.graph.complete || astar.graph.truncated) throw new Error('astar graph semantics mismatch');
if (astar.graph.nodes.length >= 30) throw new Error('astar did not reduce the tiny search space');
console.log('astar: ok (' + astar.graph.nodes.length + ' states)');
