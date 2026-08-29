import assert from 'node:assert/strict';
import { access } from 'node:fs/promises';
import test from 'node:test';
import worker from '../worker/index.js';

function assets(fetchImpl) {
  return { ASSETS: { fetch: fetchImpl } };
}

test('serves the health endpoint', async () => {
  const response = await worker.fetch(new Request('https://example.test/api/health'), assets(async () => new Response('unused')));
  assert.equal(response.status, 200);
  assert.deepEqual(await response.json(), {
    app: 'huarongdao-lean-visualizer',
    status: 'ok',
    deployment: 'sites',
  });
});

test('maps the source API to a packaged Lean file', async () => {
  const calls = [];
  const response = await worker.fetch(
    new Request('https://example.test/api/source?path=Huarongdao%2FModel.lean'),
    assets(async request => {
      calls.push(new URL(request.url).pathname);
      return new Response('structure State', { status: 200 });
    }),
  );

  assert.equal(response.status, 200);
  assert.deepEqual(calls, ['/source/Huarongdao/Model.lean']);
  assert.equal(await response.text(), 'structure State');
});

test('rejects source traversal and unsupported files', async () => {
  for (const path of ['../Model.lean', 'Huarongdao/Model.olean', 'Huarongdao/%2E%2E%2FModel.lean']) {
    const response = await worker.fetch(
      new Request(`https://example.test/api/source?path=${encodeURIComponent(path)}`),
      assets(async () => new Response('should not be called')),
    );
    assert.equal(response.status, 404);
  }
});

test('returns a clear status for the local-only solver endpoint', async () => {
  const response = await worker.fetch(
    new Request('https://example.test/api/puzzle/solve', { method: 'POST' }),
    assets(async () => new Response('unused')),
  );
  assert.equal(response.status, 501);
  assert.equal((await response.json()).error.code, 'LOCAL_LEAN_SOLVER_UNAVAILABLE');
});

test('falls back to index.html for unknown app routes', async () => {
  const calls = [];
  const response = await worker.fetch(
    new Request('https://example.test/formalization', { headers: { accept: 'text/html' } }),
    assets(async request => {
      const pathname = new URL(request.url).pathname;
      calls.push(pathname);
      return new Response(pathname === '/index.html' ? 'app' : 'missing', {
        status: pathname === '/index.html' ? 200 : 404,
      });
    }),
  );
  assert.equal(response.status, 200);
  assert.deepEqual(calls, ['/formalization', '/index.html']);
});

test('emits the files required by Sites packaging', async () => {
  await access(new URL('../dist/client/index.html', import.meta.url));
  await access(new URL('../dist/server/index.js', import.meta.url));
  await access(new URL('../dist/.openai/hosting.json', import.meta.url));
});
