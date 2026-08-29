const sourcePathPattern = /^Huarongdao\/(?:[A-Za-z0-9_-]+\/)*[A-Za-z0-9_-]+\.lean$/u;

function json(payload, status = 200) {
  return new Response(JSON.stringify(payload), {
    status,
    headers: {
      'content-type': 'application/json; charset=utf-8',
      'cache-control': 'no-store',
    },
  });
}

async function sourceResponse(request, env) {
  if (!['GET', 'HEAD'].includes(request.method)) return json({ error: { code: 'METHOD_NOT_ALLOWED' } }, 405);

  let requested;
  try {
    requested = decodeURIComponent(new URL(request.url).searchParams.get('path') || '');
  } catch {
    return json({ error: { code: 'INVALID_SOURCE_PATH', message: 'source path is not valid' } }, 400);
  }

  if (!sourcePathPattern.test(requested)) {
    return json({ error: { code: 'SOURCE_PATH_NOT_ALLOWED', message: 'source path is not allowed' } }, 404);
  }

  const assetUrl = new URL(request.url);
  assetUrl.pathname = `/source/${requested}`;
  assetUrl.search = '';
  const response = await env.ASSETS.fetch(new Request(assetUrl, request));
  if (response.status === 404) {
    return json({ error: { code: 'SOURCE_NOT_FOUND', message: 'source file not found' } }, 404);
  }
  return response;
}

export default {
  async fetch(request, env) {
    const url = new URL(request.url);

    if (request.method === 'GET' && url.pathname === '/api/health') {
      return json({ app: 'huarongdao-lean-visualizer', status: 'ok', deployment: 'sites' });
    }

    if (url.pathname === '/api/source') {
      return sourceResponse(request, env);
    }

    if (url.pathname === '/api/puzzle/solve') {
      return json({
        error: {
          code: 'LOCAL_LEAN_SOLVER_UNAVAILABLE',
          message: '站点部署不包含本机 Lean 求解器；请在本地运行关卡实验室。',
        },
      }, 501);
    }

    const response = await env.ASSETS.fetch(request);
    const acceptsHtml = request.headers.get('accept')?.includes('text/html');
    if (response.status !== 404 || !acceptsHtml || !['GET', 'HEAD'].includes(request.method)) {
      return response;
    }

    const indexUrl = new URL(request.url);
    indexUrl.pathname = '/index.html';
    indexUrl.search = '';
    return env.ASSETS.fetch(new Request(indexUrl, request));
  },
};
