// Node HTTP wrapper around the TanStack Start v1 `node-server`-preset
// SSR fetch handler. The preset emits `dist/server/ssr.js` as a Web-Fetch
// module (default export with `.fetch(req)`); this file boots an actual
// node:http listener and bridges Node's req/res to Web Request/Response.
//
// Reads PORT (default 3000) and HOST (default 127.0.0.1) from the env.

import { createServer } from "node:http";
import { Readable } from "node:stream";
import handler from "./ssr.js";

const PORT = Number(process.env.PORT ?? 3000);
const HOST = process.env.HOST ?? "127.0.0.1";

function nodeReqToWebRequest(req) {
  const proto = req.socket.encrypted ? "https" : "http";
  const url = `${proto}://${req.headers.host ?? "localhost"}${req.url}`;
  const headers = new Headers();
  for (const [k, v] of Object.entries(req.headers)) {
    if (Array.isArray(v)) for (const item of v) headers.append(k, item);
    else if (v !== undefined) headers.set(k, v);
  }
  const hasBody = !(req.method === "GET" || req.method === "HEAD");
  const init = { method: req.method, headers };
  if (hasBody) {
    init.body = Readable.toWeb(req);
    init.duplex = "half";
  }
  return new Request(url, init);
}

async function pipeWebResponseToNode(webRes, res) {
  res.statusCode = webRes.status;
  webRes.headers.forEach((value, key) => res.setHeader(key, value));
  if (webRes.body) {
    Readable.fromWeb(webRes.body).pipe(res);
  } else {
    res.end();
  }
}

const server = createServer(async (req, res) => {
  try {
    const webReq = nodeReqToWebRequest(req);
    const webRes = await handler.fetch(webReq);
    await pipeWebResponseToNode(webRes, res);
  } catch (err) {
    console.error("[frontend] handler error:", err);
    if (!res.headersSent) {
      res.statusCode = 500;
      res.setHeader("content-type", "text/plain");
    }
    res.end("Internal Server Error");
  }
});

server.listen(PORT, HOST, () => {
  console.log(`[frontend] SSR listening on ${HOST}:${PORT}`);
});

for (const sig of ["SIGTERM", "SIGINT"]) {
  process.on(sig, () => {
    console.log(`[frontend] received ${sig}, shutting down`);
    server.close(() => process.exit(0));
    setTimeout(() => process.exit(1), 5000).unref();
  });
}
