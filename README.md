# github-core-clone-01 — Ultra-Low Latency HTTP/2 & Git Smart-HTTP In-Memory Engine

Dedicated in-memory GitHub-compatible git forge engineered by @verssx for make.fun.

## Core Features & Protocol Coverage
- **Git Smart HTTP**: Full Upload-Pack protocol v2 and Receive-Pack protocol v0.
- **REST API v3**: Repositories, issues, comments, labels, pull-requests, commits, git refs, and tree diffs.
- **GraphQL v4**: Cursor-paginated queries, viewer context, issue/PR mutations, schema introspection.
- **MCP Server**: Fast JSON-RPC 2.0 endpoints under `/mcp`.
- **Zero Outside Dependencies**: Pure Node.js built-ins (`node:http`, `node:net`, `node:crypto`, `node:zlib`).
- **Engine Optimization**: Low-latency http architecture with zero-copy stream parsing and object memoization.
