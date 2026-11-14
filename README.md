# github-core-clone-01 — Deterministic In-Memory Git Forge (`verssx`)

A zero-dependency GitHub-compatible server implemented in `app.ts` using only Node built-in modules (`node:http`, `node:crypto`, and `node:zlib`). No external `git` binary, no network requests, and no external packages are used.

## Architecture & Performance Optimizations

1. **Single-Pass Packfile Inflation & Deflate Caching**:
   - `readPack` uses `inflateSync(subarray, { info: true })` and reads `engine.bytesWritten` to advance directly to the next pack entry in O(1) passes per object.
   - `writePack` caches compressed `packEntry` buffers on each `GitObject`, avoiding redundant `deflateSync` calls across repeated fetches and clones.
2. **Content-Addressed Tree & Commit Memoization**:
   - `parseTree` and `parseCommit` memoize parsed structures in `WeakMap<Buffer, ...>` caches.
   - `flattenTree` caches full path-to-blob maps per root `treeOid` in `repo.flatTreeCache`, accelerating three-way merge conflict checks and pull-request file diffs (`diffTrees`, `mergeConflict`, `pullFiles`).
3. **Precomputed & Fingerprint-Cached Smart HTTP Advertisements**:
   - Protocol v2 capability advertisements (`v2Advertisement`) use a preallocated static `Buffer`.
   - Protocol v0 ref advertisements (`v0Advertisement`) are cached in `repo.advCache` keyed by the repository's current ref-state fingerprint.
4. **Protocol Surfaces**:
   - **Git Smart HTTP** (`/{owner}/{repo}.git`): `info/refs`, `git-upload-pack` (protocol v2 `ls-refs` & `fetch` with `shallow`/`deepen`), and `git-receive-pack` (v0 with fast-forward enforcement and `report-status`).
   - **REST v3** (`/api/v3/...`): Repositories, branches, commits, git refs, contents, labels, issues, issue comments, pull requests, and three-way/squash merges.
   - **GraphQL v4** (`POST /api/graphql`): `viewer`, `repository`, `node`, `__type` introspection, cursor-paginated connections, batched queries, and mutations (`createIssue`, `closeIssue`, `createPullRequest`, `mergePullRequest`, `addComment`).
   - **MCP** (`POST /mcp`): Streamable HTTP JSON-RPC 2.0 (`2026-07-28`) exposing `create_repo`, `get_repo`, `create_issue`, `list_issues`, `create_pull_request`, and `merge_pull_request`.
5. **Strict Determinism**:
   - Logical clock seeded from `MAKEFUN_TRIAL_NOW` (or `1735689600`) with monotonic counters starting at zero on each process start.
