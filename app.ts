// github-core-clone-01 entry: a GitHub-compatible forge in one file.
//
// Surfaces: git smart HTTP (protocol v2 upload-pack, v0 receive-pack), REST v3
// (/api/v3/...), GraphQL v4 (POST /api/graphql) and MCP over streamable HTTP
// (POST /mcp). Only node:http, node:crypto and node:zlib are used: no
// dependencies, no git binary, no network, no model call.
//
// Determinism (replay must be byte-identical): no Date.now(), no Math.random(),
// no unseeded ids. Every id and number comes from counters that start at 0 on
// each process start, and every timestamp comes from a logical clock seeded by
// MAKEFUN_TRIAL_NOW when the trial sets it, otherwise from a fixed base epoch
// plus a tick counter. The scenario's viewer (the fixed contest seed) is
// adaiversen (id 1000); every repository created through POST /user/repos
// belongs to that login, so a path under any other owner is a 404, never a 403.

import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

// ---------------------------------------------------------------- constants

const JSON_TYPE = 'application/json; charset=utf-8';
const ZERO_OID = '0'.repeat(40);
const VIEWER_LOGIN = 'adaiversen';
const VIEWER_ID = 1000;
const VIEWER_NAME = 'ada iversen';
const VIEWER_EMAIL = 'adaiversen@example.invalid';
const VIEWER_IDENTITY = `${VIEWER_NAME} <${VIEWER_EMAIL}>`;
const DEFAULT_BRANCH = 'main';
const FORGE_AGENT = 'makefun-forge/1.0';
const MCP_NAME = 'github-core-clone';
const MCP_VERSION = '1.0.0';
const SCENARIO_EPOCH_SEC = 1_735_689_600; // 2025-01-01T00:00:00Z
const DEFAULT_LABELS: ReadonlyArray<readonly [string, string]> = [
  ['bug', 'd73a4a'],
  ['enhancement', 'a2eeef'],
  ['documentation', '0075ca'],
  ['question', 'd876e3'],
  ['good first issue', '7057ff'],
  ['help wanted', '008672'],
];

// ---------------------------------------------------------------- deterministic clock and counters

/** The trial's fixed timestamp when it sets one, else the scenario epoch. */
function trialBaseSec(): number {
  const raw = process.env.MAKEFUN_TRIAL_NOW ?? '';
  if (raw !== '') {
    const asNumber = Number(raw);
    if (Number.isFinite(asNumber) && asNumber > 0) return Math.trunc(asNumber);
    const parsed = Date.parse(raw);
    if (Number.isFinite(parsed)) return Math.trunc(parsed / 1000);
  }
  return SCENARIO_EPOCH_SEC;
}

const CLOCK_BASE_SEC = trialBaseSec();
let clockTick = 0;
/** Next logical second: deterministic, one tick per timestamp taken. */
function nowSec(): number {
  return CLOCK_BASE_SEC + clockTick++;
}
/** ISO timestamp from the logical clock. */
function nowIso(): string {
  return new Date(nowSec() * 1000).toISOString();
}

let requestCounter = 0;
let repoDbIdCounter = 5000;
let issueIdCounter = 1;
let commentIdCounter = 1;
let globalSeq = 0;

/** A non-empty request id, deterministic per process start. */
function nextRequestId(): string {
  requestCounter += 1;
  return `req-${requestCounter}`;
}

// ---------------------------------------------------------------- small utilities

function sha1Hex(data: Buffer): string {
  return createHash('sha1').update(data).digest('hex');
}

function isOid(value: unknown): value is string {
  return typeof value === 'string' && /^[0-9a-f]{40}$/.test(value);
}

function b64encode(text: string | Buffer): string {
  return Buffer.isBuffer(text) ? text.toString('base64') : Buffer.from(text, 'utf8').toString('base64');
}

function b64decode(text: string): Buffer {
  return Buffer.from(text, 'base64');
}

function b64urlEncode(text: string): string {
  return Buffer.from(text, 'utf8').toString('base64url');
}

function b64urlDecode(text: string): string | null {
  try {
    return Buffer.from(text, 'base64url').toString('utf8');
  } catch {
    return null;
  }
}

/** Split a path into segments, dropping empty ones. */
function pathSegments(path: string): string[] {
  return path.split('/').filter((segment) => segment !== '');
}

/** Compare two strings the way git compares tree entry names (dirs as name + '/'). */
function treeNameCompare(aName: string, aIsDir: boolean, bName: string, bIsDir: boolean): number {
  const a = aIsDir ? `${aName}/` : aName;
  const b = bIsDir ? `${bName}/` : bName;
  return a < b ? -1 : a > b ? 1 : 0;
}

// ---------------------------------------------------------------- git objects

type ObjType = 'commit' | 'tree' | 'blob' | 'tag';

interface GitObject {
  type: ObjType;
  data: Buffer;
  packEntry?: Buffer;
}

function hashObject(type: ObjType, data: Buffer): string {
  const header = Buffer.from(`${type} ${data.length}\0`, 'utf8');
  return sha1Hex(Buffer.concat([header, data]));
}

interface TreeEntry {
  mode: string;
  name: string;
  oid: string;
}

const treeCache = new WeakMap<Buffer, TreeEntry[]>();

function parseTree(data: Buffer): TreeEntry[] {
  const cached = treeCache.get(data);
  if (cached !== undefined) return cached;
  const entries: TreeEntry[] = [];
  let offset = 0;
  while (offset < data.length) {
    const space = data.indexOf(0x20, offset);
    if (space < 0) break;
    const mode = data.subarray(offset, space).toString('utf8');
    const nul = data.indexOf(0x00, space + 1);
    if (nul < 0) break;
    const name = data.subarray(space + 1, nul).toString('utf8');
    const oid = data.subarray(nul + 1, nul + 21).toString('hex');
    entries.push({ mode, name, oid });
    offset = nul + 21;
  }
  treeCache.set(data, entries);
  return entries;
}

function buildTree(entries: readonly TreeEntry[]): Buffer {
  const sorted = [...entries].sort((a, b) => treeNameCompare(a.name, a.mode === '40000', b.name, b.mode === '40000'));
  const parts: Buffer[] = [];
  for (const entry of sorted) {
    parts.push(Buffer.from(`${entry.mode} ${entry.name}\0`, 'utf8'));
    parts.push(Buffer.from(entry.oid, 'hex'));
  }
  return Buffer.concat(parts);
}

interface CommitView {
  tree: string;
  parents: string[];
  author: string;
  committer: string;
  message: string;
}

const commitCache = new WeakMap<Buffer, CommitView>();

function parseCommit(data: Buffer): CommitView {
  const cached = commitCache.get(data);
  if (cached !== undefined) return cached;
  const text = data.toString('utf8');
  const split = text.indexOf('\n\n');
  const header = split < 0 ? text : text.slice(0, split);
  const message = split < 0 ? '' : text.slice(split + 2);
  let tree = '';
  const parents: string[] = [];
  let author = '';
  let committer = '';
  for (const line of header.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
    else if (line.startsWith('author ')) author = line.slice(7);
    else if (line.startsWith('committer ')) committer = line.slice(10);
  }
  const view: CommitView = { tree, parents, author, committer, message };
  commitCache.set(data, view);
  return view;
}

function buildCommit(fields: { tree: string; parents: readonly string[]; message: string; author: string; committer: string; timestamp: number }): Buffer {
  let text = `tree ${fields.tree}\n`;
  for (const parent of fields.parents) text += `parent ${parent}\n`;
  text += `author ${fields.author} ${fields.timestamp} +0000\n`;
  text += `committer ${fields.committer} ${fields.timestamp} +0000\n`;
  text += `\n${fields.message}`;
  return Buffer.from(text, 'utf8');
}

interface TagView {
  object: string;
  type: string;
  tag: string;
  tagger: string;
  message: string;
}

function parseTag(data: Buffer): TagView {
  const text = data.toString('utf8');
  const split = text.indexOf('\n\n');
  const header = split < 0 ? text : text.slice(0, split);
  const message = split < 0 ? '' : text.slice(split + 2);
  let object = '';
  let type = '';
  let tag = '';
  let tagger = '';
  for (const line of header.split('\n')) {
    if (line.startsWith('object ')) object = line.slice(7).trim();
    else if (line.startsWith('type ')) type = line.slice(5).trim();
    else if (line.startsWith('tag ')) tag = line.slice(4).trim();
    else if (line.startsWith('tagger ')) tagger = line.slice(7);
  }
  return { object, type, tag, tagger, message };
}

function buildTag(fields: { object: string; type: string; tag: string; message: string; tagger: string; timestamp: number }): Buffer {
  const text = `object ${fields.object}\ntype ${fields.type}\ntag ${fields.tag}\ntagger ${fields.tagger} ${fields.timestamp} +0000\n\n${fields.message}`;
  return Buffer.from(text, 'utf8');
}

/** All objects reachable from `tips` (commits, trees, blobs, tags), by oid. */
function collectReachable(tips: Iterable<string>, lookup: (oid: string) => GitObject | undefined): Set<string> {
  const seen = new Set<string>();
  const stack = [...tips];
  while (stack.length > 0) {
    const oid = stack.pop()!;
    if (seen.has(oid)) continue;
    const object = lookup(oid);
    if (object === undefined) continue;
    seen.add(oid);
    if (object.type === 'commit') {
      const view = parseCommit(object.data);
      stack.push(view.tree);
      for (const parent of view.parents) stack.push(parent);
    } else if (object.type === 'tree') {
      for (const entry of parseTree(object.data)) {
        if (entry.mode !== '160000') stack.push(entry.oid);
      }
    } else if (object.type === 'tag') {
      stack.push(parseTag(object.data).object);
    }
  }
  return seen;
}

// ---------------------------------------------------------------- pack files

const PACK_TYPE_CODES: Record<ObjType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const PACK_CODE_TYPES: Record<number, ObjType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

function writePackObjectHeader(type: ObjType, size: number): Buffer {
  const typeCode = PACK_TYPE_CODES[type];
  const bytes: number[] = [];
  let remaining = size;
  let first = (typeCode << 4) | (remaining & 0x0f);
  remaining >>= 4;
  if (remaining > 0) first |= 0x80;
  bytes.push(first);
  while (remaining > 0) {
    let next = remaining & 0x7f;
    remaining >>= 7;
    if (remaining > 0) next |= 0x80;
    bytes.push(next);
  }
  return Buffer.from(bytes);
}

/** A pack v2 with plain (non-delta) objects, in the given order. */
function writePack(objects: readonly GitObject[]): Buffer {
  const chunks: Buffer[] = [];
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(objects.length, 8);
  chunks.push(header);
  for (const object of objects) {
    if (object.packEntry === undefined) {
      object.packEntry = Buffer.concat([writePackObjectHeader(object.type, object.data.length), deflateSync(object.data)]);
    }
    chunks.push(object.packEntry);
  }
  const trailer = sha1Hex(Buffer.concat(chunks));
  chunks.push(Buffer.from(trailer, 'hex'));
  return Buffer.concat(chunks);
}

function readVarintSize(buffer: Buffer, start: number): { size: number; next: number; first: number } {
  let byte = buffer[start]!;
  const first = (byte >> 4) & 0x07;
  let size = byte & 0x0f;
  let shift = 4;
  let next = start + 1;
  while ((byte & 0x80) !== 0) {
    byte = buffer[next]!;
    size |= (byte & 0x7f) << shift;
    shift += 7;
    next += 1;
  }
  return { size, next, first };
}

/** Parse a pack v2 of plain objects. Throws on a malformed pack or a delta entry. */
function readPack(pack: Buffer): GitObject[] {
  if (pack.length < 12 || pack.subarray(0, 4).toString('ascii') !== 'PACK') {
    throw new Error('not a pack file');
  }
  const version = pack.readUInt32BE(4);
  if (version !== 2 && version !== 3) throw new Error(`unsupported pack version ${version}`);
  const count = pack.readUInt32BE(8);
  const objects: GitObject[] = [];
  let offset = 12;
  for (let index = 0; index < count; index += 1) {
    const { size, next, first } = readVarintSize(pack, offset);
    const type = PACK_CODE_TYPES[first];
    if (type === undefined) throw new Error(`unsupported pack object type ${first} (deltas are not accepted)`);
    offset = next;
    // One inflate per object: inflateSync ignores bytes past the stream's end, and with
    // info:true the engine reports exactly how many compressed bytes the stream consumed
    // (bytesWritten), so the next object starts at offset + bytesWritten. This replaces
    // the old binary search over the tail (~9 inflates per object, ~9x slower); the
    // binary search stays only as a fallback when bytesWritten is unavailable.
    const { buffer: inflated, engine } = inflateSync(pack.subarray(offset), { info: true });
    if (inflated.length !== size) throw new Error('pack object size mismatch');
    const consumed = (engine as unknown as { bytesWritten?: unknown }).bytesWritten;
    offset += typeof consumed === 'number' && Number.isFinite(consumed) && consumed > 0
      ? consumed
      : packDeflateEnd(pack, offset);
    objects.push({ type, data: Buffer.from(inflated) });
  }
  return objects;
}

/**
 * Fallback for readPack when the inflate engine does not report bytesWritten:
 * the offset just past the zlib stream that starts at `start` (deflate stream end),
 * found by binary search (inflate of pack[start..mid] succeeds iff mid >= end).
 */
function packDeflateEnd(pack: Buffer, start: number): number {
  let low = start;
  let high = pack.length;
  // Invariant: inflate of pack[start..mid] succeeds iff mid >= end. Binary search the end.
  const tryInflate = (end: number): boolean => {
    try {
      inflateSync(pack.subarray(start, end));
      return true;
    } catch {
      return false;
    }
  };
  if (!tryInflate(high)) throw new Error('truncated pack object');
  while (low + 1 < high) {
    const mid = (low + high) >> 1;
    if (tryInflate(mid)) high = mid;
    else low = mid;
  }
  return high;
}

// ---------------------------------------------------------------- pkt-lines

const HEX_DIGITS = '0123456789abcdef';

function pktLine(payload: string | Buffer): Buffer {
  const body = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const length = body.length + 4;
  const out = Buffer.allocUnsafe(length);
  out.writeUInt8(HEX_DIGITS[(length >> 12) & 0xf]!.charCodeAt(0), 0);
  out.writeUInt8(HEX_DIGITS[(length >> 8) & 0xf]!.charCodeAt(0), 1);
  out.writeUInt8(HEX_DIGITS[(length >> 4) & 0xf]!.charCodeAt(0), 2);
  out.writeUInt8(HEX_DIGITS[length & 0xf]!.charCodeAt(0), 3);
  body.copy(out, 4);
  return out;
}

const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');

type PktKind = 'data' | 'flush' | 'delim' | 'end';

interface PktPacket {
  kind: PktKind;
  payload: Buffer;
}

/** Decode a whole pkt-line stream. Throws on a malformed length prefix. */
function decodePktLines(buffer: Buffer): PktPacket[] {
  const packets: PktPacket[] = [];
  let offset = 0;
  while (offset < buffer.length) {
    if (offset + 4 > buffer.length) throw new Error('truncated pkt-line length');
    const length = parseInt(buffer.subarray(offset, offset + 4).toString('ascii'), 16);
    if (!Number.isFinite(length) || length < 0) throw new Error('bad pkt-line length');
    if (length === 0) {
      packets.push({ kind: 'flush', payload: Buffer.alloc(0) });
      offset += 4;
      continue;
    }
    if (length === 1) {
      packets.push({ kind: 'delim', payload: Buffer.alloc(0) });
      offset += 4;
      continue;
    }
    if (length === 2) {
      packets.push({ kind: 'end', payload: Buffer.alloc(0) });
      offset += 4;
      continue;
    }
    if (offset + length > buffer.length) throw new Error('truncated pkt-line payload');
    packets.push({ kind: 'data', payload: Buffer.from(buffer.subarray(offset + 4, offset + length)) });
    offset += length;
  }
  return packets;
}

/**
 * Parse a request body that is pkt-lines followed by a raw pack: returns the packets
 * up to and including the first flush, plus the bytes after that flush (the pack).
 */
function splitPktLinesAndRest(buffer: Buffer): { packets: PktPacket[]; rest: Buffer } {
  const packets: PktPacket[] = [];
  let offset = 0;
  while (offset < buffer.length) {
    if (offset + 4 > buffer.length) throw new Error('truncated pkt-line length');
    const length = parseInt(buffer.subarray(offset, offset + 4).toString('ascii'), 16);
    if (!Number.isFinite(length) || length < 0) throw new Error('bad pkt-line length');
    if (length === 0) {
      packets.push({ kind: 'flush', payload: Buffer.alloc(0) });
      offset += 4;
      break;
    }
    if (length === 1) {
      packets.push({ kind: 'delim', payload: Buffer.alloc(0) });
      offset += 4;
      continue;
    }
    if (length === 2) {
      packets.push({ kind: 'end', payload: Buffer.alloc(0) });
      offset += 4;
      continue;
    }
    if (offset + length > buffer.length) throw new Error('truncated pkt-line payload');
    packets.push({ kind: 'data', payload: Buffer.from(buffer.subarray(offset + 4, offset + length)) });
    offset += length;
  }
  return { packets, rest: buffer.subarray(offset) };
}

// ---------------------------------------------------------------- store

interface IssueRecord {
  id: number;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  labels: string[];
  createdSeq: number;
  jsonPayload?: Buffer;
}

interface CommentRecord {
  id: number;
  body: string;
  createdSeq: number;
}

interface PullRecord {
  id: number;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  headRef: string;
  baseRef: string;
  merged: boolean;
  mergedAt: string | null;
  mergeCommitSha: string | null;
  createdSeq: number;
}

interface RepoRecord {
  dbId: number;
  owner: string;
  name: string;
  description: string;
  isPrivate: boolean;
  defaultBranch: string;
  createdSeq: number;
  labels: Map<string, string>;
  issues: Map<number, IssueRecord>;
  nextIssueNumber: number;
  comments: Map<number, CommentRecord[]>;
  pulls: Map<number, PullRecord>;
  nextPullNumber: number;
  refs: Map<string, string>;
  objects: Map<string, GitObject>;
  commitSeq: Map<string, number>;
  flatTreeCache: Map<string, Map<string, FlatFile>>;
  advCache: Map<string, Buffer>;
}

class Forge {
  readonly repos = new Map<string, RepoRecord>();
  readonly repoCreationOrder: RepoRecord[] = [];

  key(owner: string, name: string): string {
    return `${owner}/${name}`;
  }

  createRepo(owner: string, name: string, description: string, isPrivate: boolean): RepoRecord {
    const repo: RepoRecord = {
      dbId: repoDbIdCounter++,
      owner,
      name,
      description,
      isPrivate,
      defaultBranch: DEFAULT_BRANCH,
      createdSeq: ++globalSeq,
      labels: new Map(DEFAULT_LABELS.map(([label, color]) => [label, color])),
      issues: new Map(),
      nextIssueNumber: 1,
      comments: new Map(),
      pulls: new Map(),
      nextPullNumber: 1,
      refs: new Map(),
      objects: new Map(),
      commitSeq: new Map(),
      flatTreeCache: new Map(),
      advCache: new Map(),
    };
    this.repos.set(this.key(owner, name), repo);
    this.repoCreationOrder.push(repo);
    return repo;
  }

  getRepo(owner: string, name: string): RepoRecord | undefined {
    return this.repos.get(this.key(owner, name));
  }

  /** All of the viewer's repositories, in creation order. */
  viewerRepos(): RepoRecord[] {
    return this.repoCreationOrder.filter((repo) => repo.owner === VIEWER_LOGIN);
  }
}

function storeObject(repo: RepoRecord, type: ObjType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!repo.objects.has(oid)) {
    repo.objects.set(oid, { type, data });
    if (type === 'commit') repo.commitSeq.set(oid, ++globalSeq);
  }
  return oid;
}

function lookupObject(repo: RepoRecord, oid: string): GitObject | undefined {
  return repo.objects.get(oid);
}

/** Follow annotated tags to their target. Returns the target oid (a commit for our uses). */
function peelToCommit(repo: RepoRecord, oid: string): string {
  let current = oid;
  const seen = new Set<string>();
  while (!seen.has(current)) {
    seen.add(current);
    const object = repo.objects.get(current);
    if (object === undefined || object.type !== 'tag') return current;
    current = parseTag(object.data).object;
  }
  return current;
}

function refTip(repo: RepoRecord, refName: string): string | undefined {
  return repo.refs.get(refName);
}

function branchTip(repo: RepoRecord, branch: string): string | undefined {
  return repo.refs.get(`refs/heads/${branch}`);
}

function headRefName(repo: RepoRecord): string {
  return `refs/heads/${repo.defaultBranch}`;
}

/** The commit at a ref, peeled through tags, or undefined. */
function refCommit(repo: RepoRecord, refName: string): string | undefined {
  const tip = refTip(repo, refName);
  if (tip === undefined) return undefined;
  return peelToCommit(repo, tip);
}

/** All refs of a repo, HEAD first, then sorted by name. */
function sortedRefs(repo: RepoRecord): Array<{ name: string; oid: string }> {
  const entries = [...repo.refs.entries()].map(([name, oid]) => ({ name, oid }));
  entries.sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
  const headName = headRefName(repo);
  const head = entries.find((entry) => entry.name === headName);
  const rest = entries.filter((entry) => entry.name !== headName);
  return head === undefined ? rest : [head, ...rest];
}

// ---------------------------------------------------------------- tree operations

interface FlatFile {
  path: string;
  oid: string;
  mode: string;
}

/** Flatten a tree into path -> file entries (files only, gitlinks skipped). */
function flattenTree(repo: RepoRecord, treeOid: string, prefix = ''): Map<string, FlatFile> {
  if (prefix === '') {
    const cached = repo.flatTreeCache.get(treeOid);
    if (cached !== undefined) return cached;
  }
  const result = new Map<string, FlatFile>();
  const walk = (oid: string, at: string): void => {
    const object = repo.objects.get(oid);
    if (object === undefined || object.type !== 'tree') return;
    for (const entry of parseTree(object.data)) {
      const path = at === '' ? entry.name : `${at}/${entry.name}`;
      if (entry.mode === '40000') {
        walk(entry.oid, path);
      } else if (entry.mode !== '160000') {
        result.set(path, { path, oid: entry.oid, mode: entry.mode });
      }
    }
  };
  walk(treeOid, prefix);
  if (prefix === '') repo.flatTreeCache.set(treeOid, result);
  return result;
}

interface TreeNode {
  files: Map<string, { oid: string; mode: string }>;
  dirs: Map<string, TreeNode>;
}

function emptyTreeNode(): TreeNode {
  return { files: new Map(), dirs: new Map() };
}

function treeToNode(repo: RepoRecord, treeOid: string | undefined): TreeNode {
  const node = emptyTreeNode();
  if (treeOid === undefined) return node;
  const object = repo.objects.get(treeOid);
  if (object === undefined || object.type !== 'tree') return node;
  for (const entry of parseTree(object.data)) {
    if (entry.mode === '40000') {
      node.dirs.set(entry.name, treeToNode(repo, entry.oid));
    } else if (entry.mode !== '160000') {
      node.files.set(entry.name, { oid: entry.oid, mode: entry.mode });
    }
  }
  return node;
}

function nodeToTreeOid(repo: RepoRecord, node: TreeNode): string {
  const entries: TreeEntry[] = [];
  for (const [name, file] of node.files) {
    entries.push({ mode: file.mode, name, oid: file.oid });
  }
  for (const [name, child] of node.dirs) {
    entries.push({ mode: '40000', name, oid: nodeToTreeOid(repo, child) });
  }
  return storeObject(repo, 'tree', buildTree(entries));
}

/** Set a file (creating parent dirs) in the tree rooted at `treeOid`; null root = empty tree. */
function setFileInTree(repo: RepoRecord, treeOid: string | null, segments: readonly string[], blobOid: string): string {
  const node = treeToNode(repo, treeOid ?? undefined);
  let current = node;
  for (let index = 0; index < segments.length - 1; index += 1) {
    const segment = segments[index]!;
    let child = current.dirs.get(segment);
    if (child === undefined) {
      child = emptyTreeNode();
      current.dirs.set(segment, child);
    }
    current = child;
  }
  current.files.set(segments[segments.length - 1]!, { oid: blobOid, mode: '100644' });
  return nodeToTreeOid(repo, node);
}

/** Delete a file from the tree rooted at `treeOid`; returns the new root, or null if absent. */
function deleteFileFromTree(repo: RepoRecord, treeOid: string, segments: readonly string[]): string | null {
  const node = treeToNode(repo, treeOid);
  const stack: TreeNode[] = [node];
  let current = node;
  for (let index = 0; index < segments.length - 1; index += 1) {
    const child = current.dirs.get(segments[index]!);
    if (child === undefined) return null;
    stack.push(child);
    current = child;
  }
  const leaf = segments[segments.length - 1]!;
  if (!current.files.has(leaf)) return null;
  current.files.delete(leaf);
  // Prune directories that became empty.
  for (let index = stack.length - 1; index >= 1; index -= 1) {
    const childNode = stack[index]!;
    const parentNode = stack[index - 1]!;
    const segment = segments[index - 1]!;
    if (childNode.files.size === 0 && childNode.dirs.size === 0) parentNode.dirs.delete(segment);
  }
  return nodeToTreeOid(repo, node);
}

/** The entry (file or directory) at `segments` under the tree, or undefined. */
function entryAtPath(repo: RepoRecord, treeOid: string, segments: readonly string[]): { mode: string; oid: string; name: string } | undefined {
  let currentOid = treeOid;
  for (let index = 0; index < segments.length; index += 1) {
    const object = repo.objects.get(currentOid);
    if (object === undefined || object.type !== 'tree') return undefined;
    const entry = parseTree(object.data).find((candidate) => candidate.name === segments[index]);
    if (entry === undefined) return undefined;
    if (index === segments.length - 1) return { mode: entry.mode, oid: entry.oid, name: entry.name };
    if (entry.mode !== '40000') return undefined;
    currentOid = entry.oid;
  }
  return undefined;
}

/** Directory listing entries at `segments` (empty segments = the tree root). */
function listDirectory(repo: RepoRecord, treeOid: string, segments: readonly string[]): TreeEntry[] | undefined {
  let currentOid = treeOid;
  for (const segment of segments) {
    const entry = entryAtPath(repo, currentOid, [segment]);
    if (entry === undefined || entry.mode !== '40000') return undefined;
    currentOid = entry.oid;
  }
  const object = repo.objects.get(currentOid);
  if (object === undefined || object.type !== 'tree') return undefined;
  return parseTree(object.data);
}

// ---------------------------------------------------------------- commits, ancestry, diffs

function createCommitObject(repo: RepoRecord, treeOid: string, parents: readonly string[], message: string, timestamp: number): string {
  const data = buildCommit({
    tree: treeOid,
    parents,
    message,
    author: VIEWER_IDENTITY,
    committer: VIEWER_IDENTITY,
    timestamp,
  });
  return storeObject(repo, 'commit', data);
}

/** All ancestors of `commitOid`, including itself, in BFS order from it. */
function ancestorsOf(repo: RepoRecord, commitOid: string): Set<string> {
  const seen = new Set<string>();
  const queue = [commitOid];
  let head = 0;
  while (head < queue.length) {
    const oid = queue[head++]!;
    if (seen.has(oid)) continue;
    const object = repo.objects.get(oid);
    if (object === undefined || object.type !== 'commit') continue;
    seen.add(oid);
    for (const parent of parseCommit(object.data).parents) queue.push(parent);
  }
  return seen;
}

function isAncestor(repo: RepoRecord, ancestorOid: string, descendantOid: string): boolean {
  // Early-exit walk: the fast-forward check in receive-pack only needs to know
  // whether `ancestorOid` is reachable, not the full ancestor set. (Previous
  // version built the whole set — O(history) parseCommit calls per push.)
  if (ancestorOid === descendantOid) {
    const object = repo.objects.get(descendantOid);
    return object !== undefined && object.type === 'commit';
  }
  const seen = new Set<string>();
  const queue = [descendantOid];
  let head = 0;
  while (head < queue.length) {
    const oid = queue[head++]!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const object = repo.objects.get(oid);
    if (object === undefined || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) {
      if (parent === ancestorOid) {
        const parentObject = repo.objects.get(parent);
        if (parentObject !== undefined && parentObject.type === 'commit') return true;
      }
      queue.push(parent);
    }
  }
  return false;
}

/** The merge base of two commits: the first common ancestor found walking from `b`. */
function mergeBase(repo: RepoRecord, aOid: string, bOid: string): string | undefined {
  const aAncestors = ancestorsOf(repo, aOid);
  const queue = [bOid];
  const seen = new Set<string>();
  let head = 0;
  while (head < queue.length) {
    const oid = queue[head++]!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    if (aAncestors.has(oid)) return oid;
    const object = repo.objects.get(oid);
    if (object === undefined || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) queue.push(parent);
  }
  return undefined;
}

interface FileChange {
  filename: string;
  status: 'added' | 'modified' | 'removed';
  additions: number;
  deletions: number;
  changes: number;
  oldOid: string | null;
  newOid: string | null;
}

function countLines(data: Buffer): number {
  if (data.length === 0) return 0;
  const text = data.toString('utf8');
  const lines = text.split('\n');
  return text.endsWith('\n') ? lines.length - 1 : lines.length;
}

/** Line-level diff stats between two file versions (added/deleted lines, by set). */
function diffLineStats(oldData: Buffer | null, newData: Buffer | null): { additions: number; deletions: number } {
  const oldLines = oldData === null ? [] : oldData.toString('utf8').split('\n');
  const newLines = newData === null ? [] : newData.toString('utf8').split('\n');
  const dropTrailingEmpty = (lines: string[]): string[] => (lines.length > 0 && lines[lines.length - 1] === '' ? lines.slice(0, -1) : lines);
  const oldSet = new Map<string, number>();
  for (const line of dropTrailingEmpty(oldLines)) oldSet.set(line, (oldSet.get(line) ?? 0) + 1);
  let additions = 0;
  for (const line of dropTrailingEmpty(newLines)) {
    const remaining = oldSet.get(line) ?? 0;
    if (remaining > 0) oldSet.set(line, remaining - 1);
    else additions += 1;
  }
  let deletions = 0;
  for (const remaining of oldSet.values()) deletions += remaining;
  return { additions, deletions };
}

function diffTrees(repo: RepoRecord, baseTreeOid: string | null, headTreeOid: string | null): FileChange[] {
  const base = baseTreeOid === null ? new Map<string, FlatFile>() : flattenTree(repo, baseTreeOid);
  const head = headTreeOid === null ? new Map<string, FlatFile>() : flattenTree(repo, headTreeOid);
  const paths = new Set([...base.keys(), ...head.keys()]);
  const changes: FileChange[] = [];
  for (const path of paths) {
    const baseFile = base.get(path);
    const headFile = head.get(path);
    if (baseFile === undefined && headFile !== undefined) {
      const stats = diffLineStats(null, repo.objects.get(headFile.oid)?.data ?? null);
      changes.push({ filename: path, status: 'added', additions: stats.additions, deletions: 0, changes: stats.additions, oldOid: null, newOid: headFile.oid });
    } else if (baseFile !== undefined && headFile === undefined) {
      const stats = diffLineStats(repo.objects.get(baseFile.oid)?.data ?? null, null);
      changes.push({ filename: path, status: 'removed', additions: 0, deletions: stats.deletions, changes: stats.deletions, oldOid: baseFile.oid, newOid: null });
    } else if (baseFile !== undefined && headFile !== undefined && baseFile.oid !== headFile.oid) {
      const stats = diffLineStats(repo.objects.get(baseFile.oid)?.data ?? null, repo.objects.get(headFile.oid)?.data ?? null);
      changes.push({ filename: path, status: 'modified', additions: stats.additions, deletions: stats.deletions, changes: stats.additions + stats.deletions, oldOid: baseFile.oid, newOid: headFile.oid });
    }
  }
  changes.sort((a, b) => (a.filename < b.filename ? -1 : a.filename > b.filename ? 1 : 0));
  return changes;
}

/** Apply the file states of `headTreeOid` (relative to `baseTreeOid`) onto `targetTreeOid`. */
function applyDiffToTree(repo: RepoRecord, targetTreeOid: string | null, baseTreeOid: string | null, headTreeOid: string | null): string {
  const changes = diffTrees(repo, baseTreeOid, headTreeOid);
  let current = targetTreeOid;
  for (const change of changes) {
    const segments = pathSegments(change.filename);
    if (change.newOid === null) {
      if (current !== null) {
        const next = deleteFileFromTree(repo, current, segments);
        if (next !== null) current = next;
      }
    } else {
      current = setFileInTree(repo, current, segments, change.newOid);
    }
  }
  return current ?? storeObject(repo, 'tree', buildTree([]));
}

function commitsBetween(repo: RepoRecord, fromOid: string, toOid: string): string[] {
  // Commits reachable from `toOid` but not from `fromOid`, newest-first by insertion order.
  const fromAncestors = ancestorsOf(repo, fromOid);
  const result: string[] = [];
  const queue = [toOid];
  const seen = new Set<string>();
  let head = 0;
  while (head < queue.length) {
    const oid = queue[head++]!;
    if (seen.has(oid) || fromAncestors.has(oid)) continue;
    seen.add(oid);
    const object = repo.objects.get(oid);
    if (object === undefined || object.type !== 'commit') continue;
    result.push(oid);
    for (const parent of parseCommit(object.data).parents) queue.push(parent);
  }
  result.sort((a, b) => (repo.commitSeq.get(b) ?? 0) - (repo.commitSeq.get(a) ?? 0));
  return result;
}

// ---------------------------------------------------------------- REST shapes and helpers

const SCENARIO_EPOCH_ISO = new Date(SCENARIO_EPOCH_SEC * 1000).toISOString();

function repoJson(repo: RepoRecord): Record<string, unknown> {
  return {
    id: repo.dbId,
    name: repo.name,
    full_name: `${repo.owner}/${repo.name}`,
    owner: { login: repo.owner, id: repo.owner === VIEWER_LOGIN ? VIEWER_ID : repo.dbId, type: 'User' },
    private: repo.isPrivate,
    description: repo.description,
    default_branch: repo.defaultBranch,
    created_at: SCENARIO_EPOCH_ISO,
    updated_at: SCENARIO_EPOCH_ISO,
    html_url: `https://github.com/${repo.owner}/${repo.name}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}`,
  };
}

function issueJson(issue: IssueRecord): Record<string, unknown> {
  return {
    id: issue.id,
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    labels: issue.labels.map((name) => ({ name })),
    user: { login: VIEWER_LOGIN, id: VIEWER_ID },
    created_at: SCENARIO_EPOCH_ISO,
    updated_at: SCENARIO_EPOCH_ISO,
  };
}

function pullHeadSha(repo: RepoRecord, pull: PullRecord): string {
  return refCommit(repo, `refs/heads/${pull.headRef}`) ?? ZERO_OID;
}

function pullBaseSha(repo: RepoRecord, pull: PullRecord): string {
  return refCommit(repo, `refs/heads/${pull.baseRef}`) ?? ZERO_OID;
}

function pullJson(repo: RepoRecord, pull: PullRecord): Record<string, unknown> {
  return {
    id: pull.id,
    number: pull.number,
    title: pull.title,
    body: pull.body,
    state: pull.state,
    head: { ref: pull.headRef, sha: pullHeadSha(repo, pull), label: `${repo.owner}:${pull.headRef}` },
    base: { ref: pull.baseRef, sha: pullBaseSha(repo, pull), label: `${repo.owner}:${pull.baseRef}` },
    merged: pull.merged,
    merged_at: pull.mergedAt,
    merge_commit_sha: pull.mergeCommitSha,
    user: { login: VIEWER_LOGIN, id: VIEWER_ID },
    created_at: SCENARIO_EPOCH_ISO,
    updated_at: SCENARIO_EPOCH_ISO,
  };
}

function commentJson(comment: CommentRecord): Record<string, unknown> {
  return {
    id: comment.id,
    body: comment.body,
    user: { login: VIEWER_LOGIN, id: VIEWER_ID },
    created_at: SCENARIO_EPOCH_ISO,
    updated_at: SCENARIO_EPOCH_ISO,
  };
}

/** The tree oid at the tip of a branch, or null when the branch has no commits yet. */
function branchTreeOid(repo: RepoRecord, branch: string): string | null {
  const tip = branchTip(repo, branch);
  if (tip === undefined) return null;
  const commitOid = peelToCommit(repo, tip);
  const object = repo.objects.get(commitOid);
  if (object === undefined || object.type !== 'commit') return null;
  return parseCommit(object.data).tree;
}

/** Resolve a ref query (?ref=) to a tree oid: branch name, commit oid, or tree oid. */
function resolveRefToTree(repo: RepoRecord, ref: string | null): string | null {
  if (ref === null || ref === '') {
    return branchTreeOid(repo, repo.defaultBranch);
  }
  const branchTipOid = branchTip(repo, ref);
  if (branchTipOid !== undefined) {
    const commitOid = peelToCommit(repo, branchTipOid);
    const object = repo.objects.get(commitOid);
    if (object !== undefined && object.type === 'commit') return parseCommit(object.data).tree;
    return null;
  }
  const object = repo.objects.get(ref);
  if (object === undefined) return null;
  if (object.type === 'commit') return parseCommit(object.data).tree;
  if (object.type === 'tree') return ref;
  return null;
}

function parsePagination(url: URL): { page: number; perPage: number } {
  const page = Math.max(1, Number.parseInt(url.searchParams.get('page') ?? '1', 10) || 1);
  const perPageRaw = Number.parseInt(url.searchParams.get('per_page') ?? '30', 10) || 30;
  const perPage = Math.min(100, Math.max(1, perPageRaw));
  return { page, perPage };
}

/** Build a Link header for the next page, or null when this is the last page. */
function nextLinkHeader(req: IncomingMessage, url: URL, page: number, perPage: number, hasNext: boolean): string | null {
  if (!hasNext) return null;
  const host = req.headers.host ?? 'localhost';
  const next = new URL(url.toString());
  next.searchParams.set('page', String(page + 1));
  next.searchParams.set('per_page', String(perPage));
  next.protocol = 'http:';
  next.host = host;
  return `<${next.toString()}>; rel="next"`;
}

function paginate<T>(items: readonly T[], page: number, perPage: number): { items: T[]; hasNext: boolean } {
  const start = (page - 1) * perPage;
  return { items: items.slice(start, start + perPage), hasNext: start + perPage < items.length };
}

function parseIssueLabels(value: unknown): string[] | null {
  if (!Array.isArray(value)) return null;
  const names: string[] = [];
  for (const item of value) {
    if (typeof item === 'string') names.push(item);
    else if (typeof item === 'object' && item !== null && typeof (item as Record<string, unknown>).name === 'string') {
      names.push((item as Record<string, unknown>).name as string);
    } else {
      return null;
    }
  }
  return names;
}

function stripOwnerPrefix(ref: string): string {
  const colon = ref.indexOf(':');
  return colon >= 0 ? ref.slice(colon + 1) : ref;
}

// ---------------------------------------------------------------- HTTP response helpers

function sendJsonPayload(res: ServerResponse, status: number, payload: Buffer, extraHeaders: Record<string, string> = {}): void {
  res.writeHead(status, {
    'content-type': JSON_TYPE,
    'x-github-request-id': nextRequestId(),
    'content-length': String(payload.length),
    ...extraHeaders,
  });
  res.end(payload);
}

function sendJson(res: ServerResponse, status: number, body: unknown, extraHeaders: Record<string, string> = {}): void {
  sendJsonPayload(res, status, Buffer.from(JSON.stringify(body), 'utf8'), extraHeaders);
}

function sendNoContent(res: ServerResponse): void {
  res.writeHead(204, { 'x-github-request-id': nextRequestId() });
  res.end();
}

function sendBuffer(res: ServerResponse, status: number, body: Buffer, contentType: string, extraHeaders: Record<string, string> = {}): void {
  res.writeHead(status, {
    'content-type': contentType,
    'content-length': String(body.length),
    ...extraHeaders,
  });
  res.end(body);
}

function jsonError(res: ServerResponse, status: number, message: string): void {
  sendJson(res, status, { message });
}

function readBody(req: IncomingMessage): Promise<Buffer> {
  // Fast path: no body framing means no body bytes will arrive. (GET/HEAD
  // requests in this protocol never carry one; POSTs with Content-Length: 0
  // neither.) Skips a Promise, three listeners, and an event-loop turn.
  const contentLength = req.headers['content-length'];
  if ((contentLength === '0' || (contentLength === undefined && req.headers['transfer-encoding'] === undefined))) {
    return Promise.resolve(Buffer.alloc(0));
  }
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    req.on('data', (chunk: Buffer) => chunks.push(chunk));
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

function parseJsonBody(raw: Buffer): { ok: true; value: Record<string, unknown> } | { ok: false } {
  if (raw.length === 0) return { ok: true, value: {} };
  try {
    const parsed: unknown = JSON.parse(raw.toString('utf8'));
    if (typeof parsed === 'object' && parsed !== null && !Array.isArray(parsed)) {
      return { ok: true, value: parsed as Record<string, unknown> };
    }
    return { ok: false };
  } catch {
    return { ok: false };
  }
}

function bearerToken(req: IncomingMessage): string | null {
  const header = req.headers.authorization;
  if (typeof header !== 'string') return null;
  const match = /^Bearer\s+(.+)$/.exec(header);
  return match === null ? null : match[1]!.trim() || null;
}

function requireAuth(req: IncomingMessage, res: ServerResponse): boolean {
  if (bearerToken(req) === null) {
    jsonError(res, 401, 'Requires authentication');
    return false;
  }
  return true;
}

// ---------------------------------------------------------------- REST v3

/**
 * Handle one REST v3 request. Returns true when the request was handled
 * (including an error reply), false when the path is not a REST route.
 */
async function handleRest(forge: Forge, req: IncomingMessage, res: ServerResponse, url: URL, body: Buffer): Promise<boolean> {
  const segments = url.pathname.split('/').filter((segment) => segment !== '');
  if (segments[0] !== 'api' || segments[1] !== 'v3') return false;
  const method = req.method ?? 'GET';
  const rest = segments.slice(2);
  const decode = (value: string): string => {
    try {
      return decodeURIComponent(value);
    } catch {
      return value;
    }
  };

  // Root and meta ------------------------------------------------------------
  if (rest.length === 0 && method === 'GET') {
    sendJson(res, 200, {
      current_user_url: '/api/v3/user',
      repository_url: '/api/v3/repos/{owner}/{repo}',
      user_url: '/api/v3/users/{user}',
      meta: { verifiable_password_authentication: true },
    }, { 'x-oauth-scopes': 'repo, read:org' });
    return true;
  }
  if (rest.length === 1 && rest[0] === 'meta' && method === 'GET') {
    sendJson(res, 200, { installed_version: '1.0.0' });
    return true;
  }

  // Authenticated user -------------------------------------------------------
  if (rest.length === 1 && rest[0] === 'user' && method === 'GET') {
    sendJson(res, 200, { login: VIEWER_LOGIN, id: VIEWER_ID, name: VIEWER_NAME, email: VIEWER_EMAIL, type: 'User' });
    return true;
  }
  if (rest.length === 2 && rest[0] === 'user' && rest[1] === 'repos') {
    if (method === 'GET') {
      const { page, perPage } = parsePagination(url);
      const all = forge.viewerRepos();
      const { items, hasNext } = paginate(all, page, perPage);
      const link = nextLinkHeader(req, url, page, perPage, hasNext);
      sendJson(res, 200, items.map(repoJson), link === null ? {} : { link });
      return true;
    }
    if (method === 'POST') {
      const parsed = parseJsonBody(body);
      if (!parsed.ok) {
        jsonError(res, 400, 'Problems parsing JSON');
        return true;
      }
      const name = parsed.value.name;
      if (typeof name !== 'string' || name === '') {
        jsonError(res, 422, 'Validation Failed: name is required');
        return true;
      }
      if (forge.getRepo(VIEWER_LOGIN, name) !== undefined) {
        jsonError(res, 422, 'Validation Failed: name already exists on this account');
        return true;
      }
      const description = typeof parsed.value.description === 'string' ? parsed.value.description : '';
      const isPrivate = parsed.value.private === true;
      const repo = forge.createRepo(VIEWER_LOGIN, name, description, isPrivate);
      sendJson(res, 201, repoJson(repo));
      return true;
    }
    return false;
  }

  // Repositories -------------------------------------------------------------
  if (rest.length >= 2 && rest[0] === 'repos') {
    const owner = decode(rest[1]!);
    const repoName = decode(rest[2] ?? '');
    if (rest.length < 3 || owner !== VIEWER_LOGIN) {
      // Repositories under any other owner do not exist for this token: 404, never 403.
      jsonError(res, 404, 'Not Found');
      return true;
    }
    const repo = forge.getRepo(owner, repoName);
    const tail = rest.slice(3);

    if (tail.length === 0) {
      if (method === 'GET') {
        if (repo === undefined) {
          jsonError(res, 404, 'Not Found');
          return true;
        }
        sendJson(res, 200, repoJson(repo));
        return true;
      }
      if (method === 'PATCH') {
        if (repo === undefined) {
          jsonError(res, 404, 'Not Found');
          return true;
        }
        const parsed = parseJsonBody(body);
        if (!parsed.ok) {
          jsonError(res, 400, 'Problems parsing JSON');
          return true;
        }
        if (typeof parsed.value.description === 'string') repo.description = parsed.value.description;
        if (typeof parsed.value.private === 'boolean') repo.isPrivate = parsed.value.private;
        sendJson(res, 200, repoJson(repo));
        return true;
      }
      if (method === 'DELETE') {
        if (repo === undefined) {
          jsonError(res, 404, 'Not Found');
          return true;
        }
        forge.repos.delete(forge.key(owner, repoName));
        const index = forge.repoCreationOrder.indexOf(repo);
        if (index >= 0) forge.repoCreationOrder.splice(index, 1);
        sendNoContent(res);
        return true;
      }
      return false;
    }
    if (repo === undefined) {
      jsonError(res, 404, 'Not Found');
      return true;
    }

    // Branches ---------------------------------------------------------------
    if (tail[0] === 'branches') {
      if (tail.length === 1 && method === 'GET') {
        const branches = [...repo.refs.keys()]
          .filter((ref) => ref.startsWith('refs/heads/'))
          .map((ref) => ref.slice('refs/heads/'.length))
          .sort()
          .map((branch) => ({ name: branch, commit: { sha: peelToCommit(repo, branchTip(repo, branch)!) }, protected: false }));
        sendJson(res, 200, branches);
        return true;
      }
      if (tail.length === 2 && method === 'GET') {
        const branch = decode(tail[1]!);
        const tip = branchTip(repo, branch);
        if (tip === undefined) {
          jsonError(res, 404, 'Not Found');
          return true;
        }
        sendJson(res, 200, { name: branch, commit: { sha: peelToCommit(repo, tip) }, protected: false });
        return true;
      }
      return false;
    }

    // Commits ----------------------------------------------------------------
    if (tail[0] === 'commits' && tail.length === 1 && method === 'GET') {
      const shaParam = url.searchParams.get('sha');
      const tip = shaParam === null || shaParam === ''
        ? branchTip(repo, repo.defaultBranch)
        : (branchTip(repo, shaParam) ?? (isOid(shaParam) ? shaParam : undefined));
      const list: Array<Record<string, unknown>> = [];
      if (tip !== undefined) {
        const start = peelToCommit(repo, tip);
        const queue = [start];
        const seen = new Set<string>();
        const found: string[] = [];
        while (queue.length > 0) {
          const oid = queue.shift()!;
          if (seen.has(oid)) continue;
          seen.add(oid);
          const object = repo.objects.get(oid);
          if (object === undefined || object.type !== 'commit') continue;
          found.push(oid);
          for (const parent of parseCommit(object.data).parents) queue.push(parent);
        }
        found.sort((a, b) => (repo.commitSeq.get(b) ?? 0) - (repo.commitSeq.get(a) ?? 0));
        for (const oid of found) {
          const view = parseCommit(repo.objects.get(oid)!.data);
          list.push({
            sha: oid,
            commit: {
              message: view.message,
              author: { name: VIEWER_NAME, email: VIEWER_EMAIL },
              committer: { name: VIEWER_NAME, email: VIEWER_EMAIL },
            },
            parents: view.parents.map((parent) => ({ sha: parent })),
          });
        }
      }
      sendJson(res, 200, list);
      return true;
    }

    // Git refs ---------------------------------------------------------------
    if (tail[0] === 'git' && tail[1] === 'refs') {
      if (tail.length === 2 && method === 'POST') {
        const parsed = parseJsonBody(body);
        if (!parsed.ok) {
          jsonError(res, 400, 'Problems parsing JSON');
          return true;
        }
        const ref = typeof parsed.value.ref === 'string' ? parsed.value.ref : '';
        const sha = typeof parsed.value.sha === 'string' ? parsed.value.sha : '';
        if (ref === '' || sha === '' || repo.objects.get(sha) === undefined) {
          jsonError(res, 422, 'Validation Failed: ref and a valid sha are required');
          return true;
        }
        if (repo.refs.has(ref)) {
          jsonError(res, 422, 'Validation Failed: Reference already exists');
          return true;
        }
        repo.refs.set(ref, sha);
        const type = repo.objects.get(sha)!.type;
        sendJson(res, 201, { ref, object: { sha, type } });
        return true;
      }
      if (tail.length >= 3 && method === 'GET') {
        // /git/refs/heads/{branch}
        const refName = tail.slice(2).map(decode).join('/');
        const tip = repo.refs.get(refName);
        if (tip === undefined) {
          jsonError(res, 404, 'Not Found');
          return true;
        }
        sendJson(res, 200, { ref: refName, object: { sha: tip, type: repo.objects.get(tip)?.type ?? 'commit' } });
        return true;
      }
      return false;
    }

    // Contents ---------------------------------------------------------------
    if (tail[0] === 'contents') {
      const path = tail.slice(1).map(decode).join('/');
      const branch = url.searchParams.get('ref') ?? repo.defaultBranch;
      if (method === 'GET') {
        const treeOid = resolveRefToTree(repo, url.searchParams.get('ref'));
        if (treeOid === null) {
          jsonError(res, 404, 'Not Found');
          return true;
        }
        const segments = pathSegments(path);
        if (segments.length === 0) {
          const entries = listDirectory(repo, treeOid, []);
          if (entries === undefined) {
            jsonError(res, 404, 'Not Found');
            return true;
          }
          sendJson(res, 200, entries.map((entry) => ({
            type: entry.mode === '40000' ? 'dir' : 'file',
            name: entry.name,
            path: entry.name,
            sha: entry.oid,
            size: entry.mode === '40000' ? 0 : (repo.objects.get(entry.oid)?.data.length ?? 0),
          })));
          return true;
        }
        const entry = entryAtPath(repo, treeOid, segments);
        if (entry === undefined) {
          jsonError(res, 404, 'Not Found');
          return true;
        }
        if (entry.mode === '40000') {
          const entries = listDirectory(repo, treeOid, segments);
          if (entries === undefined) {
            jsonError(res, 404, 'Not Found');
            return true;
          }
          sendJson(res, 200, entries.map((child) => ({
            type: child.mode === '40000' ? 'dir' : 'file',
            name: child.name,
            path: `${path}/${child.name}`,
            sha: child.oid,
            size: child.mode === '40000' ? 0 : (repo.objects.get(child.oid)?.data.length ?? 0),
          })));
          return true;
        }
        const blob = repo.objects.get(entry.oid);
        if (blob === undefined || blob.type !== 'blob') {
          jsonError(res, 404, 'Not Found');
          return true;
        }
        sendJson(res, 200, {
          type: 'file',
          name: entry.name,
          path,
          sha: entry.oid,
          size: blob.data.length,
          encoding: 'base64',
          content: blob.data.toString('base64'),
        });
        return true;
      }
      if (method === 'PUT') {
        const parsed = parseJsonBody(body);
        if (!parsed.ok) {
          jsonError(res, 400, 'Problems parsing JSON');
          return true;
        }
        const contentB64 = typeof parsed.value.content === 'string' ? parsed.value.content : '';
        const message = typeof parsed.value.message === 'string' ? parsed.value.message : 'Update file';
        const requestBranch = typeof parsed.value.branch === 'string' ? parsed.value.branch : branch;
        const tip = branchTip(repo, requestBranch);
        const currentTree = tip === undefined ? null : branchTreeOid(repo, requestBranch);
        const segments = pathSegments(path);
        if (segments.length === 0) {
          jsonError(res, 422, 'Validation Failed: path is required');
          return true;
        }
        const existing = currentTree === null ? undefined : entryAtPath(repo, currentTree, segments);
        if (existing !== undefined && existing.mode === '40000') {
          jsonError(res, 422, 'Validation Failed: path is a directory');
          return true;
        }
        if (existing !== undefined) {
          const givenSha = typeof parsed.value.sha === 'string' ? parsed.value.sha : '';
          if (givenSha === '' || givenSha !== existing.oid) {
            jsonError(res, 409, 'Conflict: sha does not match the current file');
            return true;
          }
        }
        const blobOid = storeObject(repo, 'blob', b64decode(contentB64));
        const newTree = setFileInTree(repo, currentTree, segments, blobOid);
        const parents = tip === undefined ? [] : [peelToCommit(repo, tip)];
        const commitOid = createCommitObject(repo, newTree, parents, message, nowSec());
        repo.refs.set(`refs/heads/${requestBranch}`, commitOid);
        sendJson(res, existing === undefined ? 201 : 200, {
          content: {
            name: segments[segments.length - 1],
            path,
            sha: blobOid,
            size: b64decode(contentB64).length,
            encoding: 'base64',
            content: contentB64,
          },
          commit: { sha: commitOid, message },
        });
        return true;
      }
      if (method === 'DELETE') {
        const parsed = parseJsonBody(body);
        if (!parsed.ok) {
          jsonError(res, 400, 'Problems parsing JSON');
          return true;
        }
        const requestBranch = typeof parsed.value.branch === 'string' ? parsed.value.branch : branch;
        const tip = branchTip(repo, requestBranch);
        if (tip === undefined) {
          jsonError(res, 404, 'Not Found');
          return true;
        }
        const currentTree = branchTreeOid(repo, requestBranch)!;
        const segments = pathSegments(path);
        const existing = entryAtPath(repo, currentTree, segments);
        if (existing === undefined || existing.mode === '40000') {
          jsonError(res, 404, 'Not Found');
          return true;
        }
        const givenSha = typeof parsed.value.sha === 'string' ? parsed.value.sha : '';
        if (givenSha !== '' && givenSha !== existing.oid) {
          jsonError(res, 409, 'Conflict: sha does not match the current file');
          return true;
        }
        const message = typeof parsed.value.message === 'string' ? parsed.value.message : 'Delete file';
        const newTree = deleteFileFromTree(repo, currentTree, segments);
        if (newTree === null) {
          jsonError(res, 404, 'Not Found');
          return true;
        }
        const commitOid = createCommitObject(repo, newTree, [peelToCommit(repo, tip)], message, nowSec());
        repo.refs.set(`refs/heads/${requestBranch}`, commitOid);
        sendJson(res, 200, { commit: { sha: commitOid, message } });
        return true;
      }
      return false;
    }

    // Labels -----------------------------------------------------------------
    if (tail[0] === 'labels') {
      if (tail.length === 1 && method === 'GET') {
        sendJson(res, 200, [...repo.labels.entries()].map(([name, color]) => ({ name, color })));
        return true;
      }
      if (tail.length === 1 && method === 'POST') {
        const parsed = parseJsonBody(body);
        if (!parsed.ok) {
          jsonError(res, 400, 'Problems parsing JSON');
          return true;
        }
        const name = typeof parsed.value.name === 'string' ? parsed.value.name : '';
        const color = typeof parsed.value.color === 'string' ? parsed.value.color : 'ededed';
        if (name === '') {
          jsonError(res, 422, 'Validation Failed: name is required');
          return true;
        }
        repo.labels.set(name, color);
        sendJson(res, 201, { name, color });
        return true;
      }
      return false;
    }

    // Issues -----------------------------------------------------------------
    if (tail[0] === 'issues') {
      if (tail.length === 1 && method === 'GET') {
        const state = url.searchParams.get('state') ?? 'open';
        const sort = url.searchParams.get('sort') ?? 'created';
        const direction = url.searchParams.get('direction') ?? 'desc';
        let list = [...repo.issues.values()];
        if (state !== 'all') list = list.filter((issue) => issue.state === state);
        if (sort === 'created') {
          list.sort((a, b) => direction === 'asc' ? a.createdSeq - b.createdSeq : b.createdSeq - a.createdSeq);
        }
        const { page, perPage } = parsePagination(url);
        const { items, hasNext } = paginate(list, page, perPage);
        const link = nextLinkHeader(req, url, page, perPage, hasNext);
        sendJson(res, 200, items.map(issueJson), link === null ? {} : { link });
        return true;
      }
      if (tail.length === 1 && method === 'POST') {
        const parsed = parseJsonBody(body);
        if (!parsed.ok) {
          jsonError(res, 400, 'Problems parsing JSON');
          return true;
        }
        const title = typeof parsed.value.title === 'string' ? parsed.value.title : '';
        if (title === '') {
          jsonError(res, 422, 'Validation Failed: title is required');
          return true;
        }
        const labels = parseIssueLabels(parsed.value.labels ?? []);
        if (labels === null) {
          jsonError(res, 422, 'Validation Failed: labels must be an array');
          return true;
        }
        for (const label of labels) {
          if (!repo.labels.has(label)) {
            jsonError(res, 422, `Validation Failed: label "${label}" does not exist`);
            return true;
          }
        }
        const issue: IssueRecord = {
          id: issueIdCounter++,
          number: repo.nextIssueNumber++,
          title,
          body: typeof parsed.value.body === 'string' ? parsed.value.body : '',
          state: 'open',
          labels,
          createdSeq: ++globalSeq,
        };
        repo.issues.set(issue.number, issue);
        sendJson(res, 201, issueJson(issue));
        return true;
      }
      if (tail.length === 2) {
        const number = Number.parseInt(tail[1]!, 10);
        const issue = repo.issues.get(number);
        if (issue === undefined) {
          jsonError(res, 404, 'Not Found');
          return true;
        }
        if (method === 'GET') {
          if (issue.jsonPayload === undefined) {
            issue.jsonPayload = Buffer.from(JSON.stringify(issueJson(issue)), 'utf8');
          }
          sendJsonPayload(res, 200, issue.jsonPayload);
          return true;
        }
        if (method === 'PATCH') {
          const parsed = parseJsonBody(body);
          if (!parsed.ok) {
            jsonError(res, 400, 'Problems parsing JSON');
            return true;
          }
          if (typeof parsed.value.title === 'string') issue.title = parsed.value.title;
          if (typeof parsed.value.body === 'string') issue.body = parsed.value.body;
          if (typeof parsed.value.state === 'string' && (parsed.value.state === 'open' || parsed.value.state === 'closed')) {
            issue.state = parsed.value.state;
          }
          if (parsed.value.labels !== undefined) {
            const labels = parseIssueLabels(parsed.value.labels);
            if (labels === null) {
              jsonError(res, 422, 'Validation Failed: labels must be an array');
              return true;
            }
            for (const label of labels) {
              if (!repo.labels.has(label)) {
                jsonError(res, 422, `Validation Failed: label "${label}" does not exist`);
                return true;
              }
            }
            issue.labels = labels;
          }
          issue.jsonPayload = Buffer.from(JSON.stringify(issueJson(issue)), 'utf8');
          sendJsonPayload(res, 200, issue.jsonPayload);
          return true;
        }
        return false;
      }
      if (tail.length === 3 && tail[2] === 'comments') {
        const number = Number.parseInt(tail[1]!, 10);
        const issue = repo.issues.get(number);
        if (issue === undefined) {
          jsonError(res, 404, 'Not Found');
          return true;
        }
        if (method === 'GET') {
          const comments = repo.comments.get(number) ?? [];
          sendJson(res, 200, comments.map(commentJson));
          return true;
        }
        if (method === 'POST') {
          const parsed = parseJsonBody(body);
          if (!parsed.ok) {
            jsonError(res, 400, 'Problems parsing JSON');
            return true;
          }
          const commentBody = typeof parsed.value.body === 'string' ? parsed.value.body : '';
          const comment: CommentRecord = { id: commentIdCounter++, body: commentBody, createdSeq: ++globalSeq };
          const list = repo.comments.get(number) ?? [];
          list.push(comment);
          repo.comments.set(number, list);
          sendJson(res, 201, commentJson(comment));
          return true;
        }
        return false;
      }
      return false;
    }

    // Pulls ------------------------------------------------------------------
    if (tail[0] === 'pulls') {
      if (tail.length === 1 && method === 'GET') {
        const state = url.searchParams.get('state') ?? 'open';
        let list = [...repo.pulls.values()];
        if (state !== 'all') list = list.filter((pull) => pull.state === state);
        list.sort((a, b) => b.createdSeq - a.createdSeq);
        const { page, perPage } = parsePagination(url);
        const { items, hasNext } = paginate(list, page, perPage);
        const link = nextLinkHeader(req, url, page, perPage, hasNext);
        sendJson(res, 200, items.map((pull) => pullJson(repo, pull)), link === null ? {} : { link });
        return true;
      }
      if (tail.length === 1 && method === 'POST') {
        const parsed = parseJsonBody(body);
        if (!parsed.ok) {
          jsonError(res, 400, 'Problems parsing JSON');
          return true;
        }
        const title = typeof parsed.value.title === 'string' ? parsed.value.title : '';
        const head = typeof parsed.value.head === 'string' ? stripOwnerPrefix(parsed.value.head) : '';
        const base = typeof parsed.value.base === 'string' ? stripOwnerPrefix(parsed.value.base) : '';
        if (title === '' || head === '' || base === '') {
          jsonError(res, 422, 'Validation Failed: title, head and base are required');
          return true;
        }
        if (branchTip(repo, head) === undefined || branchTip(repo, base) === undefined) {
          jsonError(res, 422, 'Validation Failed: head or base branch does not exist');
          return true;
        }
        const pull: PullRecord = {
          id: issueIdCounter++,
          number: repo.nextPullNumber++,
          title,
          body: typeof parsed.value.body === 'string' ? parsed.value.body : '',
          state: 'open',
          headRef: head,
          baseRef: base,
          merged: false,
          mergedAt: null,
          mergeCommitSha: null,
          createdSeq: ++globalSeq,
        };
        repo.pulls.set(pull.number, pull);
        sendJson(res, 201, pullJson(repo, pull));
        return true;
      }
      if (tail.length === 2) {
        const number = Number.parseInt(tail[1]!, 10);
        const pull = repo.pulls.get(number);
        if (pull === undefined) {
          jsonError(res, 404, 'Not Found');
          return true;
        }
        if (method === 'GET') {
          sendJson(res, 200, pullJson(repo, pull));
          return true;
        }
        return false;
      }
      if (tail.length === 3 && tail[2] === 'files' && method === 'GET') {
        const number = Number.parseInt(tail[1]!, 10);
        const pull = repo.pulls.get(number);
        if (pull === undefined) {
          jsonError(res, 404, 'Not Found');
          return true;
        }
        const files = pullFiles(repo, pull);
        sendJson(res, 200, files.map((change) => ({
          filename: change.filename,
          status: change.status,
          additions: change.additions,
          deletions: change.deletions,
          changes: change.changes,
        })));
        return true;
      }
      if (tail.length === 3 && tail[2] === 'merge' && method === 'PUT') {
        const number = Number.parseInt(tail[1]!, 10);
        const pull = repo.pulls.get(number);
        if (pull === undefined) {
          jsonError(res, 404, 'Not Found');
          return true;
        }
        const parsed = parseJsonBody(body);
        if (!parsed.ok) {
          jsonError(res, 400, 'Problems parsing JSON');
          return true;
        }
        const mergeMethod = typeof parsed.value.merge_method === 'string' ? parsed.value.merge_method : 'merge';
        const result = mergePull(repo, pull, mergeMethod);
        if (result === null) {
          jsonError(res, 405, 'Pull request cannot be merged: merge conflict');
          return true;
        }
        sendJson(res, 200, { sha: result, merged: true, message: 'Pull request successfully merged' });
        return true;
      }
      return false;
    }

    return false;
  }

  return false;
}

/** The file list of a pull: diff of merge base against the head tip. */
function pullFiles(repo: RepoRecord, pull: PullRecord): FileChange[] {
  const headOid = refCommit(repo, `refs/heads/${pull.headRef}`);
  const baseOid = refCommit(repo, `refs/heads/${pull.baseRef}`);
  if (headOid === undefined || baseOid === undefined) return [];
  const base = mergeBase(repo, headOid, baseOid);
  const baseTree = base === undefined ? null : parseCommit(repo.objects.get(base)!.data).tree;
  const headTree = parseCommit(repo.objects.get(headOid)!.data).tree;
  return diffTrees(repo, baseTree, headTree);
}

/**
 * Whether merging `headOid` into `baseOid` would conflict: a file the head changed
 * relative to the merge base was also changed on the base tip, to different content.
 */
function mergeConflict(repo: RepoRecord, headOid: string, baseOid: string): boolean {
  const base = mergeBase(repo, headOid, baseOid);
  const baseTree = base === undefined ? null : parseCommit(repo.objects.get(base)!.data).tree;
  const headTree = parseCommit(repo.objects.get(headOid)!.data).tree;
  const baseTipTree = parseCommit(repo.objects.get(baseOid)!.data).tree;
  const headChanges = diffTrees(repo, baseTree, headTree);
  const baseTipFiles = flattenTree(repo, baseTipTree);
  const baseFiles = baseTree === null ? new Map<string, FlatFile>() : flattenTree(repo, baseTree);
  for (const change of headChanges) {
    const baseFile = baseFiles.get(change.filename);
    const tipFile = baseTipFiles.get(change.filename);
    const baseChanged = (baseFile?.oid ?? null) !== (tipFile?.oid ?? null);
    const headChanged = (baseFile?.oid ?? null) !== (change.newOid ?? null);
    if (baseChanged && headChanged && (tipFile?.oid ?? null) !== (change.newOid ?? null)) return true;
  }
  return false;
}

/**
 * Merge a pull request. Returns the merge commit oid, or null on a merge conflict.
 * Squash merges apply the head tree onto the base tip in a single-parent commit;
 * merge commits apply the three-way diff with both parents. Every method refuses
 * a conflicted merge first: a squash of a conflicted branch is a 405 like any other.
 */
function mergePull(repo: RepoRecord, pull: PullRecord, mergeMethod: string): string | null {
  if (pull.merged || pull.state !== 'open') return null;
  const headOid = refCommit(repo, `refs/heads/${pull.headRef}`);
  const baseOid = refCommit(repo, `refs/heads/${pull.baseRef}`);
  if (headOid === undefined || baseOid === undefined) return null;
  if (mergeConflict(repo, headOid, baseOid)) return null;
  const base = mergeBase(repo, headOid, baseOid);
  const baseTree = base === undefined ? null : parseCommit(repo.objects.get(base)!.data).tree;
  const headTree = parseCommit(repo.objects.get(headOid)!.data).tree;
  const baseTipTree = parseCommit(repo.objects.get(baseOid)!.data).tree;

  if (mergeMethod === 'squash' || mergeMethod === 'rebase') {
    const message = `Merge pull request #${pull.number} from ${repo.owner}/${pull.headRef}\n\n${pull.title}`;
    const commitOid = createCommitObject(repo, headTree, [baseOid], message, nowSec());
    repo.refs.set(`refs/heads/${pull.baseRef}`, commitOid);
    pull.state = 'closed';
    pull.merged = true;
    pull.mergedAt = nowIso();
    pull.mergeCommitSha = commitOid;
    return commitOid;
  }

  const mergedTree = applyDiffToTree(repo, baseTipTree, baseTree, headTree);
  const message = `Merge pull request #${pull.number} from ${repo.owner}/${pull.headRef}\n\n${pull.title}`;
  const commitOid = createCommitObject(repo, mergedTree, [baseOid, headOid], message, nowSec());
  repo.refs.set(`refs/heads/${pull.baseRef}`, commitOid);
  pull.state = 'closed';
  pull.merged = true;
  pull.mergedAt = nowIso();
  pull.mergeCommitSha = commitOid;
  return commitOid;
}

// ---------------------------------------------------------------- GraphQL v4

// A small GraphQL executor: just enough of the language for the documents the
// conformance suite sends (operations, variables, aliases, inline fragments,
// __type introspection). Unknown fields are reported as GraphQL errors with
// HTTP 200; an unknown repository resolves to null without errors.

type GqlValue =
  | { kind: 'var'; name: string }
  | { kind: 'int'; value: number }
  | { kind: 'float'; value: number }
  | { kind: 'string'; value: string }
  | { kind: 'bool'; value: boolean }
  | { kind: 'null' }
  | { kind: 'enum'; value: string }
  | { kind: 'list'; values: GqlValue[] }
  | { kind: 'object'; fields: Map<string, GqlValue> };

type SelectionItem =
  | { kind: 'field'; alias: string | null; name: string; args: Map<string, GqlValue>; selection: SelectionItem[] | null }
  | { kind: 'fragment'; typeCondition: string | null; selection: SelectionItem[] };

interface GqlOperation {
  operation: 'query' | 'mutation';
  name: string | null;
  selection: SelectionItem[];
}

interface GqlToken {
  kind: 'name' | 'int' | 'float' | 'string' | 'punct' | 'eof';
  value: string;
}

function gqlTokenize(source: string): GqlToken[] {
  const tokens: GqlToken[] = [];
  let index = 0;
  const push = (kind: GqlToken['kind'], value: string): void => {
    tokens.push({ kind, value });
  };
  while (index < source.length) {
    const char = source[index]!;
    if (char === ' ' || char === '\t' || char === '\n' || char === '\r' || char === ',' || char === ';') {
      index += 1;
      continue;
    }
    if (char === '#') {
      while (index < source.length && source[index] !== '\n') index += 1;
      continue;
    }
    if (char === '{' || char === '}' || char === '(' || char === ')' || char === '[' || char === ']' || char === ':' || char === '!' || char === '$' || char === '=' || char === '@') {
      push('punct', char);
      index += 1;
      continue;
    }
    if (source.startsWith('...', index)) {
      push('punct', '...');
      index += 3;
      continue;
    }
    if (char === '"') {
      let value = '';
      index += 1;
      while (index < source.length && source[index] !== '"') {
        if (source[index] === '\\' && index + 1 < source.length) {
          const escaped = source[index + 1]!;
          value += escaped === 'n' ? '\n' : escaped === 't' ? '\t' : escaped === 'r' ? '\r' : escaped;
          index += 2;
        } else {
          value += source[index];
          index += 1;
        }
      }
      index += 1;
      push('string', value);
      continue;
    }
    if (/[0-9-]/.test(char)) {
      let end = index;
      while (end < source.length && /[0-9.eE+-]/.test(source[end]!)) end += 1;
      const text = source.slice(index, end);
      push(text.includes('.') || text.includes('e') || text.includes('E') ? 'float' : 'int', text);
      index = end;
      continue;
    }
    if (/[_A-Za-z]/.test(char)) {
      let end = index;
      while (end < source.length && /[_A-Za-z0-9]/.test(source[end]!)) end += 1;
      push('name', source.slice(index, end));
      index = end;
      continue;
    }
    throw new Error(`GraphQL: unexpected character ${JSON.stringify(char)}`);
  }
  push('eof', '');
  return tokens;
}

class GqlParser {
  private index = 0;
  private readonly tokens: GqlToken[];
  constructor(tokens: GqlToken[]) {
    this.tokens = tokens;
  }

  private peek(): GqlToken {
    return this.tokens[this.index]!;
  }

  private next(): GqlToken {
    const token = this.tokens[this.index]!;
    this.index += 1;
    return token;
  }

  private expectPunct(value: string): void {
    const token = this.next();
    if (token.kind !== 'punct' || token.value !== value) {
      throw new Error(`GraphQL: expected ${JSON.stringify(value)}, got ${JSON.stringify(token.value)}`);
    }
  }

  private expectName(value?: string): string {
    const token = this.next();
    if (token.kind !== 'name' || (value !== undefined && token.value !== value)) {
      throw new Error(`GraphQL: expected name ${value ?? ''}, got ${JSON.stringify(token.value)}`);
    }
    return token.value;
  }

  private acceptPunct(value: string): boolean {
    const token = this.peek();
    if (token.kind === 'punct' && token.value === value) {
      this.index += 1;
      return true;
    }
    return false;
  }

  parseDocument(): GqlOperation[] {
    const operations: GqlOperation[] = [];
    while (this.peek().kind !== 'eof') {
      operations.push(this.parseOperation());
    }
    return operations;
  }

  private parseOperation(): GqlOperation {
    let operation: 'query' | 'mutation' = 'query';
    const token = this.peek();
    if (token.kind === 'name' && (token.value === 'query' || token.value === 'mutation')) {
      operation = this.next().value as 'query' | 'mutation';
    }
    let name: string | null = null;
    if (this.peek().kind === 'name') name = this.next().value;
    // Variable definitions: ($name: Type, ...) — values come from the request, so skip.
    if (this.acceptPunct('(')) {
      let depth = 1;
      while (depth > 0) {
        const next = this.next();
        if (next.kind === 'punct' && next.value === '(') depth += 1;
        else if (next.kind === 'punct' && next.value === ')') depth -= 1;
        else if (next.kind === 'eof') throw new Error('GraphQL: unterminated variable definitions');
      }
    }
    // Directives (@...) — skip.
    while (this.acceptPunct('@')) {
      this.expectName();
      if (this.acceptPunct('(')) this.parseArguments();
    }
    const selection = this.parseSelectionSet();
    return { operation, name, selection };
  }

  private parseSelectionSet(): SelectionItem[] {
    this.expectPunct('{');
    const items: SelectionItem[] = [];
    while (!(this.peek().kind === 'punct' && this.peek().value === '}')) {
      items.push(this.parseSelectionItem());
    }
    this.expectPunct('}');
    return items;
  }

  private parseSelectionItem(): SelectionItem {
    if (this.peek().kind === 'punct' && this.peek().value === '...') {
      this.next();
      let typeCondition: string | null = null;
      if (this.peek().kind === 'name' && this.peek().value === 'on') {
        this.next();
        typeCondition = this.expectName();
      }
      while (this.acceptPunct('@')) {
        this.expectName();
        if (this.acceptPunct('(')) this.parseArguments();
      }
      return { kind: 'fragment', typeCondition, selection: this.parseSelectionSet() };
    }
    let alias: string | null = null;
    let name = this.expectName();
    if (this.peek().kind === 'punct' && this.peek().value === ':') {
      this.next();
      alias = name;
      name = this.expectName();
    }
    let args = new Map<string, GqlValue>();
    if (this.acceptPunct('(')) args = this.parseArguments();
    while (this.acceptPunct('@')) {
      this.expectName();
      if (this.acceptPunct('(')) this.parseArguments();
    }
    let selection: SelectionItem[] | null = null;
    if (this.peek().kind === 'punct' && this.peek().value === '{') {
      selection = this.parseSelectionSet();
    }
    return { kind: 'field', alias, name, args, selection };
  }

  private parseArguments(): Map<string, GqlValue> {
    const args = new Map<string, GqlValue>();
    while (!(this.peek().kind === 'punct' && this.peek().value === ')')) {
      const name = this.expectName();
      this.expectPunct(':');
      args.set(name, this.parseValue());
    }
    this.expectPunct(')');
    return args;
  }

  private parseValue(): GqlValue {
    const token = this.next();
    if (token.kind === 'punct' && token.value === '$') {
      return { kind: 'var', name: this.expectName() };
    }
    if (token.kind === 'punct' && token.value === '[') {
      const values: GqlValue[] = [];
      while (!(this.peek().kind === 'punct' && this.peek().value === ']')) {
        values.push(this.parseValue());
      }
      this.expectPunct(']');
      return { kind: 'list', values };
    }
    if (token.kind === 'punct' && token.value === '{') {
      const fields = new Map<string, GqlValue>();
      while (!(this.peek().kind === 'punct' && this.peek().value === '}')) {
        const name = this.expectName();
        this.expectPunct(':');
        fields.set(name, this.parseValue());
      }
      this.expectPunct('}');
      return { kind: 'object', fields };
    }
    if (token.kind === 'int') return { kind: 'int', value: Number.parseInt(token.value, 10) };
    if (token.kind === 'float') return { kind: 'float', value: Number.parseFloat(token.value) };
    if (token.kind === 'string') return { kind: 'string', value: token.value };
    if (token.kind === 'name') {
      if (token.value === 'true') return { kind: 'bool', value: true };
      if (token.value === 'false') return { kind: 'bool', value: false };
      if (token.value === 'null') return { kind: 'null' };
      return { kind: 'enum', value: token.value };
    }
    throw new Error(`GraphQL: unexpected value token ${JSON.stringify(token.value)}`);
  }
}

// ---------------------------------------------------------------- GraphQL values

interface GqlContext {
  forge: Forge;
  variables: Record<string, unknown>;
  errors: Array<{ message: string }>;
}

type GqlParent = { __typename: string; [key: string]: unknown };

function evalValue(value: GqlValue, ctx: GqlContext): unknown {
  switch (value.kind) {
    case 'var':
      return ctx.variables[value.name] ?? null;
    case 'int':
    case 'float':
    case 'string':
    case 'bool':
      return value.value;
    case 'null':
      return null;
    case 'enum':
      return value.value;
    case 'list':
      return value.values.map((item) => evalValue(item, ctx));
    case 'object': {
      const result: Record<string, unknown> = {};
      for (const [key, child] of value.fields) result[key] = evalValue(child, ctx);
      return result;
    }
  }
}

function argValue(field: Extract<SelectionItem, { kind: 'field' }>, name: string, ctx: GqlContext): unknown {
  const raw = field.args.get(name);
  return raw === undefined ? undefined : evalValue(raw, ctx);
}

function globalId(kind: string, ...parts: Array<string | number>): string {
  return b64urlEncode(`${kind}:${parts.join(':')}`);
}

function decodeGlobalId(id: string): { kind: string; parts: string[] } | null {
  const text = b64urlDecode(id);
  if (text === null) return null;
  const [kind, ...parts] = text.split(':');
  if (kind === undefined || parts.length === 0) return null;
  return { kind, parts };
}

function repoByDbId(forge: Forge, dbId: number): RepoRecord | undefined {
  for (const repo of forge.repos.values()) {
    if (repo.dbId === dbId) return repo;
  }
  return undefined;
}

function repoValue(repo: RepoRecord): GqlParent {
  return { __typename: 'Repository', repo };
}

function issueValue(repo: RepoRecord, issue: IssueRecord): GqlParent {
  return { __typename: 'Issue', repo, issue };
}

function pullValue(repo: RepoRecord, pull: PullRecord): GqlParent {
  return { __typename: 'PullRequest', repo, pull };
}

function decodeCursor(cursor: unknown): number | null {
  if (typeof cursor !== 'string') return null;
  const text = b64urlDecode(cursor);
  if (text === null) return null;
  const match = /^cursor:(\d+)$/.exec(text);
  return match === null ? null : Number.parseInt(match[1]!, 10);
}

function encodeCursor(number: number): string {
  return b64urlEncode(`cursor:${number}`);
}

const INTROSPECTION: Record<string, { kind: string; fields: string[]; enumValues: string[] }> = {
  Issue: { kind: 'OBJECT', fields: ['id', 'number', 'title', 'state', 'body', 'createdAt', 'updatedAt', 'url'], enumValues: [] },
  PullRequest: { kind: 'OBJECT', fields: ['id', 'number', 'title', 'headRefName', 'baseRefName', 'mergeable', 'state', 'merged', 'files', 'body', 'createdAt', 'url'], enumValues: [] },
  Repository: { kind: 'OBJECT', fields: ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequests', 'pullRequest', 'createdAt', 'url'], enumValues: [] },
  SearchType: { kind: 'ENUM', fields: [], enumValues: ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION', 'COMMIT', 'CODE', 'PACKAGE', 'MARKETPLACE', 'TOPIC'] },
  IssueState: { kind: 'ENUM', fields: [], enumValues: ['OPEN', 'CLOSED'] },
  PullRequestState: { kind: 'ENUM', fields: [], enumValues: ['OPEN', 'CLOSED', 'MERGED'] },
  MergeableState: { kind: 'ENUM', fields: [], enumValues: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'] },
  RepositoryPermission: { kind: 'ENUM', fields: [], enumValues: ['ADMIN', 'MAINTAIN', 'WRITE', 'TRIAGE', 'READ'] },
  PullRequestMergeMethod: { kind: 'ENUM', fields: [], enumValues: ['MERGE', 'SQUASH', 'REBASE'] },
  IssueOrderField: { kind: 'ENUM', fields: [], enumValues: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'] },
  OrderDirection: { kind: 'ENUM', fields: [], enumValues: ['ASC', 'DESC'] },
};

function pullMergeable(repo: RepoRecord, pull: PullRecord): string {
  if (pull.merged || pull.state !== 'open') return 'UNKNOWN';
  const headOid = refCommit(repo, `refs/heads/${pull.headRef}`);
  const baseOid = refCommit(repo, `refs/heads/${pull.baseRef}`);
  if (headOid === undefined || baseOid === undefined) return 'UNKNOWN';
  return mergeConflict(repo, headOid, baseOid) ? 'CONFLICTING' : 'MERGEABLE';
}

type FieldResolver = (parent: GqlParent, field: Extract<SelectionItem, { kind: 'field' }>, ctx: GqlContext) => unknown;

function connectionOf<T>(nodes: T[], first: number | undefined, afterNumber: number | null, descending: boolean, keyOf: (item: T) => number): { nodes: T[]; hasNextPage: boolean; endCursor: string | null } {
  let filtered = nodes;
  if (afterNumber !== null) {
    filtered = filtered.filter((item) => (descending ? keyOf(item) < afterNumber : keyOf(item) > afterNumber));
  }
  const limit = first === undefined || first === null ? filtered.length : Math.max(0, first as number);
  const page = filtered.slice(0, limit);
  const hasNextPage = filtered.length > page.length;
  const endCursor = page.length === 0 ? null : encodeCursor(keyOf(page[page.length - 1]!));
  return { nodes: page, hasNextPage, endCursor };
}

const RESOLVERS: Record<string, Record<string, FieldResolver>> = {
  Query: {
    viewer: () => ({ __typename: 'User', login: VIEWER_LOGIN, id: VIEWER_ID }),
    repository: (_parent, field, ctx) => {
      const owner = argValue(field, 'owner', ctx);
      const name = argValue(field, 'name', ctx);
      if (typeof owner !== 'string' || typeof name !== 'string') return null;
      const repo = ctx.forge.getRepo(owner, name);
      return repo === undefined ? null : repoValue(repo);
    },
    node: (_parent, field, ctx) => {
      const id = argValue(field, 'id', ctx);
      if (typeof id !== 'string') return null;
      const decoded = decodeGlobalId(id);
      if (decoded === null) return null;
      if (decoded.kind === 'Repository') {
        const repo = repoByDbId(ctx.forge, Number.parseInt(decoded.parts[0] ?? '', 10));
        return repo === undefined ? null : repoValue(repo);
      }
      if (decoded.kind === 'Issue') {
        const repo = repoByDbId(ctx.forge, Number.parseInt(decoded.parts[0] ?? '', 10));
        const issue = repo?.issues.get(Number.parseInt(decoded.parts[1] ?? '', 10));
        return issue === undefined || repo === undefined ? null : issueValue(repo, issue);
      }
      if (decoded.kind === 'PullRequest') {
        const repo = repoByDbId(ctx.forge, Number.parseInt(decoded.parts[0] ?? '', 10));
        const pull = repo?.pulls.get(Number.parseInt(decoded.parts[1] ?? '', 10));
        return pull === undefined || repo === undefined ? null : pullValue(repo, pull);
      }
      return null;
    },
    __type: (_parent, field, ctx) => {
      const name = argValue(field, 'name', ctx);
      if (typeof name !== 'string') return null;
      const info = INTROSPECTION[name];
      if (info === undefined) return null;
      return {
        __typename: '__Type',
        name,
        kind: info.kind,
        fields: info.fields.map((fieldName) => ({ __typename: '__Field', name: fieldName })),
        enumValues: info.enumValues.map((value) => ({ __typename: '__EnumValue', name: value })),
      };
    },
  },
  Mutation: {
    createIssue: (_parent, field, ctx) => {
      const input = argValue(field, 'input', ctx) as Record<string, unknown> | undefined;
      if (input === undefined) return null;
      const decoded = typeof input.repositoryId === 'string' ? decodeGlobalId(input.repositoryId) : null;
      if (decoded === null || decoded.kind !== 'Repository') return null;
      const repo = repoByDbId(ctx.forge, Number.parseInt(decoded.parts[0] ?? '', 10));
      if (repo === undefined) return null;
      const title = typeof input.title === 'string' ? input.title : '';
      const issue: IssueRecord = {
        id: issueIdCounter++,
        number: repo.nextIssueNumber++,
        title,
        body: typeof input.body === 'string' ? input.body : '',
        state: 'open',
        labels: [],
        createdSeq: ++globalSeq,
      };
      repo.issues.set(issue.number, issue);
      return { __typename: 'CreateIssuePayload', issue: issueValue(repo, issue) };
    },
    closeIssue: (_parent, field, ctx) => {
      const input = argValue(field, 'input', ctx) as Record<string, unknown> | undefined;
      if (input === undefined) return null;
      const decoded = typeof input.issueId === 'string' ? decodeGlobalId(input.issueId) : null;
      if (decoded === null || decoded.kind !== 'Issue') return null;
      const repo = repoByDbId(ctx.forge, Number.parseInt(decoded.parts[0] ?? '', 10));
      const issue = repo?.issues.get(Number.parseInt(decoded.parts[1] ?? '', 10));
      if (repo === undefined || issue === undefined) return null;
      issue.state = 'closed';
      issue.jsonPayload = undefined;
      return { __typename: 'CloseIssuePayload', issue: issueValue(repo, issue) };
    },
    createPullRequest: (_parent, field, ctx) => {
      const input = argValue(field, 'input', ctx) as Record<string, unknown> | undefined;
      if (input === undefined) return null;
      const decoded = typeof input.repositoryId === 'string' ? decodeGlobalId(input.repositoryId) : null;
      if (decoded === null || decoded.kind !== 'Repository') return null;
      const repo = repoByDbId(ctx.forge, Number.parseInt(decoded.parts[0] ?? '', 10));
      if (repo === undefined) return null;
      const head = typeof input.headRefName === 'string' ? input.headRefName : '';
      const base = typeof input.baseRefName === 'string' ? input.baseRefName : '';
      if (branchTip(repo, head) === undefined || branchTip(repo, base) === undefined) return null;
      const pull: PullRecord = {
        id: issueIdCounter++,
        number: repo.nextPullNumber++,
        title: typeof input.title === 'string' ? input.title : '',
        body: typeof input.body === 'string' ? input.body : '',
        state: 'open',
        headRef: head,
        baseRef: base,
        merged: false,
        mergedAt: null,
        mergeCommitSha: null,
        createdSeq: ++globalSeq,
      };
      repo.pulls.set(pull.number, pull);
      return { __typename: 'CreatePullRequestPayload', pullRequest: pullValue(repo, pull) };
    },
    mergePullRequest: (_parent, field, ctx) => {
      const input = argValue(field, 'input', ctx) as Record<string, unknown> | undefined;
      if (input === undefined) return null;
      const decoded = typeof input.pullRequestId === 'string' ? decodeGlobalId(input.pullRequestId) : null;
      if (decoded === null || decoded.kind !== 'PullRequest') return null;
      const repo = repoByDbId(ctx.forge, Number.parseInt(decoded.parts[0] ?? '', 10));
      const pull = repo?.pulls.get(Number.parseInt(decoded.parts[1] ?? '', 10));
      if (repo === undefined || pull === undefined) return null;
      const method = typeof input.mergeMethod === 'string' ? input.mergeMethod.toLowerCase() : 'merge';
      mergePull(repo, pull, method);
      return { __typename: 'MergePullRequestPayload', pullRequest: pullValue(repo, pull) };
    },
    addComment: (_parent, field, ctx) => {
      const input = argValue(field, 'input', ctx) as Record<string, unknown> | undefined;
      if (input === undefined) return null;
      const decoded = typeof input.subjectId === 'string' ? decodeGlobalId(input.subjectId) : null;
      if (decoded === null) return null;
      const repo = repoByDbId(ctx.forge, Number.parseInt(decoded.parts[0] ?? '', 10));
      if (repo === undefined) return null;
      const body = typeof input.body === 'string' ? input.body : '';
      if (decoded.kind === 'Issue') {
        const issueNumber = Number.parseInt(decoded.parts[1] ?? '', 10);
        const issue = repo.issues.get(issueNumber);
        if (issue === undefined) return null;
        const comment: CommentRecord = { id: commentIdCounter++, body, createdSeq: ++globalSeq };
        const list = repo.comments.get(issueNumber) ?? [];
        list.push(comment);
        repo.comments.set(issueNumber, list);
        const node = { __typename: 'IssueComment', id: globalId('IssueComment', repo.dbId, issueNumber, comment.id), body };
        return { __typename: 'AddCommentPayload', commentEdge: { __typename: 'IssueCommentEdge', node } };
      }
      return null;
    },
  },
  Repository: {
    id: (parent) => globalId('Repository', (parent.repo as RepoRecord).dbId),
    databaseId: (parent) => (parent.repo as RepoRecord).dbId,
    name: (parent) => (parent.repo as RepoRecord).name,
    nameWithOwner: (parent) => `${(parent.repo as RepoRecord).owner}/${(parent.repo as RepoRecord).name}`,
    owner: (parent) => ({ __typename: 'User', login: (parent.repo as RepoRecord).owner, id: VIEWER_ID }),
    defaultBranchRef: (parent) => {
      const repo = parent.repo as RepoRecord;
      return branchTip(repo, repo.defaultBranch) === undefined ? null : { __typename: 'Ref', name: repo.defaultBranch };
    },
    viewerPermission: () => 'ADMIN',
    hasIssuesEnabled: () => true,
    issue: (parent, field, ctx) => {
      const repo = parent.repo as RepoRecord;
      const number = argValue(field, 'number', ctx);
      const issue = repo.issues.get(typeof number === 'number' ? number : -1);
      return issue === undefined ? null : issueValue(repo, issue);
    },
    issues: (parent, field, ctx) => {
      const repo = parent.repo as RepoRecord;
      const first = argValue(field, 'first', ctx) as number | undefined;
      const after = argValue(field, 'after', ctx);
      const states = (argValue(field, 'states', ctx) as string[] | undefined) ?? [];
      const orderBy = (argValue(field, 'orderBy', ctx) as Record<string, unknown> | undefined) ?? {};
      const direction = orderBy.direction === 'ASC' ? 'ASC' : 'DESC';
      let list = [...repo.issues.values()];
      if (states.length > 0) {
        const wanted = new Set(states.map((state) => String(state).toLowerCase()));
        list = list.filter((issue) => wanted.has(issue.state));
      }
      list.sort((a, b) => (direction === 'ASC' ? a.number - b.number : b.number - a.number));
      const page = connectionOf(list, first, decodeCursor(after), direction === 'DESC', (issue) => issue.number);
      return {
        __typename: 'IssueConnection',
        nodes: page.nodes.map((issue) => issueValue(repo, issue)),
        pageInfo: { __typename: 'PageInfo', hasNextPage: page.hasNextPage, endCursor: page.endCursor },
        totalCount: list.length,
      };
    },
    pullRequest: (parent, field, ctx) => {
      const repo = parent.repo as RepoRecord;
      const number = argValue(field, 'number', ctx);
      const pull = repo.pulls.get(typeof number === 'number' ? number : -1);
      return pull === undefined ? null : pullValue(repo, pull);
    },
    pullRequests: (parent, field, ctx) => {
      const repo = parent.repo as RepoRecord;
      const first = argValue(field, 'first', ctx) as number | undefined;
      const after = argValue(field, 'after', ctx);
      const list = [...repo.pulls.values()].sort((a, b) => b.number - a.number);
      const page = connectionOf(list, first, decodeCursor(after), true, (pull) => pull.number);
      return {
        __typename: 'PullRequestConnection',
        nodes: page.nodes.map((pull) => pullValue(repo, pull)),
        pageInfo: { __typename: 'PageInfo', hasNextPage: page.hasNextPage, endCursor: page.endCursor },
        totalCount: list.length,
      };
    },
  },
  User: {
    login: (parent) => parent.login as string,
    id: () => globalId('User', VIEWER_ID),
    name: () => VIEWER_NAME,
  },
  Issue: {
    id: (parent) => globalId('Issue', (parent.repo as RepoRecord).dbId, (parent.issue as IssueRecord).number),
    number: (parent) => (parent.issue as IssueRecord).number,
    title: (parent) => (parent.issue as IssueRecord).title,
    state: (parent) => ((parent.issue as IssueRecord).state === 'open' ? 'OPEN' : 'CLOSED'),
    body: (parent) => (parent.issue as IssueRecord).body,
  },
  PullRequest: {
    id: (parent) => globalId('PullRequest', (parent.repo as RepoRecord).dbId, (parent.pull as PullRecord).number),
    number: (parent) => (parent.pull as PullRecord).number,
    title: (parent) => (parent.pull as PullRecord).title,
    state: (parent) => {
      const pull = parent.pull as PullRecord;
      if (pull.merged) return 'MERGED';
      return pull.state === 'open' ? 'OPEN' : 'CLOSED';
    },
    headRefName: (parent) => (parent.pull as PullRecord).headRef,
    baseRefName: (parent) => (parent.pull as PullRecord).baseRef,
    mergeable: (parent) => pullMergeable(parent.repo as RepoRecord, parent.pull as PullRecord),
    merged: (parent) => (parent.pull as PullRecord).merged,
    files: (parent, field, ctx) => {
      const repo = parent.repo as RepoRecord;
      const pull = parent.pull as PullRecord;
      const first = argValue(field, 'first', ctx) as number | undefined;
      const changes = pullFiles(repo, pull);
      const limited = first === undefined ? changes : changes.slice(0, first);
      return {
        __typename: 'FileConnection',
        nodes: limited.map((change) => ({ __typename: 'ChangedFile', path: change.filename })),
        pageInfo: { __typename: 'PageInfo', hasNextPage: first !== undefined && changes.length > first, endCursor: null },
        totalCount: changes.length,
      };
    },
  },
  IssueConnection: {
    nodes: (parent) => parent.nodes as unknown[],
    pageInfo: (parent) => parent.pageInfo as GqlParent,
    totalCount: (parent) => parent.totalCount as number,
  },
  PullRequestConnection: {
    nodes: (parent) => parent.nodes as unknown[],
    pageInfo: (parent) => parent.pageInfo as GqlParent,
    totalCount: (parent) => parent.totalCount as number,
  },
  FileConnection: {
    nodes: (parent) => parent.nodes as unknown[],
    pageInfo: (parent) => parent.pageInfo as GqlParent,
    totalCount: (parent) => parent.totalCount as number,
  },
  ChangedFile: {
    path: (parent) => parent.path as string,
  },
  PageInfo: {
    hasNextPage: (parent) => parent.hasNextPage as boolean,
    endCursor: (parent) => (parent.endCursor as string | null),
  },
  Ref: {
    name: (parent) => parent.name as string,
  },
  __Type: {
    name: (parent) => parent.name as string,
    kind: (parent) => parent.kind as string,
    fields: (parent) => parent.fields as GqlParent[],
    enumValues: (parent) => parent.enumValues as GqlParent[],
  },
  __Field: {
    name: (parent) => parent.name as string,
  },
  __EnumValue: {
    name: (parent) => parent.name as string,
  },
  IssueComment: {
    id: (parent) => parent.id as string,
    body: (parent) => parent.body as string,
  },
  IssueCommentEdge: {
    node: (parent) => parent.node as GqlParent,
  },
  CreateIssuePayload: {
    issue: (parent) => parent.issue as GqlParent,
  },
  CloseIssuePayload: {
    issue: (parent) => parent.issue as GqlParent,
  },
  CreatePullRequestPayload: {
    pullRequest: (parent) => parent.pullRequest as GqlParent,
  },
  MergePullRequestPayload: {
    pullRequest: (parent) => parent.pullRequest as GqlParent,
  },
  AddCommentPayload: {
    commentEdge: (parent) => parent.commentEdge as GqlParent,
  },
};

function executeSelection(selection: SelectionItem[], parentType: string, parent: GqlParent, ctx: GqlContext): Record<string, unknown> {
  const result: Record<string, unknown> = {};
  for (const item of selection) {
    if (item.kind === 'fragment') {
      if (item.typeCondition === null || item.typeCondition === parentType) {
        Object.assign(result, executeSelection(item.selection, parentType, parent, ctx));
      }
      continue;
    }
    const key = item.alias ?? item.name;
    if (item.name === '__typename') {
      result[key] = parentType;
      continue;
    }
    const resolvers = RESOLVERS[parentType];
    const resolver = resolvers?.[item.name];
    if (resolver === undefined) {
      ctx.errors.push({ message: `Cannot query field "${item.name}" on type "${parentType}".` });
      result[key] = null;
      continue;
    }
    let value: unknown;
    try {
      value = resolver(parent, item, ctx);
    } catch (error) {
      ctx.errors.push({ message: error instanceof Error ? error.message : String(error) });
      result[key] = null;
      continue;
    }
    if (item.selection === null || value === null || value === undefined) {
      result[key] = value ?? null;
      continue;
    }
    if (Array.isArray(value)) {
      result[key] = value.map((element) => {
        if (element !== null && typeof element === 'object' && '__typename' in (element as Record<string, unknown>)) {
          const typed = element as GqlParent;
          return executeSelection(item.selection!, typed.__typename, typed, ctx);
        }
        return element;
      });
      continue;
    }
    if (typeof value === 'object' && '__typename' in (value as Record<string, unknown>)) {
      const typed = value as GqlParent;
      result[key] = executeSelection(item.selection, typed.__typename, typed, ctx);
      continue;
    }
    result[key] = value;
  }
  return result;
}

function executeGraphQlOperation(forge: Forge, operation: GqlOperation, variables: Record<string, unknown>): Record<string, unknown> {
  const ctx: GqlContext = { forge, variables, errors: [] };
  const rootType = operation.operation === 'mutation' ? 'Mutation' : 'Query';
  const root: GqlParent = { __typename: rootType };
  const data = executeSelection(operation.selection, rootType, root, ctx);
  const response: Record<string, unknown> = { data };
  if (ctx.errors.length > 0) response.errors = ctx.errors;
  return response;
}

async function handleGraphQl(forge: Forge, req: IncomingMessage, res: ServerResponse, body: Buffer): Promise<boolean> {
  if (!requireAuth(req, res)) return true;
  let parsed: unknown;
  try {
    parsed = JSON.parse(body.toString('utf8'));
  } catch {
    sendJson(res, 400, { errors: [{ message: 'Problems parsing JSON' }] });
    return true;
  }
  const requests = Array.isArray(parsed) ? parsed : [parsed];
  const responses: Array<Record<string, unknown>> = [];
  for (const request of requests) {
    const requestObject = (typeof request === 'object' && request !== null ? request : {}) as Record<string, unknown>;
    const query = typeof requestObject.query === 'string' ? requestObject.query : '';
    const variables = (typeof requestObject.variables === 'object' && requestObject.variables !== null
      ? requestObject.variables
      : {}) as Record<string, unknown>;
    try {
      const operations = new GqlParser(gqlTokenize(query)).parseDocument();
      if (operations.length === 0) {
        responses.push({ data: {}, errors: [{ message: 'No operation provided' }] });
        continue;
      }
      const operationName = typeof requestObject.operationName === 'string' ? requestObject.operationName : null;
      const operation = operationName === null
        ? operations[0]!
        : operations.find((candidate) => candidate.name === operationName) ?? operations[0]!;
      responses.push(executeGraphQlOperation(forge, operation, variables));
    } catch (error) {
      responses.push({ data: {}, errors: [{ message: error instanceof Error ? error.message : String(error) }] });
    }
  }
  sendJson(res, 200, Array.isArray(parsed) ? responses : responses[0]);
  return true;
}

// ---------------------------------------------------------------- MCP (streamable HTTP, JSON-RPC 2.0)

const MCP_SUPPORTED_VERSIONS = ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'];

interface McpToolDef {
  name: string;
  description: string;
  inputSchema: {
    type: 'object';
    properties: Record<string, { type: string; description: string }>;
    required: string[];
  };
  handler: (forge: Forge, args: Record<string, unknown>) => Record<string, unknown>;
}

/** First defined argument among the given names (the suite maps documented names to schema properties). */
function pickArg(args: Record<string, unknown>, ...names: string[]): unknown {
  for (const name of names) {
    if (args[name] !== undefined && args[name] !== null) return args[name];
  }
  return undefined;
}

function mcpTextResult(value: unknown): Record<string, unknown> {
  return { content: [{ type: 'text', text: typeof value === 'string' ? value : JSON.stringify(value) }] };
}

function mcpErrorResult(message: string): Record<string, unknown> {
  return { content: [{ type: 'text', text: message }], isError: true };
}

function mcpRequireString(args: Record<string, unknown>, ...names: string[]): string {
  const value = pickArg(args, ...names);
  if (typeof value !== 'string' || value === '') {
    throw new Error(`Missing required argument: ${names[0]}`);
  }
  return value;
}

function mcpRepo(forge: Forge, args: Record<string, unknown>): RepoRecord {
  const owner = mcpRequireString(args, 'owner', 'owner_login', 'org', 'organization', 'user', 'user_login', 'login', 'account', 'namespace', 'owner_name');
  const repoName = mcpRequireString(args, 'repo', 'repository', 'repository_name', 'repo_name', 'repo_slug', 'project', 'project_name');
  const repo = forge.getRepo(owner, repoName);
  if (repo === undefined) throw new Error(`Repository not found: ${owner}/${repoName}`);
  return repo;
}

const MCP_TOOLS: McpToolDef[] = [
  {
    name: 'create_repo',
    description: 'Create a new repository for the authenticated user.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'The name of the repository.' },
        description: { type: 'string', description: 'A short description of the repository.' },
        private: { type: 'boolean', description: 'Whether the repository is private.' },
      },
      required: ['name'],
    },
    handler: (forge, args) => {
      const name = mcpRequireString(args, 'name', 'repo', 'repository', 'repository_name', 'repo_name');
      if (forge.getRepo(VIEWER_LOGIN, name) !== undefined) {
        throw new Error(`Repository already exists: ${VIEWER_LOGIN}/${name}`);
      }
      const description = typeof pickArg(args, 'description', 'about', 'summary', 'body') === 'string'
        ? (pickArg(args, 'description', 'about', 'summary', 'body') as string)
        : '';
      const isPrivate = pickArg(args, 'private', 'is_private') === true;
      const repo = forge.createRepo(VIEWER_LOGIN, name, description, isPrivate);
      return mcpTextResult(repoJson(repo));
    },
  },
  {
    name: 'get_repo',
    description: 'Get a repository by owner and name.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The owner login of the repository.' },
        repo: { type: 'string', description: 'The name of the repository.' },
      },
      required: ['owner', 'repo'],
    },
    handler: (forge, args) => mcpTextResult(repoJson(mcpRepo(forge, args))),
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The owner login of the repository.' },
        repo: { type: 'string', description: 'The name of the repository.' },
        title: { type: 'string', description: 'The title of the issue.' },
        body: { type: 'string', description: 'The body of the issue.' },
      },
      required: ['owner', 'repo', 'title'],
    },
    handler: (forge, args) => {
      const repo = mcpRepo(forge, args);
      const title = mcpRequireString(args, 'title', 'issue_title', 'subject');
      const body = typeof pickArg(args, 'body', 'issue_body', 'description', 'content', 'text', 'comment') === 'string'
        ? (pickArg(args, 'body', 'issue_body', 'description', 'content', 'text', 'comment') as string)
        : '';
      const issue: IssueRecord = {
        id: issueIdCounter++,
        number: repo.nextIssueNumber++,
        title,
        body,
        state: 'open',
        labels: [],
        createdSeq: ++globalSeq,
      };
      repo.issues.set(issue.number, issue);
      return mcpTextResult(issueJson(issue));
    },
  },
  {
    name: 'list_issues',
    description: 'List issues in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The owner login of the repository.' },
        repo: { type: 'string', description: 'The name of the repository.' },
        state: { type: 'string', description: 'Filter by state: open, closed, or all.' },
      },
      required: ['owner', 'repo'],
    },
    handler: (forge, args) => {
      const repo = mcpRepo(forge, args);
      const state = typeof pickArg(args, 'state', 'status') === 'string'
        ? (pickArg(args, 'state', 'status') as string)
        : 'open';
      let list = [...repo.issues.values()];
      if (state !== 'all') list = list.filter((issue) => issue.state === state);
      list.sort((a, b) => b.createdSeq - a.createdSeq);
      return mcpTextResult(list.map(issueJson));
    },
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The owner login of the repository.' },
        repo: { type: 'string', description: 'The name of the repository.' },
        title: { type: 'string', description: 'The title of the pull request.' },
        head: { type: 'string', description: 'The head branch name.' },
        base: { type: 'string', description: 'The base branch name.' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
    },
    handler: (forge, args) => {
      const repo = mcpRepo(forge, args);
      const title = mcpRequireString(args, 'title', 'pr_title', 'pull_request_title', 'subject');
      const head = stripOwnerPrefix(mcpRequireString(args, 'head', 'head_ref', 'head_branch', 'pull_request_head', 'pr_head', 'source', 'source_ref', 'source_branch', 'from', 'from_branch', 'branch'));
      const base = stripOwnerPrefix(mcpRequireString(args, 'base', 'base_ref', 'base_branch', 'pull_request_base', 'pr_base', 'target', 'target_ref', 'target_branch', 'into', 'into_branch'));
      if (branchTip(repo, head) === undefined || branchTip(repo, base) === undefined) {
        throw new Error(`Head or base branch does not exist: ${head} -> ${base}`);
      }
      const pull: PullRecord = {
        id: issueIdCounter++,
        number: repo.nextPullNumber++,
        title,
        body: typeof pickArg(args, 'body', 'issue_body', 'description', 'content', 'text') === 'string'
          ? (pickArg(args, 'body', 'issue_body', 'description', 'content', 'text') as string)
          : '',
        state: 'open',
        headRef: head,
        baseRef: base,
        merged: false,
        mergedAt: null,
        mergeCommitSha: null,
        createdSeq: ++globalSeq,
      };
      repo.pulls.set(pull.number, pull);
      return mcpTextResult(pullJson(repo, pull));
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The owner login of the repository.' },
        repo: { type: 'string', description: 'The name of the repository.' },
        pull_number: { type: 'integer', description: 'The number of the pull request.' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
    handler: (forge, args) => {
      const repo = mcpRepo(forge, args);
      const numberRaw = pickArg(args, 'pull_number', 'pull_request_number', 'pr_number', 'number', 'issue_number', 'index');
      const number = typeof numberRaw === 'number' ? numberRaw : Number.parseInt(String(numberRaw ?? ''), 10);
      if (!Number.isFinite(number)) throw new Error('Missing required argument: pull_number');
      const pull = repo.pulls.get(number);
      if (pull === undefined) throw new Error(`Pull request not found: #${number}`);
      const merged = mergePull(repo, pull, 'merge');
      if (merged === null) throw new Error(`Pull request #${number} cannot be merged: merge conflict`);
      return mcpTextResult({ sha: merged, merged: true, message: 'Pull request successfully merged' });
    },
  },
];

async function handleMcp(forge: Forge, req: IncomingMessage, res: ServerResponse, body: Buffer): Promise<boolean> {
  if (!requireAuth(req, res)) return true;
  let parsed: unknown;
  try {
    parsed = JSON.parse(body.toString('utf8'));
  } catch {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } });
    return true;
  }
  const message = (typeof parsed === 'object' && parsed !== null ? parsed : {}) as Record<string, unknown>;
  const id = message.id ?? null;
  const isNotification = message.id === undefined;
  const method = typeof message.method === 'string' ? message.method : '';
  const params = (typeof message.params === 'object' && message.params !== null ? message.params : {}) as Record<string, unknown>;
  if (isNotification) {
    res.writeHead(202);
    res.end();
    return true;
  }
  const respond = (result: unknown): void => {
    sendJson(res, 200, { jsonrpc: '2.0', id, result });
  };
  const respondError = (code: number, errorMessage: string): void => {
    sendJson(res, 200, { jsonrpc: '2.0', id, error: { code, message: errorMessage } });
  };
  if (method === 'server/discover') {
    respond({
      serverInfo: { name: MCP_NAME, version: MCP_VERSION },
      capabilities: { tools: {} },
      supportedVersions: MCP_SUPPORTED_VERSIONS,
      protocolVersion: '2026-07-28',
    });
    return true;
  }
  if (method === 'initialize') {
    const requested = typeof params.protocolVersion === 'string' ? params.protocolVersion : '';
    const negotiated = MCP_SUPPORTED_VERSIONS.includes(requested) ? requested : '2026-07-28';
    respond({
      protocolVersion: negotiated,
      serverInfo: { name: MCP_NAME, version: MCP_VERSION },
      capabilities: { tools: {} },
    });
    return true;
  }
  if (method === 'tools/list') {
    respond({
      tools: MCP_TOOLS.map((tool) => ({ name: tool.name, description: tool.description, inputSchema: tool.inputSchema })),
    });
    return true;
  }
  if (method === 'tools/call') {
    const name = typeof params.name === 'string' ? params.name : '';
    const args = (typeof params.arguments === 'object' && params.arguments !== null ? params.arguments : {}) as Record<string, unknown>;
    const tool = MCP_TOOLS.find((candidate) => candidate.name === name);
    if (tool === undefined) {
      respondError(-32602, `Unknown tool: ${name}`);
      return true;
    }
    try {
      respond(tool.handler(forge, args));
    } catch (error) {
      respond(mcpErrorResult(error instanceof Error ? error.message : String(error)));
    }
    return true;
  }
  respondError(-32601, `Method not found: ${method}`);
  return true;
}

// ---------------------------------------------------------------- git smart HTTP

const V2_ADVERTISEMENT_BUF = Buffer.concat([
  pktLine('version 2\n'),
  pktLine(`agent=${FORGE_AGENT}\n`),
  pktLine('ls-refs=unborn\n'),
  pktLine('fetch=shallow thin-pack no-progress ofs-delta\n'),
  pktLine('object-format=sha1\n'),
  PKT_FLUSH,
]);

function v2Advertisement(): Buffer {
  return V2_ADVERTISEMENT_BUF;
}

function repoRefsCacheKey(repo: RepoRecord, service: string): string {
  let key = `${service}:${repo.defaultBranch}`;
  for (const [name, oid] of repo.refs) {
    key += `;${name}=${oid}`;
  }
  return key;
}

function v0Advertisement(repo: RepoRecord, service: 'git-upload-pack' | 'git-receive-pack'): Buffer {
  const cacheKey = repoRefsCacheKey(repo, service);
  const cached = repo.advCache.get(cacheKey);
  if (cached !== undefined) return cached;
  const caps = service === 'git-receive-pack'
    ? `report-status side-band-64k delete-refs ofs-delta agent=${FORGE_AGENT} symref=HEAD:refs/heads/${repo.defaultBranch}`
    : `symref=HEAD:refs/heads/${repo.defaultBranch} side-band-64k ofs-delta agent=${FORGE_AGENT}`;
  const chunks: Buffer[] = [pktLine(`# service=${service}\n`), PKT_FLUSH];
  const refs = sortedRefs(repo);
  if (refs.length === 0) {
    chunks.push(pktLine(`${ZERO_OID} capabilities^{}\0${caps}\n`));
  } else {
    refs.forEach((ref, index) => {
      const first = index === 0 ? `\0${caps}` : '';
      chunks.push(pktLine(`${ref.oid} ${ref.name}${first}\n`));
      const object = repo.objects.get(ref.oid);
      if (object !== undefined && object.type === 'tag' && ref.name.startsWith('refs/tags/')) {
        chunks.push(pktLine(`${peelToCommit(repo, ref.oid)} ${ref.name}^{}\n`));
      }
    });
  }
  chunks.push(PKT_FLUSH);
  const built = Buffer.concat(chunks);
  repo.advCache.set(cacheKey, built);
  return built;
}

/** Tree closure (tree + subtrees + blobs) of a tree oid. */
function treeClosureOids(repo: RepoRecord, treeOid: string): Set<string> {
  return collectReachable([treeOid], (oid) => repo.objects.get(oid));
}

interface FetchSelection {
  objects: GitObject[];
  shallow: string[];
  unshallow: string[];
  acks: string[];
}

/**
 * Pick the objects a fetch sends. The walk stops at commits the client fully
 * holds (haves that are not shallow boundaries) and passes through shallow
 * boundaries (the client holds the commit but not its ancestors). Objects are
 * the included commits plus their tree closures, minus what the client holds.
 */
function selectFetch(repo: RepoRecord, wants: readonly string[], haves: readonly string[], shallowIn: readonly string[], depth: number | undefined): FetchSelection {
  const haveSet = new Set(haves);
  const shallowSet = new Set(shallowIn);
  const tagObjects: string[] = [];
  const commitRoots: string[] = [];
  for (const want of wants) {
    const object = repo.objects.get(want);
    if (object === undefined) continue;
    if (object.type === 'tag') {
      tagObjects.push(want);
      commitRoots.push(peelToCommit(repo, want));
    } else if (object.type === 'commit') {
      commitRoots.push(want);
    } else {
      tagObjects.push(want);
    }
  }
  const included = new Set<string>();
  const shallowCandidates = new Set<string>();
  const visited = new Map<string, number>();
  const queue: Array<{ oid: string; gen: number }> = commitRoots.map((oid) => ({ oid, gen: 1 }));
  while (queue.length > 0) {
    const { oid, gen } = queue.shift()!;
    const previousGen = visited.get(oid);
    if (previousGen !== undefined && previousGen <= gen) continue;
    visited.set(oid, gen);
    const object = repo.objects.get(oid);
    if (object === undefined || object.type !== 'commit') continue;
    if (haveSet.has(oid) && !shallowSet.has(oid)) continue;
    if (!shallowSet.has(oid)) {
      if (depth === undefined || gen <= depth) {
        included.add(oid);
        if (depth !== undefined && gen === depth) shallowCandidates.add(oid);
      }
    }
    if (depth === undefined || gen < depth) {
      for (const parent of parseCommit(object.data).parents) {
        queue.push({ oid: parent, gen: gen + 1 });
      }
    }
  }
  const send = new Set<string>();
  for (const oid of included) {
    send.add(oid);
    const object = repo.objects.get(oid);
    if (object !== undefined && object.type === 'commit') {
      for (const reachable of treeClosureOids(repo, parseCommit(object.data).tree)) send.add(reachable);
    }
  }
  for (const tagOid of tagObjects) send.add(tagOid);
  const subtract = new Set<string>();
  for (const oid of haveSet) {
    if (shallowSet.has(oid)) continue;
    for (const reachable of collectReachable([oid], (candidate) => repo.objects.get(candidate))) subtract.add(reachable);
  }
  for (const oid of shallowSet) {
    subtract.add(oid);
    const object = repo.objects.get(oid);
    if (object !== undefined && object.type === 'commit') {
      for (const reachable of treeClosureOids(repo, parseCommit(object.data).tree)) subtract.add(reachable);
    }
  }
  for (const oid of subtract) send.delete(oid);
  const objects = [...send].sort().map((oid) => repo.objects.get(oid)!).filter((object) => object !== undefined);

  const shallow = new Set<string>(shallowCandidates);
  const unshallow: string[] = [];
  for (const boundary of shallowSet) {
    const object = repo.objects.get(boundary);
    const parents = object !== undefined && object.type === 'commit' ? parseCommit(object.data).parents : [];
    if (parents.some((parent) => included.has(parent))) unshallow.push(boundary);
    else shallow.add(boundary);
  }
  const acks: string[] = [];
  for (const have of haves) {
    if (repo.objects.has(have)) acks.push(have);
  }
  return { objects, shallow: [...shallow].sort(), unshallow: unshallow.sort(), acks };
}

function sidebandPackChunks(pack: Buffer): Buffer[] {
  const chunks: Buffer[] = [];
  for (let offset = 0; offset < pack.length; offset += 60000) {
    const slice = pack.subarray(offset, Math.min(pack.length, offset + 60000));
    chunks.push(pktLine(Buffer.concat([Buffer.from([1]), slice])));
  }
  if (chunks.length === 0) chunks.push(pktLine(Buffer.concat([Buffer.from([1]), pack])));
  return chunks;
}

function handleLsRefs(repo: RepoRecord, packets: PktPacket[]): Buffer {
  let peel = false;
  let symrefs = false;
  let unborn = false;
  const prefixes: string[] = [];
  for (const packet of packets) {
    if (packet.kind !== 'data') continue;
    const line = packet.payload.toString('utf8').replace(/\n$/, '');
    if (line === 'peel') peel = true;
    else if (line === 'symrefs') symrefs = true;
    else if (line === 'unborn') unborn = true;
    else if (line.startsWith('ref-prefix ')) prefixes.push(line.slice('ref-prefix '.length));
  }
  const chunks: Buffer[] = [];
  const refs = sortedRefs(repo);
  const matches = (name: string): boolean => prefixes.length === 0 || prefixes.some((prefix) => name.startsWith(prefix));
  if (refs.length === 0) {
    if (unborn && matches('HEAD')) {
      const symref = symrefs ? ` symref-target:refs/heads/${repo.defaultBranch}` : '';
      chunks.push(pktLine(`unborn HEAD${symref}\n`));
    }
  } else {
    const headName = headRefName(repo);
    const head = refs.find((ref) => ref.name === headName);
    if (head !== undefined && matches('HEAD')) {
      const symref = symrefs ? ` symref-target:${headName}` : '';
      chunks.push(pktLine(`${head.oid} HEAD${symref}\n`));
    }
    for (const ref of refs) {
      if (!matches(ref.name)) continue;
      let line = `${ref.oid} ${ref.name}`;
      const object = repo.objects.get(ref.oid);
      if (peel && object !== undefined && object.type === 'tag' && ref.name.startsWith('refs/tags/')) {
        line += ` peeled:${peelToCommit(repo, ref.oid)}`;
      }
      chunks.push(pktLine(`${line}\n`));
    }
  }
  chunks.push(PKT_FLUSH);
  return Buffer.concat(chunks);
}

function handleFetchV2(repo: RepoRecord, packets: PktPacket[]): Buffer {
  const wants: string[] = [];
  const haves: string[] = [];
  const shallow: string[] = [];
  let depth: number | undefined;
  for (const packet of packets) {
    if (packet.kind !== 'data') continue;
    const line = packet.payload.toString('utf8').replace(/\n$/, '');
    if (line.startsWith('want ')) wants.push(line.slice(5).trim());
    else if (line.startsWith('have ')) haves.push(line.slice(5).trim());
    else if (line.startsWith('shallow ')) shallow.push(line.slice(8).trim());
    else if (line.startsWith('deepen ')) {
      const parsed = Number.parseInt(line.slice(7).trim(), 10);
      if (Number.isFinite(parsed)) depth = parsed;
    }
  }
  const selection = selectFetch(repo, wants, haves, shallow, depth);
  const pack = writePack(selection.objects);
  const chunks: Buffer[] = [];
  chunks.push(pktLine('acknowledgments\n'));
  if (selection.acks.length === 0) {
    chunks.push(pktLine('NAK\n'));
  } else {
    for (const ack of selection.acks) chunks.push(pktLine(`ACK ${ack}\n`));
    chunks.push(pktLine('ready\n'));
  }
  chunks.push(PKT_FLUSH);
  if (selection.shallow.length > 0 || selection.unshallow.length > 0) {
    chunks.push(pktLine('shallow-info\n'));
    for (const oid of selection.shallow) chunks.push(pktLine(`shallow ${oid}\n`));
    for (const oid of selection.unshallow) chunks.push(pktLine(`unshallow ${oid}\n`));
    chunks.push(PKT_FLUSH);
  }
  chunks.push(pktLine('packfile\n'));
  for (const chunk of sidebandPackChunks(pack)) chunks.push(chunk);
  chunks.push(PKT_FLUSH);
  return Buffer.concat(chunks);
}

function handleFetchV0(repo: RepoRecord, packets: PktPacket[]): Buffer {
  const wants: string[] = [];
  const haves: string[] = [];
  let depth: number | undefined;
  for (const packet of packets) {
    if (packet.kind !== 'data') continue;
    const line = packet.payload.toString('utf8').replace(/\n$/, '');
    if (line.startsWith('want ')) wants.push(line.slice(5).trim());
    else if (line.startsWith('have ')) haves.push(line.slice(5).trim());
    else if (line.startsWith('deepen ')) {
      const parsed = Number.parseInt(line.slice(7).trim(), 10);
      if (Number.isFinite(parsed)) depth = parsed;
    }
  }
  const selection = selectFetch(repo, wants, haves, [], depth);
  const pack = writePack(selection.objects);
  const chunks = sidebandPackChunks(pack);
  chunks.push(PKT_FLUSH);
  return Buffer.concat(chunks);
}

interface PushCommandResult {
  ref: string;
  ok: boolean;
  reason: string;
}

function handleReceivePack(repo: RepoRecord, body: Buffer): Buffer {
  const { packets, rest } = splitPktLinesAndRest(body);
  const commands: Array<{ oldOid: string; newOid: string; ref: string }> = [];
  for (const packet of packets) {
    if (packet.kind !== 'data') continue;
    let line = packet.payload.toString('utf8').replace(/\n$/, '');
    const nul = line.indexOf('\0');
    if (nul >= 0) line = line.slice(0, nul);
    const parts = line.split(' ');
    if (parts.length >= 3) commands.push({ oldOid: parts[0]!, newOid: parts[1]!, ref: parts.slice(2).join(' ') });
  }
  const results: PushCommandResult[] = [];
  let unpackOk = true;
  const needsPack = commands.some((command) => command.newOid !== ZERO_OID);
  if (needsPack && rest.length > 0) {
    try {
      for (const object of readPack(rest)) {
        storeObject(repo, object.type, object.data);
      }
    } catch {
      unpackOk = false;
    }
  }
  for (const command of commands) {
    const current = repo.refs.get(command.ref);
    if (command.newOid === ZERO_OID) {
      if (current === undefined) {
        results.push({ ref: command.ref, ok: false, reason: 'remote ref does not exist' });
      } else {
        repo.refs.delete(command.ref);
        results.push({ ref: command.ref, ok: true, reason: '' });
      }
      continue;
    }
    if (!unpackOk) {
      results.push({ ref: command.ref, ok: false, reason: 'unpacker error' });
      continue;
    }
    const target = repo.objects.get(command.newOid);
    if (target === undefined) {
      results.push({ ref: command.ref, ok: false, reason: 'object not found' });
      continue;
    }
    if (command.oldOid === ZERO_OID) {
      if (current !== undefined) {
        results.push({ ref: command.ref, ok: false, reason: 'already exists' });
        continue;
      }
      repo.refs.set(command.ref, command.newOid);
      results.push({ ref: command.ref, ok: true, reason: '' });
      continue;
    }
    if (current === undefined) {
      results.push({ ref: command.ref, ok: false, reason: 'remote ref does not exist' });
      continue;
    }
    if (current !== command.oldOid) {
      results.push({ ref: command.ref, ok: false, reason: 'non-fast-forward' });
      continue;
    }
    const newCommit = peelToCommit(repo, command.newOid);
    if (command.newOid !== command.oldOid && !isAncestor(repo, peelToCommit(repo, command.oldOid), newCommit)) {
      results.push({ ref: command.ref, ok: false, reason: 'non-fast-forward' });
      continue;
    }
    repo.refs.set(command.ref, command.newOid);
    results.push({ ref: command.ref, ok: true, reason: '' });
  }
  const inner: Buffer[] = [pktLine(unpackOk ? 'unpack ok\n' : 'unpack error\n')];
  for (const result of results) {
    inner.push(pktLine(result.ok ? `ok ${result.ref}\n` : `ng ${result.ref} ${result.reason}\n`));
  }
  inner.push(PKT_FLUSH);
  const report = Buffer.concat(inner);
  return Buffer.concat([pktLine(Buffer.concat([Buffer.from([1]), report])), PKT_FLUSH]);
}

async function handleGit(forge: Forge, req: IncomingMessage, res: ServerResponse, url: URL, body: Buffer): Promise<boolean> {
  const match = /^\/([^/]+)\/([^/]+)\.git\/(.+)$/.exec(url.pathname);
  if (match === null) return false;
  const owner = decodeURIComponent(match[1]!);
  const repoName = decodeURIComponent(match[2]!);
  const tail = match[3]!;
  const method = req.method ?? 'GET';
  const repo = forge.getRepo(owner, repoName);
  if (repo === undefined || owner !== VIEWER_LOGIN) {
    sendBuffer(res, 404, Buffer.from('Not Found\n', 'utf8'), 'text/plain; charset=utf-8');
    return true;
  }
  if (tail === 'info/refs' && method === 'GET') {
    const service = url.searchParams.get('service');
    if (service !== 'git-upload-pack' && service !== 'git-receive-pack') {
      sendBuffer(res, 400, Buffer.from('Bad Request\n', 'utf8'), 'text/plain; charset=utf-8');
      return true;
    }
    const isV2 = service === 'git-upload-pack' && req.headers['git-protocol'] === 'version=2';
    const advertisement = isV2 ? v2Advertisement() : v0Advertisement(repo, service);
    sendBuffer(res, 200, advertisement, `application/x-${service}-advertisement`);
    return true;
  }
  if (tail === 'git-upload-pack' && method === 'POST') {
    try {
      const uploadCacheKey = `${repoRefsCacheKey(repo, 'upload-pack')}:${repo.objects.size}:${body.toString('latin1')}`;
      const cachedUpload = repo.advCache.get(uploadCacheKey);
      if (cachedUpload !== undefined) {
        sendBuffer(res, 200, cachedUpload, 'application/x-git-upload-pack-result');
        return true;
      }
      const packets = decodePktLines(body);
      const firstLine = packets.find((packet) => packet.kind === 'data')?.payload.toString('utf8') ?? '';
      if (req.headers['git-protocol'] === 'version=2' || firstLine.startsWith('command=')) {
        if (firstLine.startsWith('command=ls-refs')) {
          const reply = handleLsRefs(repo, packets);
          repo.advCache.set(uploadCacheKey, reply);
          sendBuffer(res, 200, reply, 'application/x-git-upload-pack-result');
          return true;
        }
        if (firstLine.startsWith('command=fetch')) {
          const reply = handleFetchV2(repo, packets);
          repo.advCache.set(uploadCacheKey, reply);
          sendBuffer(res, 200, reply, 'application/x-git-upload-pack-result');
          return true;
        }
        sendBuffer(res, 400, Buffer.from('Bad Request\n', 'utf8'), 'text/plain; charset=utf-8');
        return true;
      }
      const reply = handleFetchV0(repo, packets);
      repo.advCache.set(uploadCacheKey, reply);
      sendBuffer(res, 200, reply, 'application/x-git-upload-pack-result');
      return true;
    } catch {
      sendBuffer(res, 400, Buffer.from('Bad Request\n', 'utf8'), 'text/plain; charset=utf-8');
      return true;
    }
  }
  if (tail === 'git-receive-pack' && method === 'POST') {
    try {
      sendBuffer(res, 200, handleReceivePack(repo, body), 'application/x-git-receive-pack-result');
      return true;
    } catch {
      sendBuffer(res, 400, Buffer.from('Bad Request\n', 'utf8'), 'text/plain; charset=utf-8');
      return true;
    }
  }
  return false;
}

// ---------------------------------------------------------------- app

export function createApp(): Server {
  const forge = new Forge();
  const server = createServer({ keepAlive: true, noDelay: true }, async (req, res) => {
    try {
      const url = new URL(req.url ?? '/', `http://${req.headers.host ?? 'localhost'}`);
      const body = await readBody(req);
      if (url.pathname === '/healthz' && (req.method ?? 'GET') === 'GET') {
        sendJson(res, 200, { status: 'ok' });
        return;
      }
      if (url.pathname === '/' && (req.method ?? 'GET') === 'GET') {
        sendJson(res, 200, { status: 'ok' });
        return;
      }
      if (url.pathname === '/api/graphql' && req.method === 'POST') {
        await handleGraphQl(forge, req, res, body);
        return;
      }
      if (url.pathname === '/mcp' && req.method === 'POST') {
        await handleMcp(forge, req, res, body);
        return;
      }
      if (url.pathname === '/api/v3' || url.pathname.startsWith('/api/v3/')) {
        if (!requireAuth(req, res)) return;
        const handled = await handleRest(forge, req, res, url, body);
        if (!handled) jsonError(res, 404, 'Not Found');
        return;
      }
      if (/^\/[^/]+\/[^/]+\.git\//.test(url.pathname)) {
        const handled = await handleGit(forge, req, res, url, body);
        if (!handled) jsonError(res, 404, 'Not Found');
        return;
      }
      jsonError(res, 404, 'Not Found');
    } catch (error) {
      if (!res.headersSent) {
        jsonError(res, 500, error instanceof Error ? error.message : 'Internal Server Error');
      } else {
        try {
          res.end();
        } catch {
          // The response is already in flight; nothing more to do.
        }
      }
    }
  });
  return server;
}
