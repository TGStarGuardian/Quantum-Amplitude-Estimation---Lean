#!/usr/bin/env python3
"""Build and serve an interactive dependency graph for the QAE Lean project.

The extractor is intentionally source based: it finds project-local declarations
and then records source references from each declaration body/proof to earlier or
later project declarations. It avoids the nested duplicate repository copy under
Quantum-Amplitude-Estimation---Lean.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import http.server
import json
import math
import re
import socketserver
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


PROJECT_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_HTML = PROJECT_ROOT / "docs" / "qae_dependency_graph.html"
DEFAULT_JSON = PROJECT_ROOT / "docs" / "qae_dependency_graph.json"

DECL_RE = re.compile(
    r"^\s*(?:(private|protected)\s+)?(?:@\[[^\]]*\]\s*)*"
    r"(def|theorem|lemma|structure|class|inductive|abbrev|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.!?]*|«[^»]+»)"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*(?:\s+[A-Za-z_][A-Za-z0-9_'.]*)*)\b")
END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\b")
IDENT_EDGE_CHARS = r"A-Za-z0-9_'."
THEOREM_KINDS = {"theorem", "lemma"}
MARKED_SIMPLE_NAMES = {"papertheorem11", "papertheorem12", "paperlemma7"}


@dataclass
class Decl:
    id: str
    name: str
    simple: str
    namespace: tuple[str, ...]
    kind: str
    private: bool
    file: str
    line: int
    body: str

    @property
    def is_theorem_like(self) -> bool:
        return self.kind in THEOREM_KINDS

    @property
    def is_definition_like(self) -> bool:
        return self.kind not in THEOREM_KINDS


def strip_lean_comments(text: str) -> str:
    """Remove Lean comments while preserving line positions."""
    out: list[str] = []
    i = 0
    depth = 0
    while i < len(text):
        two = text[i : i + 2]
        if depth == 0 and two == "--":
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if two == "/-":
            depth += 1
            out.extend("  ")
            i += 2
            continue
        if depth > 0:
            if two == "-/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def project_lean_files(root: Path) -> list[Path]:
    files: list[Path] = []
    top = root / "QAELean.lean"
    if top.exists():
        files.append(top)
    src = root / "QAELean"
    if src.exists():
        files.extend(sorted(src.rglob("*.lean")))
    return files


def parse_file(path: Path, root: Path) -> list[Decl]:
    text = path.read_text(encoding="utf-8")
    stripped = strip_lean_comments(text)
    lines = stripped.splitlines(keepends=True)
    starts: list[tuple[int, int, str, str, bool, tuple[str, ...]]] = []
    namespace_stack: list[str] = []
    offset = 0

    for line_no, line in enumerate(lines, start=1):
        match = DECL_RE.match(line)
        if match:
            private = bool(match.group(1) == "private")
            kind = match.group(2)
            raw_name = match.group(3).strip("«»")
            starts.append((offset, line_no, kind, raw_name, private, tuple(namespace_stack)))
            offset += len(line)
            continue

        ns = NAMESPACE_RE.match(line)
        if ns:
            namespace_stack.extend(part.strip() for part in ns.group(1).split())
        else:
            end = END_RE.match(line)
            if end and namespace_stack:
                wanted = end.group(1)
                if wanted and wanted in namespace_stack:
                    while namespace_stack:
                        popped = namespace_stack.pop()
                        if popped == wanted:
                            break
                else:
                    namespace_stack.pop()
        offset += len(line)

    decls: list[Decl] = []
    rel_file = path.relative_to(root).as_posix()
    for idx, (start, line_no, kind, raw_name, private, namespace) in enumerate(starts):
        end = starts[idx + 1][0] if idx + 1 < len(starts) else len(stripped)
        name_parts = tuple(part for part in raw_name.split(".") if part)
        full_parts = namespace + name_parts
        full_name = ".".join(full_parts)
        simple = name_parts[-1] if name_parts else raw_name
        decls.append(
            Decl(
                id=full_name,
                name=full_name,
                simple=simple,
                namespace=full_parts[:-1],
                kind=kind,
                private=private,
                file=rel_file,
                line=line_no,
                body=stripped[start:end],
            )
        )
    return decls


def is_prefix(prefix: tuple[str, ...], value: tuple[str, ...]) -> bool:
    return len(prefix) <= len(value) and value[: len(prefix)] == prefix


def allowed_edge(src: Decl, dst: Decl) -> bool:
    if src.id == dst.id:
        return False
    if dst.is_theorem_like:
        return src.is_theorem_like or src.is_definition_like
    if dst.is_definition_like:
        return src.is_definition_like
    return False


def token_pattern(name: str) -> re.Pattern[str]:
    return re.compile(
        rf"(?<![{IDENT_EDGE_CHARS}]){re.escape(name)}(?![{IDENT_EDGE_CHARS}])"
    )


def qualified_aliases(decl: Decl) -> list[str]:
    parts = decl.name.split(".")
    aliases: list[str] = []
    for i in range(0, max(0, len(parts) - 1)):
        alias = ".".join(parts[i:])
        if "." in alias:
            aliases.append(alias)
    if len(parts) > 2:
        aliases.append(".".join(parts[1:]))
    return sorted(set(aliases), key=lambda item: (-len(item), item))


def mentions(src: Decl, dst: Decl) -> bool:
    body = dst.body
    for alias in qualified_aliases(src):
        if token_pattern(alias).search(body):
            return True
    if is_prefix(src.namespace, dst.namespace):
        if token_pattern(src.simple).search(body):
            return True
    return False


def build_graph(root: Path = PROJECT_ROOT) -> dict:
    decls: list[Decl] = []
    for path in project_lean_files(root):
        decls.extend(parse_file(path, root))

    by_id = {decl.id: decl for decl in decls}
    nodes = []
    for decl in decls:
        marked = decl.simple.lower() in MARKED_SIMPLE_NAMES
        nodes.append(
            {
                "id": decl.id,
                "label": decl.simple,
                "fullName": decl.name,
                "namespace": ".".join(decl.namespace),
                "kind": decl.kind,
                "group": "theorem" if decl.is_theorem_like else "definition",
                "private": decl.private,
                "marked": marked,
                "file": decl.file,
                "line": decl.line,
            }
        )

    edges = []
    seen: set[tuple[str, str]] = set()
    for dst in decls:
        for src in decls:
            if not allowed_edge(src, dst):
                continue
            if mentions(src, dst):
                key = (src.id, dst.id)
                if key not in seen:
                    seen.add(key)
                    edges.append({"source": src.id, "target": dst.id})

    incoming = {node["id"]: 0 for node in nodes}
    outgoing = {node["id"]: 0 for node in nodes}
    for edge in edges:
        outgoing[edge["source"]] += 1
        incoming[edge["target"]] += 1
    for node in nodes:
        node["incoming"] = incoming[node["id"]]
        node["outgoing"] = outgoing[node["id"]]
        node["degree"] = node["incoming"] + node["outgoing"]

    nodes.sort(key=lambda node: (node["namespace"], node["label"], node["id"]))
    edges.sort(key=lambda edge: (edge["source"], edge["target"]))

    return {
        "generatedAt": _dt.datetime.now(_dt.timezone.utc).isoformat(),
        "projectRoot": str(root),
        "sourceFiles": [path.relative_to(root).as_posix() for path in project_lean_files(root)],
        "marked": ["PaperTheorem11", "PaperTheorem12", "paperLemma7"],
        "nodes": nodes,
        "edges": edges,
        "stats": {"nodes": len(nodes), "edges": len(edges), "files": len(project_lean_files(root))},
    }


HTML_TEMPLATE = r"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>QAE Lean Dependency Graph</title>
  <style>
    :root {
      --bg: #f7f8fb;
      --panel: #ffffff;
      --ink: #1f2937;
      --muted: #64748b;
      --line: #cbd5e1;
      --unmarked: #2563eb;
      --marked: #dc2626;
      --private: #8a5a9f;
    }
    * { box-sizing: border-box; }
    body {
      margin: 0;
      min-height: 100vh;
      background: var(--bg);
      color: var(--ink);
      font-family: system-ui, -apple-system, Segoe UI, sans-serif;
      overflow: hidden;
    }
    header {
      display: flex;
      align-items: center;
      gap: 12px;
      height: 58px;
      padding: 10px 14px;
      border-bottom: 1px solid #d8dee9;
      background: var(--panel);
      white-space: nowrap;
    }
    h1 {
      margin: 0;
      font-size: 17px;
      font-weight: 700;
    }
    .meta {
      color: var(--muted);
      font-size: 13px;
      min-width: 140px;
    }
    button, select, input {
      height: 34px;
      border: 1px solid #cbd5e1;
      background: #fff;
      color: var(--ink);
      border-radius: 6px;
      padding: 0 10px;
      font: inherit;
      font-size: 13px;
    }
    .file-list {
      display: grid;
      gap: 4px;
      max-height: 190px;
      overflow: auto;
      border: 1px solid #cbd5e1;
      border-radius: 6px;
      padding: 6px;
      background: #fff;
    }
    .file-list label {
      display: grid;
      grid-template-columns: 18px 1fr;
      align-items: start;
      gap: 7px;
      min-height: 24px;
      font-size: 12px;
      line-height: 1.25;
      cursor: pointer;
      word-break: break-word;
    }
    .file-list input {
      width: 14px;
      min-width: 14px;
      height: 14px;
      margin: 1px 0 0;
      padding: 0;
    }
    button {
      cursor: pointer;
      font-weight: 600;
    }
    button:hover { background: #f1f5f9; }
    input {
      min-width: 230px;
    }
    main {
      display: grid;
      grid-template-columns: 1fr 310px;
      height: calc(100vh - 58px);
    }
    #graph {
      width: 100%;
      height: 100%;
      cursor: grab;
      background:
        linear-gradient(90deg, rgba(148,163,184,0.16) 1px, transparent 1px),
        linear-gradient(rgba(148,163,184,0.16) 1px, transparent 1px);
      background-size: 32px 32px;
    }
    #graph:active { cursor: grabbing; }
    aside {
      border-left: 1px solid #d8dee9;
      background: var(--panel);
      padding: 14px;
      overflow: auto;
      font-size: 13px;
    }
    .file-panel {
      display: grid;
      gap: 8px;
      margin-bottom: 14px;
    }
    .file-actions {
      display: flex;
      gap: 8px;
    }
    .file-actions button {
      flex: 1;
    }
    .legend {
      display: grid;
      gap: 8px;
      margin-bottom: 14px;
    }
    .legend span {
      display: inline-flex;
      align-items: center;
      gap: 8px;
    }
    .dot {
      width: 12px;
      height: 12px;
      border-radius: 50%;
      display: inline-block;
    }
    .dot.unmarked { background: var(--unmarked); }
    .dot.marked {
      background: var(--marked);
      border: 2px solid #7f1d1d;
    }
    .shape {
      width: 14px;
      height: 14px;
      border: 2px solid #334155;
      display: inline-block;
      background: #fff;
    }
    .shape.def { border-radius: 2px; }
    .shape.thm { border-radius: 50%; }
    .details {
      display: grid;
      gap: 8px;
      line-height: 1.35;
      word-break: break-word;
    }
    .details code {
      background: #f1f5f9;
      padding: 2px 4px;
      border-radius: 4px;
    }
    .status {
      margin-left: auto;
      overflow: hidden;
      text-overflow: ellipsis;
      color: var(--muted);
      font-size: 13px;
    }
    .edge {
      stroke: #93a4b8;
      stroke-opacity: 0.45;
      stroke-width: 1.2;
    }
    .edge.dim { stroke-opacity: 0.08; }
    .edge.hidden { display: none; }
    .node .shape-node {
      stroke: #ffffff;
      stroke-width: 1.6;
      fill: var(--unmarked);
    }
    .node.private .shape-node { stroke: var(--private); stroke-width: 2.6; }
    .node.marked .shape-node {
      fill: var(--marked);
      stroke: #7f1d1d;
      stroke-width: 3;
    }
    .node text {
      pointer-events: none;
      font-size: 11px;
      paint-order: stroke;
      stroke: #fff;
      stroke-width: 3px;
      stroke-linejoin: round;
      fill: #18202d;
    }
    .node.dim { opacity: 0.16; }
    .node.hidden { display: none; }
    .node.selected .shape-node {
      stroke: #111827;
      stroke-width: 3.2;
    }
  </style>
</head>
<body>
  <header>
    <h1>QAE Lean Dependency Graph</h1>
    <div class="meta" id="stats"></div>
    <input id="search" type="search" placeholder="Search declarations">
    <select id="kindFilter" aria-label="Kind filter">
      <option value="all">All nodes</option>
      <option value="marked">Marked only</option>
      <option value="theorem">Theorems and lemmas</option>
      <option value="definition">Definitions and structures</option>
    </select>
    <button id="layoutBtn" type="button">Re-layout</button>
    <button id="refreshBtn" type="button">Refresh from Lean files</button>
    <div class="status" id="status"></div>
  </header>
  <main>
    <svg id="graph" role="img" aria-label="Lean dependency graph"></svg>
    <aside>
      <div class="file-panel">
        <strong>Included Files</strong>
        <div id="fileFilter" class="file-list" role="group" aria-label="Included Lean files"></div>
        <div class="file-actions">
          <button id="allFilesBtn" type="button">All Files</button>
          <button id="noFilesBtn" type="button">No Files</button>
          <button id="markedFilesBtn" type="button">Marked Files</button>
        </div>
      </div>
      <div class="legend">
        <span><i class="dot marked"></i>Marked construct</span>
        <span><i class="dot unmarked"></i>Unmarked construct</span>
        <span><i class="shape thm"></i>Theorem-like: theorem or lemma</span>
        <span><i class="shape def"></i>Definition-like: def, structure, class, instance, inductive, or abbrev</span>
        <span>Arrows point from dependency to dependent declaration</span>
      </div>
      <div class="details" id="details">
        <strong>Selection</strong>
        <span>Click a node to inspect it. Drag nodes to move them. Use the mouse wheel to zoom and drag the background to pan.</span>
      </div>
    </aside>
  </main>
  <script>
    let graphData = __GRAPH_DATA__;
    const svg = document.getElementById("graph");
    const details = document.getElementById("details");
    const stats = document.getElementById("stats");
    const statusEl = document.getElementById("status");
    const searchEl = document.getElementById("search");
    const kindFilter = document.getElementById("kindFilter");
    const fileFilter = document.getElementById("fileFilter");
    const NS = "http://www.w3.org/2000/svg";

    let width = 1000;
    let height = 700;
    let transform = { x: 0, y: 0, k: 1 };
    let nodes = [];
    let edges = [];
    let nodeById = new Map();
    let selected = null;
    let draggingNode = null;
    let panning = null;
    let running = true;
    let gRoot, gEdges, gNodes;

    function setStatus(text) {
      statusEl.textContent = text;
    }

    function escapeHtml(value) {
      return String(value).replace(/[&<>"']/g, ch => ({
        "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#039;"
      }[ch]));
    }

    function sizeNode(node) {
      const base = node.marked ? 12 : 7;
      return Math.min(17, base + Math.sqrt(Math.max(0, node.degree || 0)) * 0.55);
    }

    function seedPositions() {
      const nsGroups = new Map();
      nodes.forEach(node => {
        const key = node.namespace || "(root)";
        if (!nsGroups.has(key)) nsGroups.set(key, []);
        nsGroups.get(key).push(node);
      });
      const groups = Array.from(nsGroups.values());
      const centerX = width / 2;
      const centerY = height / 2;
      const radius = Math.min(width, height) * 0.31;
      groups.forEach((group, groupIdx) => {
        const groupAngle = (2 * Math.PI * groupIdx) / Math.max(1, groups.length);
        const gx = centerX + Math.cos(groupAngle) * radius;
        const gy = centerY + Math.sin(groupAngle) * radius;
        const localRadius = 24 + Math.sqrt(group.length) * 15;
        group.forEach((node, idx) => {
          const angle = (2 * Math.PI * idx) / Math.max(1, group.length);
          node.x = gx + Math.cos(angle) * localRadius;
          node.y = gy + Math.sin(angle) * localRadius;
          node.vx = 0;
          node.vy = 0;
          node.fixed = false;
        });
      });
    }

    function populateFileFilter(data) {
      const selected = new Set(Array.from(fileFilter.querySelectorAll("input:checked")).map(input => input.value));
      const hadExistingInputs = fileFilter.querySelectorAll("input").length > 0;
      fileFilter.innerHTML = "";
      data.sourceFiles.forEach(file => {
        const label = document.createElement("label");
        const input = document.createElement("input");
        const text = document.createElement("span");
        input.type = "checkbox";
        input.value = file;
        input.checked = !hadExistingInputs || selected.has(file);
        input.addEventListener("change", applyFilter);
        text.textContent = file;
        label.appendChild(input);
        label.appendChild(text);
        fileFilter.appendChild(label);
      });
    }

    function selectedFiles() {
      return new Set(Array.from(fileFilter.querySelectorAll("input:checked")).map(input => input.value));
    }

    function setAllFiles(selected) {
      Array.from(fileFilter.querySelectorAll("input")).forEach(input => { input.checked = selected; });
      applyFilter();
    }

    function setMarkedFiles() {
      const files = new Set(nodes.filter(node => node.marked).map(node => node.file));
      Array.from(fileFilter.querySelectorAll("input")).forEach(input => { input.checked = files.has(input.value); });
      applyFilter();
    }

    function loadData(data) {
      graphData = data;
      nodes = data.nodes.map(node => ({ ...node }));
      edges = data.edges.map(edge => ({ ...edge }));
      nodeById = new Map(nodes.map(node => [node.id, node]));
      edges.forEach(edge => {
        edge.sourceNode = nodeById.get(edge.source);
        edge.targetNode = nodeById.get(edge.target);
      });
      populateFileFilter(data);
      seedPositions();
      setStatus(`Generated ${new Date(data.generatedAt).toLocaleString()}`);
      render();
      restart();
    }

    function render() {
      svg.innerHTML = "";
      const defs = document.createElementNS(NS, "defs");
      const marker = document.createElementNS(NS, "marker");
      marker.setAttribute("id", "arrow");
      marker.setAttribute("markerWidth", "10");
      marker.setAttribute("markerHeight", "10");
      marker.setAttribute("refX", "8");
      marker.setAttribute("refY", "3");
      marker.setAttribute("orient", "auto");
      const arrowPath = document.createElementNS(NS, "path");
      arrowPath.setAttribute("d", "M0,0 L0,6 L9,3 z");
      arrowPath.setAttribute("fill", "#93a4b8");
      marker.appendChild(arrowPath);
      defs.appendChild(marker);
      svg.appendChild(defs);

      gRoot = document.createElementNS(NS, "g");
      gEdges = document.createElementNS(NS, "g");
      gNodes = document.createElementNS(NS, "g");
      gRoot.appendChild(gEdges);
      gRoot.appendChild(gNodes);
      svg.appendChild(gRoot);

      edges.forEach(edge => {
        const line = document.createElementNS(NS, "line");
        line.setAttribute("class", "edge");
        line.setAttribute("marker-end", "url(#arrow)");
        edge.el = line;
        gEdges.appendChild(line);
      });

      nodes.forEach(node => {
        const group = document.createElementNS(NS, "g");
        group.setAttribute("class", `node ${node.group}${node.marked ? " marked" : ""}${node.private ? " private" : ""}`);
        group.dataset.id = node.id;
        let shape;
        if (node.group === "theorem") {
          shape = document.createElementNS(NS, "circle");
          shape.setAttribute("r", String(sizeNode(node)));
        } else {
          shape = document.createElementNS(NS, "rect");
          const side = sizeNode(node) * 1.65;
          shape.setAttribute("x", String(-side / 2));
          shape.setAttribute("y", String(-side / 2));
          shape.setAttribute("width", String(side));
          shape.setAttribute("height", String(side));
          shape.setAttribute("rx", "2");
        }
        shape.setAttribute("class", "shape-node");
        const text = document.createElementNS(NS, "text");
        text.setAttribute("x", String(sizeNode(node) + 4));
        text.setAttribute("y", "4");
        text.textContent = node.marked ? `* ${node.label}` : node.label;
        group.appendChild(shape);
        group.appendChild(text);
        group.addEventListener("pointerdown", event => {
          event.stopPropagation();
          draggingNode = node;
          node.fixed = true;
          group.setPointerCapture(event.pointerId);
        });
        group.addEventListener("pointerup", event => {
          group.releasePointerCapture(event.pointerId);
          draggingNode = null;
        });
        group.addEventListener("click", event => {
          event.stopPropagation();
          selectNode(node);
        });
        node.el = group;
        gNodes.appendChild(group);
      });

      svg.addEventListener("pointerdown", event => {
        panning = { x: event.clientX, y: event.clientY, tx: transform.x, ty: transform.y };
      });
      svg.addEventListener("pointerup", () => { panning = null; });
      svg.addEventListener("pointerleave", () => { panning = null; draggingNode = null; });
      svg.addEventListener("pointermove", onPointerMove);
      svg.addEventListener("wheel", onWheel, { passive: false });
      applyTransform();
      applyFilter();
    }

    function graphPoint(event) {
      const rect = svg.getBoundingClientRect();
      return {
        x: (event.clientX - rect.left - transform.x) / transform.k,
        y: (event.clientY - rect.top - transform.y) / transform.k
      };
    }

    function onPointerMove(event) {
      if (draggingNode) {
        const point = graphPoint(event);
        draggingNode.x = point.x;
        draggingNode.y = point.y;
        draggingNode.vx = 0;
        draggingNode.vy = 0;
        tick();
      } else if (panning) {
        transform.x = panning.tx + event.clientX - panning.x;
        transform.y = panning.ty + event.clientY - panning.y;
        applyTransform();
      }
    }

    function onWheel(event) {
      event.preventDefault();
      const scale = event.deltaY < 0 ? 1.08 : 0.92;
      const rect = svg.getBoundingClientRect();
      const mx = event.clientX - rect.left;
      const my = event.clientY - rect.top;
      const before = { x: (mx - transform.x) / transform.k, y: (my - transform.y) / transform.k };
      transform.k = Math.max(0.18, Math.min(4, transform.k * scale));
      transform.x = mx - before.x * transform.k;
      transform.y = my - before.y * transform.k;
      applyTransform();
    }

    function applyTransform() {
      if (gRoot) {
        gRoot.setAttribute("transform", `translate(${transform.x},${transform.y}) scale(${transform.k})`);
      }
    }

    function selectNode(node) {
      selected = node;
      nodes.forEach(n => n.el.classList.toggle("selected", n === node));
      const outgoing = edges.filter(edge => edge.source === node.id).length;
      const incoming = edges.filter(edge => edge.target === node.id).length;
      details.innerHTML = `
        <strong>${escapeHtml(node.label)}</strong>
        <span><code>${escapeHtml(node.fullName)}</code></span>
        <span>Kind: ${escapeHtml(node.kind)}${node.private ? " private" : ""}${node.marked ? " marked" : ""}</span>
        <span>Location: <code>${escapeHtml(node.file)}:${node.line}</code></span>
        <span>Dependencies out: ${outgoing}</span>
        <span>Used by: ${incoming}</span>
      `;
      applyFilter();
    }

    function applyFilter() {
      const query = searchEl.value.trim().toLowerCase();
      const mode = kindFilter.value;
      const files = selectedFiles();
      const included = new Set();
      const visible = new Set();
      nodes.forEach(node => {
        const fileMatch = files.has(node.file);
        if (fileMatch) included.add(node.id);
        const textMatch = !query || node.fullName.toLowerCase().includes(query) || node.label.toLowerCase().includes(query);
        const kindMatch =
          mode === "all" ||
          (mode === "marked" && node.marked) ||
          mode === node.group;
        if (fileMatch && textMatch && kindMatch) visible.add(node.id);
      });
      if (selected && !included.has(selected.id)) {
        selected = null;
        nodes.forEach(n => n.el.classList.remove("selected"));
      }
      if (selected) {
        edges.forEach(edge => {
          if ((edge.source === selected.id || edge.target === selected.id) &&
              included.has(edge.source) && included.has(edge.target)) {
            visible.add(edge.source);
            visible.add(edge.target);
          }
        });
      }
      nodes.forEach(node => {
        const inFile = included.has(node.id);
        node.el.classList.toggle("hidden", !inFile);
        node.el.classList.toggle("dim", inFile && !visible.has(node.id));
      });
      let visibleEdges = 0;
      edges.forEach(edge => {
        const inFile = included.has(edge.source) && included.has(edge.target);
        const related = selected && (edge.source === selected.id || edge.target === selected.id);
        const edgeVisible = inFile && (selected ? related : (visible.has(edge.source) && visible.has(edge.target)));
        edge.el.classList.toggle("hidden", !inFile);
        edge.el.classList.toggle("dim", inFile && !edgeVisible);
        if (edgeVisible) visibleEdges += 1;
      });
      stats.textContent = `${visible.size} / ${nodes.length} nodes, ${visibleEdges} / ${edges.length} edges`;
    }

    function restart() {
      running = true;
      let frames = 0;
      function frame() {
        if (!running) return;
        simulate();
        tick();
        frames += 1;
        if (frames < 420) requestAnimationFrame(frame);
      }
      requestAnimationFrame(frame);
    }

    function simulate() {
      const cx = width / 2;
      const cy = height / 2;
      nodes.forEach(node => {
        if (!node.fixed) {
          node.vx += (cx - node.x) * 0.0008;
          node.vy += (cy - node.y) * 0.0008;
        }
      });
      for (let i = 0; i < nodes.length; i++) {
        for (let j = i + 1; j < nodes.length; j++) {
          const a = nodes[i], b = nodes[j];
          let dx = b.x - a.x;
          let dy = b.y - a.y;
          let dist2 = dx * dx + dy * dy + 0.01;
          const minDist = 24 + sizeNode(a) + sizeNode(b);
          if (dist2 < minDist * minDist * 10) {
            const force = Math.min(2.2, 180 / dist2);
            const dist = Math.sqrt(dist2);
            dx /= dist;
            dy /= dist;
            if (!a.fixed) { a.vx -= dx * force; a.vy -= dy * force; }
            if (!b.fixed) { b.vx += dx * force; b.vy += dy * force; }
          }
        }
      }
      edges.forEach(edge => {
        const a = edge.sourceNode, b = edge.targetNode;
        if (!a || !b) return;
        let dx = b.x - a.x;
        let dy = b.y - a.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        const desired = 70 + Math.min(80, (a.degree + b.degree) * 0.7);
        const force = (dist - desired) * 0.008;
        dx /= dist;
        dy /= dist;
        if (!a.fixed) { a.vx += dx * force; a.vy += dy * force; }
        if (!b.fixed) { b.vx -= dx * force; b.vy -= dy * force; }
      });
      nodes.forEach(node => {
        if (!node.fixed) {
          node.vx *= 0.86;
          node.vy *= 0.86;
          node.x += node.vx;
          node.y += node.vy;
        }
      });
    }

    function tick() {
      edges.forEach(edge => {
        const a = edge.sourceNode, b = edge.targetNode;
        if (!a || !b) return;
        const r = sizeNode(b) + 5;
        const dx = b.x - a.x;
        const dy = b.y - a.y;
        const dist = Math.sqrt(dx * dx + dy * dy) || 1;
        edge.el.setAttribute("x1", a.x);
        edge.el.setAttribute("y1", a.y);
        edge.el.setAttribute("x2", b.x - dx / dist * r);
        edge.el.setAttribute("y2", b.y - dy / dist * r);
      });
      nodes.forEach(node => {
        node.el.setAttribute("transform", `translate(${node.x},${node.y})`);
      });
    }

    function resize() {
      const rect = svg.getBoundingClientRect();
      width = Math.max(400, rect.width);
      height = Math.max(300, rect.height);
      svg.setAttribute("viewBox", `0 0 ${width} ${height}`);
    }

    async function refreshFromServer() {
      if (window.location.protocol === "file:") {
        setStatus("Start with: python3 scripts/qae_dependency_graph.py --serve");
        return;
      }
      setStatus("Refreshing from Lean files...");
      const response = await fetch("/refresh", { method: "POST" });
      if (!response.ok) {
        setStatus(`Refresh failed: HTTP ${response.status}`);
        return;
      }
      const data = await response.json();
      loadData(data);
      setStatus(`Refreshed ${new Date(data.generatedAt).toLocaleString()}`);
    }

    document.getElementById("layoutBtn").addEventListener("click", () => {
      nodes.forEach(node => { node.fixed = false; });
      seedPositions();
      restart();
    });
    document.getElementById("refreshBtn").addEventListener("click", () => {
      refreshFromServer().catch(error => setStatus(`Refresh failed: ${error.message}`));
    });
    searchEl.addEventListener("input", applyFilter);
    kindFilter.addEventListener("change", applyFilter);
    document.getElementById("allFilesBtn").addEventListener("click", () => setAllFiles(true));
    document.getElementById("noFilesBtn").addEventListener("click", () => setAllFiles(false));
    document.getElementById("markedFilesBtn").addEventListener("click", setMarkedFiles);
    window.addEventListener("resize", () => { resize(); tick(); });

    resize();
    loadData(graphData);
  </script>
</body>
</html>
"""


def write_outputs(data: dict, html_path: Path = DEFAULT_HTML, json_path: Path = DEFAULT_JSON) -> None:
    html_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_text = json.dumps(data, indent=2, sort_keys=True)
    json_path.write_text(json_text + "\n", encoding="utf-8")
    html = HTML_TEMPLATE.replace("__GRAPH_DATA__", json.dumps(data, separators=(",", ":")))
    html_path.write_text(html, encoding="utf-8")


class GraphHandler(http.server.SimpleHTTPRequestHandler):
    def __init__(self, *args, root: Path, **kwargs):
        self.root = root
        super().__init__(*args, directory=str(root), **kwargs)

    def do_GET(self) -> None:  # noqa: N802
        if self.path in {"/", "/qae_dependency_graph.html"}:
            self.path = "/docs/qae_dependency_graph.html"
        return super().do_GET()

    def do_POST(self) -> None:  # noqa: N802
        if self.path != "/refresh":
            self.send_error(404, "unknown endpoint")
            return
        data = build_graph(self.root)
        write_outputs(data)
        body = json.dumps(data, separators=(",", ":")).encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)


def serve(root: Path, port: int) -> None:
    handler = lambda *args, **kwargs: GraphHandler(*args, root=root, **kwargs)
    with socketserver.TCPServer(("127.0.0.1", port), handler) as httpd:
        print(f"Serving QAE dependency graph at http://127.0.0.1:{port}/")
        httpd.serve_forever()


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=PROJECT_ROOT, help="project root")
    parser.add_argument("--html", type=Path, default=DEFAULT_HTML, help="HTML output path")
    parser.add_argument("--json", type=Path, default=DEFAULT_JSON, help="JSON output path")
    parser.add_argument("--serve", action="store_true", help="serve the graph and enable the refresh button")
    parser.add_argument("--port", type=int, default=8765, help="HTTP port for --serve")
    args = parser.parse_args(list(argv) if argv is not None else None)

    data = build_graph(args.root.resolve())
    write_outputs(data, args.html, args.json)
    print(
        f"wrote {args.html} with {data['stats']['nodes']} nodes and "
        f"{data['stats']['edges']} edges"
    )
    if args.serve:
        serve(args.root.resolve(), args.port)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
