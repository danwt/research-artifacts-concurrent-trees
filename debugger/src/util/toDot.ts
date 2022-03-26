import _ from "lodash";

enum EdgeType {
  LEFT = 1,
  RITE = 2,
  PARENT = 3,
}

type Edge = [string, string, string, EdgeType]; // [from, to, color, isLeft]

const LEFT_COLOR = "crimson";
const RITE_COLOR = "dodgerblue";
const PARENT_COLOR = "darkseagreen2";

const DEFAULT_NODE_COLOR = "white";
const LEAF_COLOR = "aquamarine";
const CHUNK_ROOT_COLOR = "gold1";
const CHUNK_ROOT_AND_LEAF_COLOR = "darkturquoise";

class Graph {
  keys: Record<string, string> = {};
  vals: Record<string, string> = {};
  heights: Record<string, number> = {};
  isChunkRoot: Record<string, boolean> = {};
  isLeaf: Record<string, boolean> = {};

  hasLeft: string[] = [];
  hasRite: string[] = [];

  edges: Edge[] = [];

  constructor() {
    // Label root
    this.keys["0"] = "RootHolder";
  }

  addLeftEdge(from: string, to: string) {
    this.hasLeft.push(from);
    this.edges.push([from, to, LEFT_COLOR, EdgeType.LEFT]);
  }

  addRiteEdge(from: string, to: string) {
    this.hasRite.push(from);
    this.edges.push([from, to, RITE_COLOR, EdgeType.RITE]);
  }

  addParentEdge(from: string, to: string) {
    this.edges.push([from, to, PARENT_COLOR, EdgeType.PARENT]);
  }

  addKey(address: string, k: string) {
    this.keys[address] = k;
  }

  addVal(address: string, v: string) {
    this.vals[address] = v;
  }

  addHeight(address: string, v: number) {
    this.heights[address] = v;
  }

  markChunkRoot(address: string) {
    this.isChunkRoot[address] = true;
  }

  markLeaf(address: string) {
    this.isLeaf[address] = true;
  }

  nodeLabel(address: string): string {
    var k = address in this.keys ? this.keys[address] : "None";
    var v = address in this.vals ? this.vals[address] : "None";
    var h = address in this.heights ? this.heights[address] : "?";
    return `"k:${k} v:${v} a:${address} h:${h}"`;
  }

  nodeStyle(address: string): string {
    var col = DEFAULT_NODE_COLOR;
    if (this.isChunkRoot[address] === true && this.isLeaf[address] === true) {
      col = CHUNK_ROOT_AND_LEAF_COLOR;
    } else if (this.isChunkRoot[address] === true) {
      col = CHUNK_ROOT_COLOR;
    } else if (this.isLeaf[address] === true) {
      col = LEAF_COLOR;
    }
    return `${this.nodeLabel(address)} [style=filled, fillcolor=${col}];`;
  }

  nodeStyleString(): string {
    var ret = "";
    for (const address of Object.keys(this.keys)) {
      ret += `${this.nodeStyle(address)}\n`;
    }
    return ret;
  }

  regularEdgeString(edge: Edge) {
    const [from, to, col, isLeft] = edge;
    return `${this.nodeLabel(from)} -> ${this.nodeLabel(
      to
    )} [style=bold, color=${col}];\n`;
  }

  edgeStrings(): string[] {
    var ret: string[] = [];

    _.filter(this.edges, (it) => it[3] === EdgeType.LEFT).forEach((it) => {
      ret.push(this.regularEdgeString(it));
    });

    ret = ret.concat(
      this.invisibleEdges(_.difference(this.hasRite, this.hasLeft))
    );

    _.filter(this.edges, (it) => it[3] === EdgeType.RITE).forEach((it) => {
      ret.push(this.regularEdgeString(it));
    });

    ret = ret.concat(
      this.invisibleEdges(_.difference(this.hasLeft, this.hasRite))
    );

    _.filter(this.edges, (it) => it[3] === EdgeType.PARENT).forEach((it) => {
      ret.push(this.regularEdgeString(it));
    });

    return ret;
  }

  invisibleEdgeString(addr: string): string {
    const label = `"Invis${addr}"`;
    return `
${label} [ label = ${label}, style = invis ]; ${this.nodeLabel(
      addr
    )} -> ${label} [ style = invis ];\n`.trimStart();
  }

  invisibleEdges(keys: string[]) {
    return keys.map((it) => this.invisibleEdgeString(it));
  }
}

export function wrapContent(content: string): string {
  function header() {
    return `
digraph {
ordering=out;
`;
  }

  function footer() {
    return `}`;
  }

  return header() + content + footer();
}

export default function toDot(data: any): string {
  // console.log("data", data);

  const left = data.left || {};
  const rite = data.rite || {};

  const key = data.key || {};
  const val = data.val || {};

  const height = data.height || {};

  const parent = data.parent || {};

  const nodeChunk = data.chunk_of_node || {};
  const isLeaf = data.is_leaf || {};

  const graph = new Graph();

  let content = "";

  for (const [k, v] of Object.entries(left)) {
    graph.addLeftEdge(k, (v as number).toString());
  }

  for (const [k, v] of Object.entries(rite)) {
    graph.addRiteEdge(k, (v as number).toString());
  }

  for (const [k, v] of Object.entries(parent)) {
    graph.addParentEdge(k, (v as number).toString());
  }

  for (const [k, v] of Object.entries(key)) {
    graph.addKey(k, (v as number).toString());
  }

  for (const [k, v] of Object.entries(val)) {
    graph.addVal(k, (v as number).toString());
  }

  for (const [k, v] of Object.entries(height)) {
    graph.addHeight(k, v as number);
  }

  for (const [k, v] of Object.entries(nodeChunk)) {
    if (v != null) {
      graph.markChunkRoot(k);
    }
  }

  for (const [k, v] of Object.entries(isLeaf)) {
    if (v != null) {
      graph.markLeaf(k);
    }
  }

  content += graph.nodeStyleString();

  graph.edgeStrings().forEach((it) => {
    content += it;
  });

  let ret = wrapContent(content);
  return ret;
}
