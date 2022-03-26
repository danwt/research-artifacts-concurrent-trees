import json
from collections import Counter

filename = "seqcavlrecursivemapbasedcppcopy"

LEFT_COLOR = "crimson"
RITE_COLOR = "dodgerblue"
PARENT_COLOR = "darkseagreen2"
DEFAULT_NODE_COLOR = "white"
LEAF_COLOR = "forestgreen"
CHUNK_ROOT_COLOR = "gold1"
CHUNK_ROOT_AND_LEAF_COLOR = "palegreen2"


def get_obj():
    with open(f"dump/{filename}.json", "r") as f:
        return json.loads(f.read())


def pprint(o):
    pass


def dotnodelabel(node):
    id_ = node["id"]
    k = node["key"]
    v = node["value"]
    h = node["heightField"]
    label = f'"id: {id_} k: {k} v: {v} h: {h}"'
    return label


def dotnode(node):
    col = DEFAULT_NODE_COLOR
    if node["leaf"] and node["chunkRoot"]:
        col = CHUNK_ROOT_AND_LEAF_COLOR
    elif node["leaf"]:
        col = LEAF_COLOR
    elif node["chunkRoot"]:
        col = CHUNK_ROOT_COLOR
    return f"{dotnodelabel(node)} [style=filled, fillcolor={col}];"


def dotedge(src, dst, kind):
    col = None
    if kind == "left":
        col = LEFT_COLOR
    if kind == "rite":
        col = RITE_COLOR
    if kind == "parent":
        col = PARENT_COLOR

    src = dotnodelabel(src)
    dst = dotnodelabel(dst)
    return f"{src}->{dst} [style=bold, color={col}];"


def invisible_aux(parent):
    child_label = f'"invisible{parent["id"]}"'
    invisible_child = f"{child_label} [label={child_label}, style=invis];"
    invisible_edge = f"{dotnodelabel(parent)}->{child_label} [style=invis];"
    return invisible_child, invisible_edge


def graph(node_strings, edge_strings):
    header = """digraph{
ordering = out;
"""
    footer = """}
"""
    content = header
    for s in node_strings:
        content += s + "\n"
    for s in edge_strings:
        content += s + "\n"
    content += footer
    return content


edge_objs = get_obj()
node_objs = {}

nodes = {}
lefts = {}
rites = {}
parents = {}


for edge_obj in edge_objs:
    src = edge_obj["src"]
    dst = edge_obj["dst"]
    src_id = src["id"]
    dst_id = dst["id"]

    node_objs[src_id] = src
    node_objs[dst_id] = dst

    kind = edge_obj["type"]

    nodes[src_id] = dotnode(src)
    nodes[dst_id] = dotnode(dst)

    if kind == "left":
        lefts[src_id] = dotedge(src, dst, kind)
    if kind == "rite":
        rites[src_id] = dotedge(src, dst, kind)
    if kind == "parent":
        parents[src_id] = dotedge(src, dst, kind)

needs_left = set()
needs_rite = set()
for src_id, edge_str in lefts.items():
    if src_id not in rites.keys():
        needs_rite.add(src_id)
for src_id, edge_str in rites.items():
    if src_id not in lefts.keys():
        needs_left.add(src_id)

for node_id in needs_left:
    child, edge = invisible_aux(node_objs[node_id])
    nodes[-node_id] = child
    lefts[-node_id] = edge

for node_id in needs_rite:
    child, edge = invisible_aux(node_objs[node_id])
    nodes[-node_id] = child
    rites[-node_id] = edge

edges = list(lefts.values()) + list(rites.values()) + list(parents.values())
nodes = list(nodes.values())

print("\n".join(edges))
print("\n".join(nodes))

g = graph(nodes, edges)
with open(f"dump/{filename}.dot", "w") as f:
    f.write(g)
