import matplotlib.pyplot as plt
import networkx as nx

from graph import Graph
import sat

def bin_arb_layout(graph: nx.DiGraph, root, area=((-1, 1), (-1, 1)), i=0):
    x, y = area
    midx = sum(x) / 2
    midy = sum(y) / 2
    if len(graph) == 1:
        return {nx.utils.arbitrary_element(graph): (midx, midy)}
    # (root, _), (subroot, _) = heapq.nlargest(2, graph.out_degree(), key=lambda p: p[1])
    subroot = max(graph.successors(root), key=lambda v: graph.out_degree(v))
    subnodes = nx.descendants(graph, subroot) | {subroot}
    subarb1, subarb2 = graph.subgraph(graph.nodes - subnodes), graph.subgraph(subnodes)
    if i % 2 == 0:
        x1, x2 = (x[0], midx), (midx, x[1])
        y1, y2 = y, (y[0] + 0.25, y[1] + 0.25)
    else:
        x1, x2 = x, (x[0] + 0.25, x[1] + 0.25)
        y1, y2 = (y[0], midy), (midy, y[1])
    out = bin_arb_layout(subarb1, root, (x1, y1), i + 1)
    out.update(bin_arb_layout(subarb2, subroot, (x2, y2), i + 1))
    return out
    # return bin_arb_layout(subarb1, root, coords1, i + 1) | bin_arb_layout(subarb2, subroot, coords2, i + 1)

def line_layout(order, a_f):
    out = {v: (i, 0) for i, v in enumerate(order)}
    for u, v in a_f:
        out[u] = out[u][0], 1
        out[v] = out[v][0], 1
    return out

tournament = Graph(4)
tournament.make_tournament(feedback=((0, 3), (0, 2), (3, 4)))

fig, (ax1, ax2) = plt.subplots(1, 2)
g = nx.DiGraph(tournament.data)
nx.draw(g, with_labels=True, pos=line_layout(tournament.order, a_f=tournament.feedback), ax=ax1)
v_star = 4
result = sat.solve_one(tournament, v_star, decision=False)
if result is not None:
    # nx.relabel_nodes(result, node_map, copy=False)
    nx.draw(result, with_labels=True, pos=bin_arb_layout(result, v_star), ax=ax2)  # node_map[v_star]
    plt.show()
