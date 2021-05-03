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
    # In 3.9:
    # return bin_arb_layout(subarb1, root, coords1, i + 1) | bin_arb_layout(subarb2, subroot, coords2, i + 1)

def line_layout(order, a_f):
    out = {v: (i, 0) for i, v in enumerate(order)}
    for u, v in a_f:
        out[u] = out[u][0], 1
        out[v] = out[v][0], 1
    return out

def show(result, v_star):
    if result is not None:
        nx.draw(result, with_labels=True, pos=bin_arb_layout(result, v_star))
        plt.show()

if __name__ == "__main__":
    tournament = Graph(3)
    tournament.make_tournament(feedback=((3, 7), (0, 7)))

    g = nx.DiGraph(tournament.data)
    v_star = 0
    result = sat.solve_one(tournament, v_star, decision=False)
    show(result, v_star)
