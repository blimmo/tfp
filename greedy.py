import itertools

import networkx


class Template(networkx.DiGraph):
    def __eq__(self, other):
        if len(self.edges) != len(other.edges):
            return False
        for (u, v), (x, y) in zip(self.edges, other.edges):
            if not (((u == x) or (u < 0 and x < 0))
                    and ((v == y) or (v < 0 and y < 0))):
                return False
        return True



# def rooted_trees(a_f):
#     max_size = min(2 * len(a_f) + 1, G.n)
#     for total_vertices in range(len(a_f), max_size + 1):
def templates(a_f, size):
    out = []  # Templates aren't hashable so no set here
    mapping = dict(zip(range(size), itertools.chain(a_f, range(-1, len(a_f) - size - 1, -1))))
    for arb in arborescences(size):
        tpl = Template(networkx.relabel_nodes(arb, mapping))
        if tpl not in out:
            out.append(tpl)
            yield tpl
        # for unlabelled in itertools.combinations(arb.nodes, size - len(a_f)):

def arborescences(size):
    for p_seq in itertools.product(range(size), repeat=size - 2):
        undir_h = networkx.from_prufer_sequence(p_seq)
        # for root in range(total_vertices):
        h = networkx.DiGraph()
        for u, v in networkx.dfs_edges(undir_h, 0):
            h.add_edge(u, v)
        yield h

def solve_one(G, v_star):
    v_f = frozenset(sum(G.feedback))
    a_f = v_f.union((v_star,))
    a_f_tuple = tuple(a_f)
    max_size = min(2 * len(a_f) + 1, G.n)
    for size in range(len(a_f), max_size + 1):
        for t_star in templates(a_f_tuple, size):
            for lengths in itertools.product(range(G.ln), repeat=len(t_star.edges)):
                for siz in itertools.product(range(G.ln), repeat=len(v_f)):
                    pass


if __name__ == "__main__":
    for i, h in enumerate(templates((4, 7, 5), 8)):
        print(i, h.edges)
