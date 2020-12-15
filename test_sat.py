import itertools
import unittest

import aiger_sat

from sat import Conditions, all_


def switch_ith(a, i):
    return a[:i] + (~a[i],) + a[i + 1:]

def val_to_encode(val, f, inds):
    return tuple(f(i) if ((val >> i) & 1) == 1 else ~f(i) for i in inds)

class Test(unittest.TestCase):
    def and_false(self, *expr):
        self.assertEqual(aiger_sat.solve(all_(expr)), None)

    def and_true(self, *expr):
        self.assertTrue(aiger_sat.is_sat(all_(expr)))

    def test_at_most_one_parent(self):
        # TODO: test excluding v_star
        afud = {0, 1, 2}
        cond = Conditions(
            afud=afud,
            afuddv=afud
        )
        l = cond.gen_l_vars()
        a = cond.at_most_one_parent(1)
        self.and_false(a, l[0, 1], l[2, 1])
        self.and_true(a, l[0, 1], ~l[2, 1])
        self.and_true(a, ~l[0, 1], ~l[2, 1])

    def test_verify_dist(self):
        afud = {0, 1, 2}
        afuddv = {1, 2}
        cond = Conditions(
            afud=afud,
            afuddv=afuddv,
            v_star=0,
            ln=2
        )
        l = cond.gen_l_vars()
        dist = cond.gen_dist_vars()
        a = cond.verify_dist(1, 1)
        self.and_true(a, dist[1, 1], l[0, 1])
        self.and_false(a, dist[1, 1], ~l[0, 1])
        self.and_true(a, ~dist[1, 1])
        a = cond.verify_dist(1, 2)
        self.and_true(a, dist[1, 2], dist[2, 1], l[2, 1])
        self.and_false(a, dist[1, 2], dist[2, 1], ~l[2, 1])
        self.and_false(a, dist[1, 2], ~dist[2, 1], l[2, 1])

    def test_same_bit_vars(self):
        cond = Conditions(
            afud={0, 1},
            ln=2
        )
        chi = cond.gen_chi_vars()
        sbv, sbc = cond.gen_same_bit_vars()
        u, v = 0, 1
        self.and_true(sbc,
                      sbv[u, v, 0], chi[u, 0], chi[v, 0],
                      sbv[u, v, 1], ~chi[u, 1], ~chi[v, 1])
        self.and_true(sbc,
                      ~sbv[u, v, 0], chi[u, 0], ~chi[v, 0],
                      ~sbv[u, v, 1], ~chi[u, 1], chi[v, 1])
        self.and_false(sbc,
                       sbv[u, v, 0], chi[u, 0], ~chi[v, 0],
                       sbv[u, v, 1], ~chi[u, 1], chi[v, 1])
        self.and_false(sbc,
                       ~sbv[u, v, 0], chi[u, 0], chi[v, 0],
                       ~sbv[u, v, 1], ~chi[u, 1], ~chi[v, 1])

    def test_loc_check_size_dec(self):
        cond = Conditions(
            afud={0, 1},
            a_f={0, 1},
            ln=2
        )
        l = cond.gen_l_vars()
        chi = cond.gen_chi_vars()
        _, sb = cond.gen_same_bit_vars()
        a = sb & cond.loc_check_size_dec(0, 1)
        self.and_true(a, l[0, 1], chi[0, 0], ~chi[0, 1], chi[0, 2],
                      chi[1, 0], ~chi[1, 1], ~chi[1, 2])
        self.and_false(a, l[0, 1], chi[0, 0], ~chi[0, 1], ~chi[0, 2],
                       chi[1, 0], chi[1, 1], ~chi[1, 2])
        self.and_false(a, l[0, 1], chi[0, 0], chi[0, 1], ~chi[0, 2],
                       chi[1, 0], chi[1, 1], ~chi[1, 2])
        self.and_true(a, l[0, 1], chi[0, 0], ~chi[0, 1], ~chi[0, 2],
                      ~chi[1, 0], ~chi[1, 1], ~chi[1, 2])

    def test_loc_check_size_diff(self):
        cond = Conditions(
            afud={0, 1, 2},
            a_f={0, 1, 2},
            ln=2
        )
        l = cond.gen_l_vars()
        chi = cond.gen_chi_vars()
        _, sb = cond.gen_same_bit_vars()
        a = sb & cond.loc_check_size_diff(0, 1, 2)
        self.and_true(a, l[0, 1], l[0, 2],
                      chi[1, 0], ~chi[1, 1], chi[1, 2],
                      chi[2, 0], ~chi[2, 1], ~chi[2, 2])
        self.and_false(a, l[0, 1], l[0, 2],
                       chi[1, 0], ~chi[1, 1], ~chi[1, 2],
                       chi[2, 0], ~chi[2, 1], ~chi[2, 2])
        self.and_false(a, l[0, 1], l[0, 2],
                       chi[1, 0], chi[1, 1], chi[1, 2],
                       chi[2, 0], chi[2, 1], chi[2, 2])
        self.and_true(a, ~l[0, 1])

    @unittest.skip
    def test_loc_check_path(self):
        cond = Conditions(
            afud={0, 1, 2},
            v_star=1,
            ln=2
        )
        l = cond.gen_l_vars()
        chi = cond.gen_chi_vars()
        length = cond.gen_length_vars()
        u, v = 1, 2
        a = cond.loc_check_path(u, v)
        # chi(u) = 7, chi[v] = 6, l(u, v) = 0
        self.and_true(a, l[u, v], ~l[u, 0],
                      chi[u, 0], chi[u, 1], chi[u, 2],
                      ~chi[v, 0], chi[v, 1], chi[v, 2],
                      ~length[u, v, 0], ~length[u, v, 1])

    def test_w_vars(self):
        lln = 2
        cond = Conditions(
            afud={0},
            ln=2**lln
        )
        chi = cond.gen_chi_vars()
        wv, wc = cond.gen_w_vars()
        v = 0
        clauses = wc & cond.exactly_one_size_bit(v)
        valid = set()
        for bs in itertools.chain(itertools.product((False, True), repeat=lln), ((False,) * lln + (True,),)):
            val = sum(2**i for i, b in enumerate(bs) if b)
            chis = tuple(chi[v, i] if i == val else ~chi[v, i] for i in range(cond.ln + 1))
            ws = tuple(wv[v, i] if b else ~wv[v, i] for i, b in enumerate(bs))
            assignments = chis + ws
            valid.add(assignments)
            with self.subTest(val=val):
                self.and_true(clauses, *assignments)
            for i in range(len(assignments)):
                with self.subTest(val=val, wrong=i):
                    # result = aiger_sat.solve(all_())
                    # self.assertEqual(result, None)
                    self.and_false(clauses, *switch_ith(assignments, i))

    # @unittest.skip
    def test_y_vars(self):
        cond = Conditions(
            afud={0, 1},
            ln=4,
            v_star=0
        )
        cond.gen_chi_vars()
        length = cond.gen_length_vars()
        wv, wc = cond.gen_w_vars()
        yv, yc = cond.gen_y_vars()
        u, v = 0, 1
        chi_v = 4
        l_u_v = 4
        ws = val_to_encode(chi_v, lambda x: wv[v, x], cond.lln_indices)
        ls = val_to_encode(l_u_v, lambda x: length[u, v, x], cond.lln_indices)
        result = val_to_encode(chi_v + l_u_v, lambda x: yv[u, v, x], cond.lln_indices + [cond.lln])
        self.and_true(wc, yc, *(ws + ls + result))
