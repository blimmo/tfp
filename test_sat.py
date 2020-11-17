import unittest

import aiger
import aiger_sat

from sat import Conditions, distinct2, all_

class Test(unittest.TestCase):
    def and_false(self, *expr):
        self.assertEqual(aiger_sat.solve(all_(expr)), None)

    def and_true(self, *expr):
        self.assertTrue(aiger_sat.is_sat(all_(expr)))

    def test_atmostoneparent(self):
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

    def test_locchecksizedec(self):
        cond = Conditions(
            afud={0, 1},
            a_f={0, 1},
            ln=2
        )
        cond.gen_l_vars()
        cond.gen_chi_vars()
        sb = cond.gen_same_bit_vars()
        l = cond.l_vars
        chi = cond.chi_vars
        a = sb & cond.loc_check_size_dec(0, 1)
        self.and_true(a, l[0, 1], chi[0, 0], ~chi[0, 1], chi[0, 2],
                      chi[1, 0], ~chi[1, 1], ~chi[1, 2])
        self.and_false(a, l[0, 1], chi[0, 0], ~chi[0, 1], ~chi[0, 2],
                       chi[1, 0], chi[1, 1], ~chi[1, 2])
        self.and_false(a, l[0, 1], chi[0, 0], chi[0, 1], ~chi[0, 2],
                       chi[1, 0], chi[1, 1], ~chi[1, 2])
        self.and_true(a, l[0, 1], chi[0, 0], ~chi[0, 1], ~chi[0, 2],
                      ~chi[1, 0], ~chi[1, 1], ~chi[1, 2])

    def test_locchecksizediff(self):
        cond = Conditions(
            afud={0, 1, 2},
            a_f={0, 1, 2},
            ln=2
        )
        cond.gen_l_vars()
        cond.gen_chi_vars()
        sb = cond.gen_same_bit_vars()
        l = cond.l_vars
        chi = cond.chi_vars
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
