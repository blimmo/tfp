import cProfile

import sat
from graph import Graph

tournament = Graph(3)
tournament.make_tournament(feedback=((0, 4),))

# with evaluate(False):
cProfile.run("sat.solve_one(tournament, 1)")
