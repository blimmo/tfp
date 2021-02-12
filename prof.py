import cProfile

import sat
from graph import Graph

tournament = Graph(4)
tournament.make_tournament(feedback=((5, 10), (0, 11)))

cProfile.run("sat.solve_one(tournament, 1)")
