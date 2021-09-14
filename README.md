Installing
-----
- Install Python (version 3.8 or above) from https://www.python.org/downloads/
- Run `pip install -r requirements_sat.txt` to install dependencies.

Running
-----
- `python demo.py` will solve an instance and show the decoded s.b.a.
  The instance can be changed at the bottom of the script (lines 41-43).
- `python single.py` will solve an instance with all algorithms and print run times.
- `python times.py` will solve randomly generated instances and write run times and results to a file.
  You may need to create the file / folder to output times to.
- From another python script / shell `sat.solve_one(tournament, v_star)` and `dp.solve_one(tournament, v_star)`
  will solve a specified instance with the specified algorithm.
  See the above scripts for details.

It is also possible (though not recommended) to run ILP however addition dependencies are required:
`pip install -r requirements_ilp.txt`
Then to run: `python ilp.py`

References
-----
- H. Aziz et al. “Fixing a Balanced Knockout Tournament”. In: Proceedings of the
Twenty-Eighth AAAI Conference on Artificial Intelligence. 2014, pp. 552–558.
- Sushmita Gupta et al. “On Succinct Encodings for the Tournament Fixing Prob-
lem”. In: Proceedings of the Twenty-Eighth International Joint Conference on Ar-
tificial Intelligence, IJCAI-19. International Joint Conferences on Artificial Intelli-
gence Organization, July 2019, pp. 322–328. doi: 10.24963/ijcai.2019/46. url:
https://doi.org/10.24963/ijcai.2019/46.
- Sushmita Gupta et al. “When Rigging a Tournament, Let Greediness Blind You”.
In: Proceedings of the Twenty-Seventh International Joint Conference on Artificial
Intelligence, IJCAI-18. International Joint Conferences on Artificial Intelligence
Organization, July 2018, pp. 275–281. doi: 10 .24963 /ijcai .2018 /38. url:
https://doi.org/10.24963/ijcai.2018/38.
- M. S. Ramanujan and Stefan Szeider. “Rigging Nearly Acyclic Tournaments Is
Fixed-Parameter Tractable”. In: Proceedings of the Thirty-First AAAI Conference
on Artificial Intelligence. 2017, pp. 3929–3935.