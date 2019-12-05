from z3 import *
from math import *
from random import seed, randint
from example_progs import *
from analyzer import Analyzer, LangUtil

class Rewriter():
    def __init__(self, prog_t):
        self.prog_t_text = prog_t[:]
        self.prog_r_text = prog_r[:]
        prog_t_stats = LangUtil.prog_text_to_statements(prog_t)
        prog_r_stats = LangUtil.prog_text_to_statements(prog_r)
        self.prog_t = LangUtil.statements_to_dicts(prog_t_stats)
        self.prog_r = LangUtil.statements_to_dicts(prog_r_stats)

    def change_instr(self):
        pass

    def change_operand(self):
        pass

    def swap_instr(self):
        pass

    def change_line(self):
        pass

    def random_walk(self, steps):
        pass

