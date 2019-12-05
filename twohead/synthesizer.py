from z3 import *
from math import *
from random import seed, randint
from example_progs import *
from analyzer import Analyzer, LangUtil

class Rewriter():
    def __init__(self, prog_t):
        self.prog_t_text = prog_t
        self.prog_r_text = prog_t[:]
        prog_t_stats = LangUtil.prog_text_to_statements(self.prog_t_text)
        prog_r_stats = LangUtil.prog_text_to_statements(self.prog_r_text)
        self.prog_t = LangUtil.statements_to_dicts(prog_t_stats)
        self.prog_r = LangUtil.statements_to_dicts(prog_r_stats)
        self.RANDOM_SEED = 9382107
        seed(self.RANDOM_SEED)
        self.analyzer = Analyzer((300, 300), (0, 0), (300, 0))

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

    @property
    def curr_rewrite(self):
        return LangUtil.dicts_to_text(self.prog_r)

if __name__ == '__main__':
    rw = Rewriter(prog_safe_r1_set)
    rw.random_walk(3)
    print(rw.curr_rewrite)

