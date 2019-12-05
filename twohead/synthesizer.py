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

    def change_instr(self, line_num):
        d = self.prog_r[line_num]
        if d['instr'] == 'moveTo':
            d['instr'] = 'travel'
        elif d['instr'] == 'travel':
            d['instr'] = 'moveTo'
        d = LangUtil.update_dict_statement(d)

    def change_operand(self, line_num):
        d = self.prog_r[line_num]
        if d['instr'] == 'moveTo' or d['instr'] == 'travel':
            op_num = randint(0, 2)
            if op_num == 0:
                d['x'] = randint(0, self.analyzer.X_LIM)
            if op_num == 1:
                d['y'] = randint(0, self.analyzer.Y_LIM)
            if op_num == 2:
                d['r'] = randint(1, 3)
        if d['instr'] == 'sleep':
            op_num = randint(0, 1)
            if op_num == 0:
                # TODO: either use canned immediates or constraint s operand
                # to total time taken
                d['s'] = randint(0, 10)
            if op_num == 1:
                d['r'] = randint(1, 2)
        d = LangUtil.update_dict_statement(d)

    def swap_instr(self, line_num):
        other_line_num = self.get_random_line_num()
        d0 = self.prog_r[line_num]
        d1 = self.prog_r[other_line_num]
        self.prog_r[line_num], self.prog_r[other_line_num] = d1, d0

    def change_line(self, line_num):
        d = self.prog_r[line_num]
        instrs = ['moveTo', 'travel', 'sleep']
        d['instr'] = instrs[randint(0, 2)]
        if d['instr'] == 'moveTo' or d['instr'] == 'travel':
            d['x'] = randint(0, self.analyzer.X_LIM)
            d['y'] = randint(0, self.analyzer.Y_LIM)
            d['r'] = randint(1, 3)
        if d['instr'] == 'sleep':
            # TODO: either use canned immediates or constraint s operand
            # to total time taken
            d['s'] = randint(0, 10)
            d['r'] = randint(1, 2)
        d = LangUtil.update_dict_statement(d)

    def add_or_delete_line(self, line_num):
        add_or_delete = randint(0, 3)
        if add_or_delete == 0:
            del self.prog_r[line_num]
        else:
            self.prog_r.insert(line_num, { 'instr' : 'noop' })
            self.change_line(line_num)

    def random_walk(self, steps):
        pass

    @property
    def curr_rewrite(self):
        return LangUtil.dicts_to_text(self.prog_r)

if __name__ == '__main__':
    rw = Rewriter(prog_safe_r1_set)
    rw.random_walk(3)
    print(rw.curr_rewrite)

