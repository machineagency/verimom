from z3 import *
from math import *
from random import seed, randint, random
from example_progs import *
from analyzer import Analyzer, LangUtil

class Rewriter():
    def __init__(self, prog_t):
        self.prog_t_text = prog_t
        self.prog_r_text = prog_t[:]
        self.prog_rp_text = prog_t[:]
        prog_t_stats = LangUtil.prog_text_to_statements(self.prog_t_text)
        prog_r_stats = LangUtil.prog_text_to_statements(self.prog_r_text)
        prog_rp_stats = LangUtil.prog_text_to_statements(self.prog_rp_text)
        self.prog_t = LangUtil.statements_to_dicts(prog_t_stats)
        self.prog_r = LangUtil.statements_to_dicts(prog_r_stats)
        self.prog_rp = LangUtil.statements_to_dicts(prog_rp_stats)
        self.RANDOM_SEED = 5373171
        self.COLLISION_PENALTY = 100
        self.BETA = 2
        seed(self.RANDOM_SEED)
        self.analyzer = Analyzer((300, 300), (0, 0), (300, 0))

    def change_instr(self, line_num):
        d = self.prog_rp[line_num]
        if d['instr'] == 'moveTo':
            d['instr'] = 'travel'
        elif d['instr'] == 'travel':
            d['instr'] = 'moveTo'
        d = LangUtil.update_dict_statement(d)

    def change_operand(self, line_num):
        d = self.prog_rp[line_num]
        if d['instr'] == 'moveTo' or d['instr'] == 'travel':
            op_num = randint(0, 2)
            if op_num == 0:
                d['x'] = randint(0, self.analyzer.X_LIM)
            if op_num == 1:
                d['y'] = randint(0, self.analyzer.Y_LIM)
            if op_num == 2:
                d['r'] = randint(1, 2)
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
        d0 = self.prog_rp[line_num]
        d1 = self.prog_rp[other_line_num]
        self.prog_rp[line_num], self.prog_rp[other_line_num] = d1, d0

    def change_line(self, line_num):
        d = self.prog_rp[line_num]
        instrs = ['moveTo', 'travel', 'sleep']
        d['instr'] = instrs[randint(0, 2)]
        if d['instr'] == 'moveTo' or d['instr'] == 'travel':
            d['x'] = randint(0, self.analyzer.X_LIM)
            d['y'] = randint(0, self.analyzer.Y_LIM)
            d['r'] = randint(1, 2)
        if d['instr'] == 'sleep':
            # TODO: either use canned immediates or constraint s operand
            # to total time taken
            d['s'] = randint(0, 10)
            d['r'] = randint(1, 2)
        d = LangUtil.update_dict_statement(d)

    def add_or_delete_line(self, line_num):
        add_or_delete = randint(0, 1)
        if add_or_delete == 0 and len(self.prog_rp) > 1:
            del self.prog_rp[line_num]
        else:
            self.prog_rp.insert(line_num, { 'instr' : 'noop' })
            self.change_line(line_num)

    def accept(self):
        numer = self.cost(self.prog_t, self.prog_rp)
        denom = self.cost(self.prog_t, self.prog_r)
        if denom == 0:
            return 1
        return min(1, e ** -self.BETA * (numer / denom))

    def cost(self, prog_t, prog_r):
        # print(prog_t)
        # print(prog_r)
        # print(f'EQ: {self.eq(prog_t, prog_r)}')
        # print(f'PERF: {self.perf(prog_t, prog_r)}')
        return 100 * self.eq(prog_t, prog_r) + self.perf(prog_t, prog_r)

    def eq(self, prog_t, prog_r):
        prog_t_text = LangUtil.dicts_to_text(prog_t)
        prog_r_text = LangUtil.dicts_to_text(prog_r)
        return self.analyzer.check_equivalent_nosmt(prog_t_text, prog_r_text)

    def perf(self, prog_t, prog_r):
        prog_t_text = LangUtil.dicts_to_text(prog_t)
        prog_r_text = LangUtil.dicts_to_text(prog_r)
        running_time_diff = self.analyzer.find_running_time(prog_r_text)\
                            - self.analyzer.find_running_time(prog_t_text)
        collision_penalty = self.collisions(prog_r_text) * self.COLLISION_PENALTY
        return running_time_diff + collision_penalty

    def collisions(self, prog):
        return self.analyzer.check_collision(prog)

    def run(self, steps):
        def flip(p):
            return random() < p
        NUM_PERMUTATIONS = 5
        for _ in range(0, steps):
            permutation_choice = randint(0, NUM_PERMUTATIONS)
            line_num = self.get_random_line_num()
            # print(f'Line num: {line_num}')
            # print(f'P: {permutation_choice}')
            if permutation_choice == 0:
                self.change_instr(line_num)
            if permutation_choice == 1:
                self.change_operand(line_num)
            if permutation_choice == 2:
                self.swap_instr(line_num)
            if permutation_choice == 3:
                self.change_line(line_num)
            if permutation_choice == 4:
                self.add_or_delete_line(line_num)

            accept_prob = self.accept()
            # print(accept_prob)
            if flip(accept_prob):
                self.prog_r = self.prog_rp.copy()
            else:
                self.prog_rp = self.prog_r.copy()
        self.prog_r = self.prog_rp.copy()

    def random_walk(self, steps):
        NUM_PERMUTATIONS = 5
        for _ in range(0, steps):
            permutation_choice = randint(0, NUM_PERMUTATIONS)
            line_num = self.get_random_line_num()
            # print(f'Line num: {line_num}')
            # print(f'P: {permutation_choice}')
            if permutation_choice == 0:
                self.change_instr(line_num)
            if permutation_choice == 1:
                self.change_operand(line_num)
            if permutation_choice == 2:
                self.swap_instr(line_num)
            if permutation_choice == 3:
                self.change_line(line_num)
            if permutation_choice == 4:
                self.add_or_delete_line(line_num)
            # print(self.curr_rewrite)
        self.prog_r = self.prog_rp.copy()

    def get_random_line_num(self):
        return randint(0, len(self.prog_rp) - 1)

    @property
    def curr_rewrite(self):
        return LangUtil.dicts_to_text(self.prog_rp)

if __name__ == '__main__':
    rw = Rewriter(prog_safe_r1_set)
    rw.run(100)
    print(rw.curr_rewrite)
    print(f'T: {rw.analyzer.find_running_time(rw.curr_rewrite)}')
    print(f'EQ: {rw.analyzer.check_equivalent_nosmt(rw.prog_t_text, rw.curr_rewrite)}')

