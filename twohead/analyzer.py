from z3 import *

prog_unsafe_r1_collide = """moveTo(150, 100, 0, 1);
moveTo(100, 150, 0, 2);
moveTo(150, 200, 0, 1);
"""

prog_safe_r1_set = """moveTo(150, 100, 0, 1);
moveTo(100, 150, 0, 2);
"""

class LangUtil():
    def __init__(self):
        pass

    @staticmethod
    def prog_text_to_statements(prog_text):
        stats_preclean = list(filter(lambda stat: stat is not '',\
                                     prog_text.split(';\n')))
        return stats_preclean

    @staticmethod
    def stat_to_arg_dict(statement):
        instr = LangUtil.peek_instr(statement)
        if instr == 'moveTo':
            return LangUtil.parse_move_to(statement)
        else:
            print(f'Unrecognized instruction: {instr}')
            return {}

    @staticmethod
    def peek_instr(statement):
        return statement.split('(')[0]

    @staticmethod
    def parse_move_to(statement):
        arg_lst = statement.replace('(', ',')\
                           .replace(')', ',')\
                           .split(',')[1:5]
        return { 'x': int(arg_lst[0]),\
                 'y': int(arg_lst[1]),\
                 'z': int(arg_lst[2]),\
                 'r': int(arg_lst[3])\
        }

class ProgSolver():
    def __init__(self):
        self.s = z3.Solver()
        self.clock_r1 = 0
        self.clock_r2 = 0
        self.SYM_VAR_CLOCK = Real('t')

    def write_clock_frozen_constraint(self):
        c = self.SYM_VAR_CLOCK == 0
        self.s.add(c)
        return c

    def write_single_move_to_constraint(self, stat_dict):
        time_cond = self.SYM_VAR_CLOCK == 0
        x_cond = Real(f'r{stat_dict["r"]}x') == stat_dict['x']
        y_cond = Real(f'r{stat_dict["r"]}y') == stat_dict['y']
        c = Implies(time_cond, And(x_cond, y_cond))
        self.s.add(c)
        return c

    @property
    def assertions(self):
        return [a for a in self.s.assertions()]

    def check(self):
        return self.s.check()

    def model(self):
        return self.s.model()

    def solve(self):
        return self.s.solve()

class TestUtil():
    def __init__(self):
        pass

    @staticmethod
    def statement_0():
        stats = LangUtil.prog_text_to_statements(prog_safe_r1_set)
        stat_dicts = map(lambda stat: LangUtil.stat_to_arg_dict(stat), stats)
        stat_dicts = list(stat_dicts)
        print(stat_dicts)
        ps = ProgSolver()
        ps.write_clock_frozen_constraint()
        for stat in stat_dicts:
            ps.write_single_move_to_constraint(stat)
        try:
            for a in ps.assertions:
                print(a)
            ps.check()
            return ps.model()
        except Exception as e:
            print(f'Could not solve: {e}')
            return {}

if __name__ == '__main__':
    print(TestUtil.statement_0())

