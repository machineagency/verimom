from z3 import *

prog_unsafe_r1_collide = """moveTo(150, 100, 0, 1);
moveTo(100, 150, 0, 2);
moveTo(150, 200, 0, 1);
"""

prog_safe_r1_set = """moveTo(150, 100, 0, 1);
moveTo(100, 150, 0, 2);
"""

prog_safe_longer = """moveTo(150, 100, 0, 1);
moveTo(100, 150, 0, 2);
moveTo(100, 160, 0, 2);
moveTo(100, 170, 0, 2);
moveTo(50, 100, 0, 1);
moveTo(0, 0, 0, 1);
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
                 'r': int(arg_lst[3]),\
                 'statement': statement\
        }

    @staticmethod
    def statements_to_dicts(statements):
        return list(map(LangUtil.stat_to_arg_dict, statements))

    @staticmethod
    def bin_stat_dicts_by_r(dicts):
        return [list(filter(lambda d: d['r'] == 1, dicts)),\
                list(filter(lambda d: d['r'] == 2, dicts))]

class ProgSolver():
    def __init__(self):
        self.s = z3.Solver()
        self.s.set(':core.minimize', True)
        self.clock_r1 = 0
        self.clock_r2 = 0
        self.ROBOT_ARM_WIDTH = 5
        self.SYM_VAR_CLOCK = Real('t')

    def write_clock_frozen(self):
        c = self.SYM_VAR_CLOCK == 0
        self.s.add(c)
        return c

    def write_single_move_to(self, stat_dict):
        time_cond = self.SYM_VAR_CLOCK == 0
        x_cond = Real(f'r{stat_dict["r"]}x') == stat_dict['x']
        y_cond = Real(f'r{stat_dict["r"]}y') == stat_dict['y']
        c = Implies(time_cond, And(x_cond, y_cond))
        self.s.assert_and_track(c, f'SINGLE<{stat_dict["statement"]}>')
        return c

    def write_pair_move_to(self, stat_dict0, stat_dict1):
        if stat_dict0['r'] != stat_dict1['r']:
            print('Error: cannot write a pair constraint with different arms:')
            print(stat_dict0['statement'])
            print(stat_dict1['statement'])
            return None
        time_cond = self.SYM_VAR_CLOCK == 0
        r1x = Real('r1x')
        r1y = Real('r1y')
        r2x = Real('r2x')
        r2y = Real('r2y')
        w = self.ROBOT_ARM_WIDTH
        x = stat_dict0['x']
        xp = stat_dict1['x']
        y = stat_dict0['y']
        yp = stat_dict1['y']
        max_y = max(stat_dict0['y'], stat_dict1['y'])
        min_y = min(stat_dict0['y'], stat_dict1['y'])
        # Assuming ---r1---> <---r2---
        if stat_dict0['r'] == 1:
            if xp >= x:
                # infeasible region is ABOVE line, flipped for +y south
                line_constr = -(r2x - x) * (yp - y) + (r2y - y) * (xp - x) >= 0
            else:
                # infeasible region is BELOW line, flipped for +y south
                line_constr = -(r2x - x) * (yp - y) + (r2y - y) * (xp - x) <= 0
            c = Not(And(r2y >= min_y - w / 2,\
                        r2y >= max_y + w / 2,\
                        line_constr))
        else:
            if xp >= x:
                # infeasible region is ABOVE line, flipped for +y south
                line_constr = -(r1x - x) * (yp - y) + (r1y - y) * (xp - x) >= 0
            else:
                # infeasible region is BELOW line, flipped for +y south
                line_constr = -(r1x - x) * (yp - y) + (r1y - y) * (xp - x) <= 0
            c = Not(And(r1y >= min_y - w / 2,\
                        r1y >= max_y + w / 2,\
                        line_constr))
        c_with_time = Implies(time_cond, c)
        self.s.assert_and_track(c_with_time,\
                f'PAIR<{stat_dict0["statement"]}, {stat_dict1["statement"]}>')
        return c_with_time

    def write_move_to_arm(self, stat_dict):
        time_cond = self.SYM_VAR_CLOCK == 0
        r1x = Real('r1x')
        r1y = Real('r1y')
        r2x = Real('r2x')
        r2y = Real('r2y')
        w = self.ROBOT_ARM_WIDTH
        # Assuming ---r1---> <---r2---
        if stat_dict["r"] == 1:
            c = Not(And(stat_dict['x'] >= r2x, stat_dict['y'] >= r2y - w / 2,\
                        stat_dict['y'] <= r2y + w / 2))
        else:
            c = Not(And(stat_dict['x'] <= r1x, stat_dict['y'] >= r1y - w / 2,\
                        stat_dict['y'] <= r1y + w / 2))
        c_with_time = Implies(time_cond, c)
        self.s.assert_and_track(c_with_time, f'ARM<{stat_dict["statement"]}>')
        return c_with_time

    @property
    def assertions(self):
        return [a for a in self.s.assertions()]

    @property
    def unsat_core(self):
        return self.s.unsat_core()

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
    def bin_test(prog):
        stats = LangUtil.prog_text_to_statements(prog)
        dicts = LangUtil.statements_to_dicts(stats)
        bins = LangUtil.bin_stat_dicts_by_r(dicts)
        return bins

    @staticmethod
    def run_pairs_on_prog(prog):
        stats = LangUtil.prog_text_to_statements(prog)
        dicts = LangUtil.statements_to_dicts(stats)
        bins = LangUtil.bin_stat_dicts_by_r(dicts)
        ps = ProgSolver()
        for r_bin in bins:
            for idx in range(len(r_bin) - 1):
                ps.write_pair_move_to(r_bin[idx], r_bin[idx + 1])
        try:
            # print(ps.assertions)
            result = ps.check()
            if result == unsat:
                print('UNSAT')
                print(f'Minimal unsatisfiable core: {ps.unsat_core}')
                return {}
            print('SAT')
            return ps.model()
        except Exception as e:
            print(f'Error during solving: {e}')
            return {}

    @staticmethod
    def run_on_prog(prog):
        stats = LangUtil.prog_text_to_statements(prog)
        dicts = LangUtil.statements_to_dicts(stats)
        # print(stat_dicts)
        ps = ProgSolver()
        ps.write_clock_frozen()
        for stat in dicts:
            ps.write_single_move_to(stat)
            ps.write_move_to_arm(stat)
        try:
            # for a in ps.assertions:
            #     print(a)
            result = ps.check()
            if result == unsat:
                print('UNSAT')
                print(f'Minimal unsatisfiable core: {ps.unsat_core}')
                return {}
            print('SAT')
            return ps.model()
        except Exception as e:
            print(f'Error during solving: {e}')
            return {}

if __name__ == '__main__':
    print("Testing binning on unsafe program.")
    print(TestUtil.bin_test(prog_unsafe_r1_collide))
    print("Running on safe program.")
    print(TestUtil.run_on_prog(prog_safe_r1_set))
    print("Running on unsafe program.")
    print(TestUtil.run_on_prog(prog_unsafe_r1_collide))
    print("Running pairs on longer program.")
    print(TestUtil.run_pairs_on_prog(prog_safe_longer))

