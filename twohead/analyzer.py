from z3 import *
from math import *

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

prog_unsafe_longer = """moveTo(150, 100, 0, 1);
moveTo(100, 150, 0, 2);
moveTo(100, 160, 0, 2);
moveTo(100, 170, 0, 2);
moveTo(50, 100, 0, 1);
moveTo(0, 0, 0, 1);
moveTo(101, 171, 0, 1);
"""
prog_unsafe_cross = """moveTo(300, 300, 0, 1);
moveTo(0, 300, 0, 2);
"""

prog_safe_sleep_before_collide = """moveTo(150, 100, 0, 1);
sleep(8, 2);
moveTo(100, 150, 0, 2);
moveTo(150, 200, 0, 1);
"""

prog_unsafe_not_enough_sleep_before_collide = """moveTo(150, 100, 0, 1);
sleep(7, 2);
moveTo(100, 150, 0, 2);
moveTo(150, 200, 0, 1);
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
        """
        Naming convention:

        s - the z3 solver
        VAR_NAME - concrete constant
        _var_name - concrete mutable variable
        var_name - symbolic (z3) variable (constant)
        """
        self.s = z3.Solver()
        self.s.set(':core.minimize', True)
        self.ROBOT_ARM_WIDTH = 5
        self.X_LIM = 300
        self.Y_LIM = 300
        self.R1_INIT_X = 0
        self.R1_INIT_Y = 0
        self.R2_INIT_X = self.X_LIM
        self.R2_INIT_Y = 0
        self.VELOCITY = 1
        self._clock_r1 = 0
        self._clock_r2 = 0
        self._curr_r1x = self.R1_INIT_X
        self._curr_r1y = self.R1_INIT_Y
        self._curr_r2x = self.R2_INIT_X
        self._curr_r2y = self.R2_INIT_Y
        self.r1x = Function('r1x', RealSort(), RealSort())
        self.r1y = Function('r1y', RealSort(), RealSort())
        self.r2x = Function('r2x', RealSort(), RealSort())
        self.r2y = Function('r2y', RealSort(), RealSort())
        self.t = Real('t')

    def write_work_envelope(self):
        r1x = self.r1x
        r1y = self.r1y
        r2x = self.r2x
        r2y = self.r2y
        t = self.t
        self.s.assert_and_track(And(r1x(t) >= 0, r1x(t) <= self.X_LIM),
                                f'WORK_ENV: r1x in [0, {self.X_LIM}]')
        self.s.assert_and_track(And(r2x(t) >= 0, r2x(t) <= self.X_LIM),
                                f'WORK_ENV: r2x in [0, {self.X_LIM}]')
        self.s.assert_and_track(And(r1y(t) >= 0, r1y(t) <= self.Y_LIM),
                                f'WORK_ENV: r1y in [0, {self.Y_LIM}]')
        self.s.assert_and_track(And(r2y(t) >= 0, r2y(t) <= self.Y_LIM),
                                f'WORK_ENV: r2y in [0, {self.Y_LIM}]')

    def write_pos_initial(self):
        r1x = self.r1x
        r1y = self.r1y
        r2x = self.r2x
        r2y = self.r2y
        t = self.t
        self.s.assert_and_track(Implies(t == 0, r1x(t) == self.R1_INIT_X),
                                f'R1_INIT_X: {self.R1_INIT_X}')
        self.s.assert_and_track(Implies(t == 0, r1y(t) == self.R1_INIT_Y),
                                f'R1_INIT_Y: {self.R1_INIT_Y}')
        self.s.assert_and_track(Implies(t == 0, r1x(t) == self.R2_INIT_X),
                                f'R2_INIT_X: {self.R2_INIT_X}')
        self.s.assert_and_track(Implies(t == 0, r1x(t) == self.R2_INIT_Y),
                                f'R2_INIT_Y: {self.R2_INIT_Y}')

    def write_arm_constraints(self):
        r1x = self.r1x
        r1y = self.r1y
        r2x = self.r2x
        r2y = self.r2y
        t = self.t
        w = self.ROBOT_ARM_WIDTH
        self.s.assert_and_track(And(\
            And(r2x(t) <= r1x(t),\
                r2y(t) >= r1y(t) - w / 2,\
                r2y(t) <= r1y(t) + w / 2),
            And(r1x(t) >= r2x(t),\
                r1y(t) >= r2y(t) - w / 2,\
                r1y(t) <= r2y(t) + w / 2)),\
            f'ARM')

    def write_pos_move_to(self, stat_dict):
        if stat_dict['r'] == 1:
            x_old = self._curr_r1x
            y_old = self._curr_r1y
            t_old = self._clock_r1
            x = self.r1x
            y = self.r1y
        else:
            x_old = self._curr_r2x
            y_old = self._curr_r2y
            t_old = self._clock_r2
            x = self.r2x
            y = self.r2y

        x_new = stat_dict['x']
        y_new = stat_dict['y']
        dist = sqrt((x_new - x_old) ** 2 + (y_new - y_old) ** 2)
        time_taken = self.VELOCITY * dist
        t_new = t_old + time_taken
        t = self.t

        # Calculate line in y = ... and x = ... forms interpolating endpoints
        self.s.assert_and_track(ForAll([t],\
            Implies(And(t > t_old, t <= t_new),\
                x(t) == (1 - (t - t_old) / time_taken) * x_old\
                    + ((t - t_old) / time_taken) * x_new)),\
                f'POS_X: for r{stat_dict["r"]} on t in ({t_old}, {t_new}]')
        self.s.assert_and_track(ForAll([t],\
            Implies(And(t > t_old, t <= t_new),\
                y(t) == (1 - (t - t_old) / time_taken) * y_old\
                    + ((t - t_old) / time_taken) * y_new)),\
                f'POS_Y: for r{stat_dict["r"]} on t in ({t_old}, {t_new}]')

        # Update (x, y, t)
        if stat_dict['r'] == 1:
            self._curr_r1x = stat_dict['x']
            self._curr_r1y = stat_dict['y']
            self._clock_r1 += time_taken
        else:
            self._curr_r2x = stat_dict['x']
            self._curr_r2y = stat_dict['y']
            self._clock_r2 += time_taken

    def write_time_constraint(self):
        """
        Only call after calling write_pos_move_to on all statements.
        """
        self.s.assert_and_track(self.t >= 0, 'START T: 0')
        self.s.assert_and_track(self.t <= max(self._clock_r1, self._clock_r2),\
                f'END T: {max(self._clock_r1, self._clock_r2)}')

    def write_extend_final_pos_to_end_time(self):
        """
        Only call after calling write_pos_move_to on all statements.
        """
        r1x = self.r1x
        r1y = self.r1y
        r2x = self.r2x
        r2y = self.r2y
        t = self.t
        max_clock = max(self._clock_r1, self._clock_r2)
        if (self._clock_r1 < max_clock):
            self.s.assert_and_track(ForAll([t], Implies(t > self._clock_r1,\
                    r1x(t) == self._curr_r1x)), 'R1X EXTEND')
            self.s.assert_and_track(ForAll([t], Implies(t > self._clock_r1,\
                    r1y(t) == self._curr_r1y)), 'R1Y EXTEND')
        if (self._clock_r2 < max_clock):
            self.s.assert_and_track(ForAll([t], Implies(t > self._clock_r2,\
                    r2x(t) == self._curr_r2x)), 'R2X EXTEND')
            self.s.assert_and_track(ForAll([t], Implies(t > self._clock_r2,\
                    r2y(t) == self._curr_r2y)), 'R2Y EXTEND')

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
        ps.write_clock_frozen()
        ps.write_work_envelope(300, 300)
        for r_dict in dicts:
            ps.write_dest_pos(r_dict)
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
        set_option(rational_to_decimal=True)
        ps.write_work_envelope()
        ps.write_pos_initial()
        ps.write_arm_constraints()
        for stat in dicts:
            ps.write_pos_move_to(stat)
        ps.write_time_constraint()
        ps.write_extend_final_pos_to_end_time()
        try:
            # print(ps.assertions)
            result = ps.check()
            if result == unsat:
                print('UNSAT')
                # print(f'Minimal unsatisfiable core: {ps.unsat_core}')
                return {}
            print('SAT')
            return ps.model()[ps.t]
            # return ps.model()
        except Exception as e:
            print(f'Error during solving: {e}')
            return {}

if __name__ == '__main__':
    # print("Testing binning on unsafe program.")
    # print(TestUtil.bin_test(prog_unsafe_r1_collide))
    print("Running on safe program.")
    print(TestUtil.run_on_prog(prog_safe_r1_set))
    print("Running on unsafe program.")
    print(TestUtil.run_on_prog(prog_unsafe_r1_collide))
    print("Running on longer safe program.")
    print(TestUtil.run_on_prog(prog_safe_longer))
    print("Running on longer unsafe program.")
    print(TestUtil.run_on_prog(prog_unsafe_longer))
    print("Running on bad cross program.")
    print(TestUtil.run_on_prog(prog_unsafe_cross))

