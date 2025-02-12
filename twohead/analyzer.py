from z3 import *
from math import *
from functools import reduce
from example_progs import *

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
        instr = LangUtil.peek_instr_text(statement)
        if instr == 'moveTo' or instr == 'travel':
            return LangUtil.parse_move_to(statement)
        if instr == 'sleep':
            return LangUtil.parse_sleep(statement)
        else:
            print(f'Unrecognized instruction: {instr}')
            return {}

    @staticmethod
    def peek_instr_text(statement):
        return statement.split('(')[0]

    @staticmethod
    def parse_move_to(statement):
        arg_lst = statement.replace('(', ',')\
                           .replace(')', ',')\
                           .split(',')[0:5]
        return { 'instr': arg_lst[0],\
                 'x': int(arg_lst[1]),\
                 'y': int(arg_lst[2]),\
                 'z': int(arg_lst[3]),\
                 'r': int(arg_lst[4]),\
                 'statement': statement\
        }

    @staticmethod
    def parse_sleep(statement):
        arg_lst = statement.replace('(', ',')\
                           .replace(')', ',')\
                           .split(',')[0:3]
        return { 'instr': arg_lst[0],\
                 's': int(arg_lst[1]),\
                 'r': int(arg_lst[2]),\
                 'statement': statement\
        }

    @staticmethod
    def statements_to_dicts(statements):
        return list(map(LangUtil.stat_to_arg_dict, statements))

    @staticmethod
    def update_dict_statement(d):
        if d['instr'] == 'moveTo' or d['instr'] == 'travel':
            d['statement'] = f'{d["instr"]}({d["x"]}, {d["y"]}, 0, {d["r"]})'
        if d['instr'] == 'sleep':
            d['statement'] = f'{d["instr"]}({d["s"]}, {d["r"]})'
        return d

    @staticmethod
    def dicts_to_text(dicts):
        stats = [d['statement'] for d in dicts]
        return reduce(lambda s0, s1: s0 + ';\n' + s1, stats)

    @staticmethod
    def bin_stat_dicts_by_r(dicts):
        return [list(filter(lambda d: d['r'] == 1, dicts)),\
                list(filter(lambda d: d['r'] == 2, dicts))]

    @staticmethod
    def dicts_to_points(dicts):
        def slope(pt0, pt1):
            denom = (pt1[0] - pt0[0])
            if denom == 0:
                return inf
            return (pt1[1] - pt0[1]) / denom
        def same_pt(pt0, pt1):
            return pt0[0] == pt1[0] and pt0[1] == pt1[1]
        def merge_points(pts):
            # TODO: split between arms?
            mp_indices = []
            i = 0
            while i <= len(pts) - 3:
                start_pt = pts[i]
                maybe_mid_pt = pts[i + 1]
                end_pt = pts[i + 2]
                m0 = slope(start_pt, maybe_mid_pt)
                m1 = slope(maybe_mid_pt, end_pt)
                if m0 == m1 or same_pt(start_pt, maybe_mid_pt):
                    mp_indices.append(i + 1)
                i += 1
            new_pts = []
            while i <= len(pts) - 1:
                if i not in mp_indices:
                    new_pts.append(pts[i])
                i += 1
            return new_pts

        paths = []
        curr_path = []
        if dicts[0]['instr'] == 'sleep':
            # TODO: does this matter?
            last_move_pos = (0, 0)
        else:
            last_move_pos = (dicts[0]['x'], dicts[0]['y'])
        for i in range(0, len(dicts)):
            prev_dict = dicts[i - 1] if i > 0 else { 'instr': 'noop' }
            curr_dict = dicts[i]
            if curr_dict['instr'] == 'moveTo':
                curr_move_pos = (curr_dict['x'], curr_dict['y'])
                # NOTE: If we did some travels, check to make sure that the
                # last travel, i.e. where this moveTo starts from, is at the
                # same point as the last moveTo point. If not, the last moveTo
                # point is the end of the last path, and we start a new path
                # starting with the travel point, and the newest moveTo point.
                if prev_dict['instr'] == 'travel':
                    last_travel_pt = (prev_dict['x'], prev_dict['y'])
                    if not same_pt(last_move_pos, last_travel_pt):
                        paths.append(curr_path)
                        curr_path = [last_travel_pt, curr_move_pos]
                    else:
                        curr_path.append(curr_move_pos)
                else:
                    curr_path.append(curr_move_pos)
                last_move_pos = curr_move_pos
        paths.append(curr_path)
        paths = map(merge_points, paths)
        pts = reduce(lambda path0, path1: path0 + path1, paths)
        return sorted(pts, key=lambda xy: [xy[0], xy[1]])

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
        # Fields for collision solving
        self.MAX_COLLISIONS = 10
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
        # Fields for equivalence solving
        self.n1 = Int('n1')
        self.n2 = Int('n2')
        self.p1x = Function('p1x', IntSort(), RealSort())
        self.p1y = Function('p1y', IntSort(), RealSort())
        self.p2x = Function('p2x', IntSort(), RealSort())
        self.p2y = Function('p2y', IntSort(), RealSort())

    # Constraints for collision problem
    def set_work_envelope_setting(self, tup):
        self.X_LIM = tup[0]
        self.Y_LIM = tup[1]

    def set_init_pos_setting(self, tup_r1, tup_r2):
        self.R1_INIT_X = tup_r1[0]
        self.R1_INIT_Y = tup_r1[1]
        self.R2_INIT_X = tup_r2[0]
        self.R2_INIT_Y = tup_r2[1]

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
                r2y(t) >= r1y(t) - w,\
                r2y(t) <= r1y(t) + w),
            And(r1x(t) >= r2x(t),\
                r1y(t) >= r2y(t) - w,\
                r1y(t) <= r2y(t) + w)),\
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
                f'POS_X: R{stat_dict["r"]} {x_old} -> {x_new} @ t={t_old}')
        self.s.assert_and_track(ForAll([t],\
            Implies(And(t > t_old, t <= t_new),\
                y(t) == (1 - (t - t_old) / time_taken) * y_old\
                    + ((t - t_old) / time_taken) * y_new)),\
                f'POS_Y: R{stat_dict["r"]} {y_old} -> {y_new} @ t={t_old}')

        # Update (x, y, t)
        if stat_dict['r'] == 1:
            self._curr_r1x = stat_dict['x']
            self._curr_r1y = stat_dict['y']
            self._clock_r1 += time_taken
        else:
            self._curr_r2x = stat_dict['x']
            self._curr_r2y = stat_dict['y']
            self._clock_r2 += time_taken

    def write_sleep(self, stat_dict):
        if stat_dict['r'] == 1:
            x_curr = self._curr_r1x
            y_curr = self._curr_r1y
            t_curr = self._clock_r1
            x = self.r1x
            y = self.r1y
        else:
            x_curr = self._curr_r2x
            y_curr = self._curr_r2y
            t_curr = self._clock_r2
            x = self.r2x
            y = self.r2y
        t = self.t
        new_t = t_curr + stat_dict['s']
        self.s.assert_and_track(ForAll([t], Implies(And(t > t_curr, t <= new_t),\
            x(t) == x_curr)), f'SLEEP R{stat_dict["r"]}X: ({t_curr}, {new_t}]')
        self.s.assert_and_track(ForAll([t], Implies(And(t > t_curr, t <= new_t),\
            y(t) == y_curr)), f'SLEEP R{stat_dict["r"]}Y: ({t_curr}, {new_t}]')

        if stat_dict['r'] == 1:
            self._clock_r1 += stat_dict['s']
        else:
            self._clock_r2 += stat_dict['s']

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

    # Constraints for equivalence problem
    def write_indices_constraints(self, dicts, p_idx):
        '''
        NB: we add initial positions later, so upper bound is |dicts|.
        '''
        num_dicts = len(dicts)
        if p_idx == 1:
            self.s.assert_and_track(And(self.n1 >= 0, self.n1 <= num_dicts),\
                                    f'N1 BOUND')
        else:
            self.s.assert_and_track(And(self.n2 >= 0, self.n2 <= num_dicts),\
                                    f'N2 BOUND')

    def write_all_index_positions(self, dicts, p_idx):
        # TODO: handle sleep, travel
        bins = LangUtil.bin_stat_dicts_by_r(dicts)
        r1_dicts = bins[0]
        r2_dicts = bins[1]
        # r1_dicts.insert(LangUtil.parse_move_to(\
        #         f'moveTo({self.R1_INIT_X}, {self.R1_INIT_Y}, 0, 1)'))
        # r2_dicts.insert(LangUtil.parse_move_to(\
        #         f'moveTo({self.R2_INIT_X}, {self.R2_INIT_Y}, 0, 2)'))
        dicts_ser = r1_dicts + r2_dicts
        curr_n = 0
        p1x = self.p1x
        p1y = self.p1y
        p2x = self.p2x
        p2y = self.p2y
        n1 = self.n1
        n2 = self.n2
        if p_idx == 1:
            for i in range(0, len(dicts_ser)):
                # Will probably need to look backwards for travels, but not now
                # prev_x = dicts_ser[i - 1]['x']
                # prev_y = dicts_ser[i - 1]['y']
                curr_x = dicts_ser[i]['x']
                curr_y = dicts_ser[i]['y']
                self.s.add(Implies(n1 == curr_n, p1x(n1) == curr_x))
                self.s.add(Implies(n1 == curr_n, p1y(n1) == curr_y))
        else:
            for i in range(0, len(dicts_ser)):
                curr_x = dicts_ser[i]['x']
                curr_y = dicts_ser[i]['y']
                self.s.add(Implies(n2 == curr_n, p2x(n2) == curr_x))
                self.s.add(Implies(n2 == curr_n, p2y(n2) == curr_y))

    def write_equiv_constraint(self):
        n1 = self.n1
        n2 = self.n2
        p1x = self.p1x
        p1y = self.p1y
        p2x = self.p2x
        p2y = self.p2y
        self.s.assert_and_track(ForAll([n1], Exists(n2,\
                And(p1x(n1) == p2x(n2), p1y(n1) == p2y(n2)))),\
                f'EQUIV CONSTRAINT N1')
        self.s.assert_and_track(ForAll([n2], Exists(n1,\
                And(p2x(n2) == p1x(n1), p2y(n2) == p1y(n1)))),\
                f'EQUIV CONSTRAINT N2')

    # Getters and miscellaneous
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

class Analyzer():
    def __init__(self, work_envelope, init_pos_r1, init_pos_r2):
        """
        work_envelope - (x_max, y_max)
        init_pos_r1 - (x, y)
        init_pos_r2 - (x, y)
        """
        self.work_envelope = work_envelope
        self.init_pos_r1 = init_pos_r1
        self.init_pos_r2 = init_pos_r2
        self.X_LIM = work_envelope[0]
        self.Y_LIM = work_envelope[1]

    # TODO: interactively block out collision points to check num of collisions
    def check_collision(self, prog):
        """
        Returns False if no collision, otherwise the (x, y, t) of collision
        """
        stats = LangUtil.prog_text_to_statements(prog)
        dicts = LangUtil.statements_to_dicts(stats)
        ps = ProgSolver()
        ps.set_work_envelope_setting(self.work_envelope)
        ps.set_init_pos_setting(self.init_pos_r1, self.init_pos_r2)
        set_option(rational_to_decimal=True)
        ps.write_work_envelope()
        ps.write_pos_initial()
        ps.write_arm_constraints()
        for stat in dicts:
            if stat['instr'] == 'moveTo' or stat['instr'] == 'travel':
                ps.write_pos_move_to(stat)
            elif stat['instr'] == 'sleep':
                ps.write_sleep(stat)
        ps.write_time_constraint()
        ps.write_extend_final_pos_to_end_time()
        collisions = 0
        for _ in range(0, ps.MAX_COLLISIONS):
            try:
                result = ps.check()
                if result == unsat:
                    return collisions
                collisions += 1
                ps.s.add(Or(ps.t <= ps.model()[ps.t] - ps.ROBOT_ARM_WIDTH,\
                            ps.t >= ps.model()[ps.t] + ps.ROBOT_ARM_WIDTH))
            except Exception as e:
                print(f'Error during solving: {e}')
                return False
        return collisions

    def check_equivalent_nosmt(self, prog_target, prog_rewrite):
        stats_t = LangUtil.prog_text_to_statements(prog_target)
        stats_r = LangUtil.prog_text_to_statements(prog_rewrite)
        dicts_t = LangUtil.statements_to_dicts(stats_t)
        dicts_r = LangUtil.statements_to_dicts(stats_r)
        pts_t = LangUtil.dicts_to_points(dicts_t)
        pts_r = LangUtil.dicts_to_points(dicts_r)
        score = 0
        if len(pts_t) == 0 or len(pts_r) == 0:
            return inf
        if pts_t != pts_r:
            if len(pts_t) > len(pts_r):
                last_pt = pts_r[len(pts_r) - 1]
                len_diff = len(pts_t) - len(pts_r)
                pts_r += [last_pt for _ in range(0, len_diff + 1)]
            elif len(pts_t) < len(pts_r):
                last_pt = pts_t[len(pts_t) - 1]
                len_diff = len(pts_r) - len(pts_t)
                pts_t += [last_pt for _ in range(0, len_diff + 1)]
            pt_pairs = list(zip(pts_t, pts_r))
            distances = list(map(lambda pt_pair: self.dist(pt_pair[0],\
                                    pt_pair[1]), pt_pairs))
            score = reduce(lambda a, b: a + b, distances)
        return score

    def check_equivalent(self, prog_target, prog_rewrite):
        prog_texts = (prog_target, prog_rewrite)
        ps = ProgSolver()
        for p in range(0, 2):
            stats = LangUtil.prog_text_to_statements(prog_texts[p])
            print(stats)
            dicts = LangUtil.statements_to_dicts(stats)
            ps.write_indices_constraints(dicts, p)
            ps.write_all_index_positions(dicts, p)
        ps.write_equiv_constraint()
        print(ps.assertions)
        try:
            result = ps.check()
            return result != unsat
        except Exception as e:
            print(f'Error during solving: {e}')
            return False

    def find_running_time(self, prog):
        stats = LangUtil.prog_text_to_statements(prog)
        dicts = LangUtil.statements_to_dicts(stats)
        r1_stats, r2_stats = LangUtil.bin_stat_dicts_by_r(dicts)
        r1_stats = list(filter(lambda d: d['instr'] == 'moveTo'
                            or d['instr'] == 'travel', r1_stats))
        r2_stats = list(filter(lambda d: d['instr'] == 'moveTo'
                            or d['instr'] == 'travel', r2_stats))
        r1_time = self.dist(self.init_pos_r1, (r1_stats[0]['x'], r1_stats[0]['y']))\
                    if len(r1_stats) > 0 else 0
        r2_time = self.dist(self.init_pos_r2, (r2_stats[0]['x'], r2_stats[0]['y']))\
                    if len(r2_stats) > 0 else 0
        for i in range(0, len(r1_stats) - 1):
            p0 = (r1_stats[i]['x'], r1_stats[i]['y'])
            p1 = (r1_stats[i + 1]['x'], r1_stats[i + 1]['y'])
            r1_time += self.dist(p0, p1)
        for i in range(0, len(r2_stats) - 1):
            p0 = (r2_stats[i]['x'], r2_stats[i]['y'])
            p1 = (r2_stats[i + 1]['x'], r2_stats[i + 1]['y'])
            r2_time += self.dist(p0, p1)
        return max(r1_time, r2_time)

    def dist(self, p0, p1):
        return sqrt((p0[0] - p1[0]) ** 2 + (p0[1] - p1[1]) ** 2)

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
            if stat['instr'] == 'moveTo':
                ps.write_pos_move_to(stat)
            elif stat['instr'] == 'sleep':
                ps.write_sleep(stat)
        ps.write_time_constraint()
        ps.write_extend_final_pos_to_end_time()
        # test_time = sqrt(150**2 + 150**2)
        # ps.s.add(Real('r1xTEST') == ps.r1x(test_time))
        # ps.s.add(Real('r1yTEST') == ps.r1y(test_time))
        # ps.s.add(Real('r2xTEST') == ps.r2x(test_time))
        # ps.s.add(Real('r2yTEST') == ps.r2y(test_time))
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

    @staticmethod
    def test_equiv(prog_t, prog_r):
        analyzer = Analyzer((300, 300), (0, 0), (300, 0))
        # return analyzer.check_equivalent(prog_t, prog_t)
        return analyzer.check_equivalent_nosmt(prog_t, prog_r)

    @staticmethod
    def count_collisions(prog):
        analyzer = Analyzer((300, 300), (0, 0), (300, 0))
        return analyzer.check_collision(prog)

if __name__ == '__main__':
    # print("Testing binning on unsafe program.")
    # print(TestUtil.bin_test(prog_unsafe_r1_collide))
    # print("Running on safe program.")
    # print(TestUtil.run_on_prog(prog_safe_r1_set))
    print("Running on unsafe program.")
    print(TestUtil.run_on_prog(prog_unsafe_r1_collide))
    print("Running on unsafe program using check_collision.")
    print(TestUtil.count_collisions(prog_unsafe_r1_collide))
    # print("Running on longer safe program.")
    # print(TestUtil.run_on_prog(prog_safe_longer))
    # print("Running on longer unsafe program.")
    # print(TestUtil.run_on_prog(prog_unsafe_longer))
    # print("Running on bad cross program.")
    # print(TestUtil.run_on_prog(prog_unsafe_cross))
    # print("Running on safe program with sleep.")
    # print(TestUtil.run_on_prog(prog_safe_sleep_before_collide))
    # print("Running on unsafe program with sleep.")
    # print(TestUtil.run_on_prog(prog_unsafe_not_enough_sleep_before_collide))
    # print("Running on safe but slow prog.")
    # print(TestUtil.run_on_prog(prog_safe_easy_optimize))
    # print("Testing equivalence with safe prog on itself.")
    # print(TestUtil.test_equiv(prog_safe_r1_set, prog_safe_r1_set))
    # print("Testing equivalence with safe prog on reverse version")
    # print(TestUtil.test_equiv(prog_safe_r1_set, prog_safe_r1_set_rev))
    # print("Testing equivalence with safe prog and non-equiv unsafe")
    # print(TestUtil.test_equiv(prog_safe_r1_set, prog_safe_longer))
    # print("Testing equivalence with easy to optimize prog with optimized")
    # print(TestUtil.test_equiv(prog_safe_easy_optimize, prog_safe_easy_post_opt))
    # print("Testing equivalence with segmented vs. merged")
    # print(TestUtil.test_equiv(prog_segmented, prog_merged))
    # print("Testing equivalence with wrong segmented vs. merged")
    # print(TestUtil.test_equiv(prog_segmented_wrong, prog_merged))

