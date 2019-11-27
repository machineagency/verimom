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
        return { 'x': arg_lst[0],\
                 'y': arg_lst[1],\
                 'z': arg_lst[2],\
                 'r': arg_lst[3] }


class TestUtil():
    def __init__(self):
        pass

    @staticmethod
    def statement_0():
        stats = LangUtil.prog_text_to_statements(prog_safe_r1_set)
        stat_dicts = map(lambda stat: LangUtil.stat_to_arg_dict(stat), stats)
        return list(stat_dicts)

if __name__ == '__main__':
    print(TestUtil.statement_0())

