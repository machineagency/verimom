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

