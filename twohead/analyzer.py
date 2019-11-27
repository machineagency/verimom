example_prog = """moveTo(150, 100, 0, 1);
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

class TestUtil():
    def __init__(self):
        pass

    @staticmethod
    def statement_0():
        return LangUtil.prog_text_to_statements(example_prog)

if __name__ == '__main__':
    print(TestUtil.statement_0())

