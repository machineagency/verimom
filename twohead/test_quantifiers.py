from z3 import *

# Test piecewise intersection
# f - unit slope triangle wave with peak at 5
# g - zero slope line

s = Solver()

t = Real('t')
x = Real('x')
y = Real('y')

f = Function('f', RealSort(), RealSort())
g = Function('g', RealSort(), RealSort())

s.add(And(x >= 0, x < 10))
s.add(And(y >= 0, y < 10))

f_0_5 = ForAll([x], Implies(And(x >= 0, x < 5), f(x) == x))
f_5_10 = ForAll([x], Implies(And(x >= 5, x < 10), f(x) == -x + 10))
g_0_10 = ForAll([x], Implies(And(x >= 0, x < 10), g(x) == 5))
collision = f(x) == g(x)

s.add(f_0_5)
s.add(f_5_10)
s.add(g_0_10)
s.add(collision)

if s.check() == sat:
    print(s.model())
    print(f'Collision x-val: {s.model()[x]}')
else:
    print('unsat')

