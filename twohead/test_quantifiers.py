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
g_0_10 = ForAll([x], Implies(And(x >= 0, x < 10), g(x) == 6))
collision = f(x) == g(x)

s.add(f_0_5)
s.add(f_5_10)
s.add(g_0_10)
s.add(collision)

print('Running piecewise test.')
if s.check() == sat:
    print(s.model())
    print(f'Collision x-val: {s.model()[x]}')
else:
    print('No collision.')

# Now add t as third dimension, cross example with no arm constraint
s = Solver()
r1x = Function('r1x', RealSort(), RealSort())
r1y = Function('r1y', RealSort(), RealSort())
r2x = Function('r2x', RealSort(), RealSort())
r2y = Function('r2y', RealSort(), RealSort())

s.add(And(x >= 0, x <= 10))
s.add(And(y >= 0, y <= 10))
s.add(And(t >= 0, t <= 10))

s.add(Implies(t == 0, r1x(t) == 0))
s.add(Implies(t == 0, r1y(t) == 0))
s.add(Implies(t == 0, r2x(t) == 10))
s.add(Implies(t == 0, r2y(t) == 0))

s.add(ForAll([t], Implies(And(t > 0, t <= 10), r1x(t) == t)))
s.add(ForAll([t], Implies(And(t > 0, t <= 10), r1y(t) == t)))
s.add(ForAll([t], Implies(And(t > 0, t <= 10), r2x(t) == t)))
s.add(ForAll([t], Implies(And(t > 0, t <= 10), r2y(t) == -t + 10)))

collision = And(r1x(t) == r2x(t), r1y(t) == r2y(t))
s.add(collision)

print('Running cross test.')
if s.check() == sat:
    print(s.model())
    print(f'Collision t-val: {s.model()[t]}')
else:
    print('No collision.')
