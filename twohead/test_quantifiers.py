from z3 import *
from math import *

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

# Try r1 running into r2, with arm constraint
s = Solver()
r1x = Function('r1x', RealSort(), RealSort())
r1y = Function('r1y', RealSort(), RealSort())
r2x = Function('r2x', RealSort(), RealSort())
r2y = Function('r2y', RealSort(), RealSort())

s.add(And(r1x(t) >= 0, r1x(t) <= 10))
s.add(And(r2x(t) >= 0, r2x(t) <= 10))
s.add(And(r1y(t) >= 0, r1y(t) <= 10))
s.add(And(r2y(t) >= 0, r2y(t) <= 10))
s.add(And(t >= 0, t <= 10))

s.add(Implies(t == 0, r1x(t) == 0))
s.add(Implies(t == 0, r1y(t) == 0))
s.add(Implies(t == 0, r2x(t) == 10))
s.add(Implies(t == 0, r2y(t) == 0))

# R2 positions
s.add(ForAll([t], Implies(And(t > 0, t < 5 * sqrt(2)), r2x(t) == t)))
s.add(ForAll([t], Implies(And(t > 0, t < 5 * sqrt(2)), r2y(t) == -t + 10)))
s.add(ForAll([t], Implies(And(t >= 5 * sqrt(2)), r2x(t) == 5)))
s.add(ForAll([t], Implies(And(t >= 5 * sqrt(2)), r2y(t) == 5)))

# R1 positions
s.add(ForAll([t], Implies(And(t > 0, t < 5 * sqrt(2)), r1x(t) == (3/2) * t)))
s.add(ForAll([t], Implies(And(t > 0, t < 5 * sqrt(2)), r1y(t) == 0)))
s.add(ForAll([t], Implies(And(t >= 5 * sqrt(2)), r1x(t) == 15/2)))
s.add(ForAll([t], Implies(And(t >= 5 * sqrt(2)), r1y(t) == 2 * t - 10)))

s.push()
collision = And(r1x(t) == r2x(t), r1y(t) == r2y(t))
s.add(collision)

print('Running r1 crash without arm constraint, should pass.')
if s.check() == sat:
    print(s.model())
    print(f'Collision t-val: {s.model()[t]}')
else:
    print('No collision.')

# Arm constraints: when I, r1, move, r2 cannot have a pos in my bounds
# !! Remove exact position constraint first otherwise we have guaranteed unsat
s.pop()
w = 1
s.add(And(r2x(t) <= r1x(t),\
          r2y(t) >= r1y(t) - w / 2,\
          r2y(t) <= r1y(t) + w / 2))

print('Running r1 crash with arm constraints, should NOT pass.')
print(s.assertions())
if s.check() == sat:
    print(s.model())
    print(f'Collision t-val: {s.model()[t]}')
else:
    print('No collision.')

