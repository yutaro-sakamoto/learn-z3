from z3 import *
Q = Array('Q', IntSort(), BoolSort())
x = Int('x')
y = Int('y')
prove(Implies(ForAll(Q, Implies(Select(Q, x), Select(Q, y))),
    x == y))