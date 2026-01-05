from z3 import *
A = Array('A', IntSort(), IntSort())
x = Int('x')
y = Int('y')
solve(A[x] == x, Store(A, x, y) == A)