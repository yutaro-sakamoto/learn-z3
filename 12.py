from z3 import *
def is_power_of_two(x):
    return And(x != 0, 0 == (x & (x - 1)))
x = BitVec('x', 4)
prove(is_power_of_two(x) == Or([x == 2**i for i in range(4)]))

v = BitVec('v', 32)
mask = v >> 31
prove(If(v > 0, v, -v) == (v + mask) ^ mask)

x = FP('x', FPSort(3, 4))
print(10 + x)

Z = IntSort()
Tree = Datatype('Tree')
Tree.declare('Empty')
Tree.declare('Node', ('left', Tree), ('data', Z), ('right', Tree))
Tree = Tree.create()
t = Const('t', Tree)
solve(t != Tree.Empty)
prove(t != Tree.Node(t, 0, t))

s, t, u = Strings('s t u')
prove(Implies(And(PrefixOf(s, t), SuffixOf(u, t), Length(t) == Length(s) + Length(u)),
    t == Concat(s, u)))

s, t = Consts('s t', SeqSort(IntSort()))
solve(Concat(s, Unit(IntVal(2))) == Concat(Unit(IntVal(1)), t))
solve(Concat(s, Unit(IntVal(2))) == Concat(Unit(IntVal(1)), s))

s = Solver()
A  = DeclareSort('A')
B = BoolSort()
R = Function('R', A, A, B)
x, y, z = Consts('x, y z', A)
s.add(ForAll([x], R(x, x)))
s.add(ForAll([x, y], Implies(And(R(x, y), R(y, x)), x == y)))
s.add(ForAll([x, y, z], Implies(And(R(x, y), R(y, z)), R(x, z))))

s = Solver()
A  = DeclareSort('A')
B = BoolSort()
R = Function('R', A, A, B)
x, y, z = Consts('x, y z', A)
s.add(ForAll([x], R(x, x)))
s.add(ForAll([x, y], Implies(And(R(x, y), R(y, x)), x == y)))
s.add(ForAll([x, y, z], Implies(And(R(x, y), R(y, z)), R(x, z))))
s.add(ForAll([x, y, z], Implies(And(R(x, y), R(y, z)), Or(R(y, z), R(z, y)))))

R = Function('R', A, A, B)
TC_R = TransitiveClosure(R)
s = Solver()
a, b, c = Consts('a b c', A)
s.add(R(a, c))
s.add(R(b, c))
s.add(Not(TC_R(a, c)))
print(s.check())

p, q, r = Bools('p q r')
s = Solver()
s.add(Implies(p, q))
s.add(Not(q))
print(s.check())
s.push()
s.add(p)
print(s.check())
s.pop()
print(s.check())

p, q = Bools('p q')
s = Solver()
s.add(Not(q))
s.assert_and_track(q, p)
print(s.check())

p, q, r, v = Bools('p q r v')
s = Solver()
s.add(Not(q))
s.assert_and_track(q, p)
s.assert_and_track(r, v)
print(s.check())
print(s.unsat_core())

s = Solver()
f = Function('f', Z, Z)
x, y = Ints('x y')
s.add(f(x) > y, f(f(y)) == y)
print(s.check())
print(s.model())

m = s.model()
for d in m:
    print(d, m[d])

num_entries = m[f].num_entries()
for i in range(num_entries):
    print(m[f].entry(i))
print("else", m[f].else_value())

print(m.eval(x), m.eval(f(3)), m.eval(f(4)))