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

#p, q, r, v = Bools('p q r v')
#s = Solver()
#s.add(Not(q))
#s.assert_and_track(q, p)
#s.assert_and_track(r, v)
#print(s.check())
#print(s.unsat_core())
#
#s = Solver()
#s.set("produce-proofs", True)
#f = Function('f', Z, Z)
#x, y = Ints('x y')
#s.add(f(x) > y, f(f(y)) == y)
#print(s.check())
#print(s.model())

#m = s.model()
#for d in m:
#    print(d, m[d])
#
#num_entries = m[f].num_entries()
#for i in range(num_entries):
#    print(m[f].entry(i))
#print("else", m[f].else_value())
#
#print(m.eval(x), m.eval(f(3)), m.eval(f(4)))

#print(s.statistics())
#
#print(s.proof())

a, b, c, d = Bools('a b c d')
s = Solver()
s.add(Implies(a, b), Implies(c, d))
print(s.consequences([a, c], [b, c, d]))

s = SolverFor("QF_FD")
#s.add(F)

def block_model(s):
    m = s.model()
    s.add(Or([f() != m[f]]))

def simple_cdclT(clauses):
    prop = Solver()
    theory = Solver()
    abs = {}
    prop.add(abstract_clauses(abs, clauses))
    theory.add([p == abs[p] for p in abs])
    while True:
        is_sat = prop.check()
        if sat == is_sat:
            m = prop.model()
            lits = [mk_lit(m, abs[p]) for p in abs]
            if unsat == theory.check(lits):
                prop.add(Not(And(tehory.unsat_core())))
            else:
                print(theory.model())
                return
        else:
            print(is_sat)
            return

index = 0

def abstract_atom(abs, atom):
    global index
    if atom in abs:
        return abs[atom]
    p = Bool('p_%d' % index)
    index += 1
    abs[atom] = p
    return p

def abstract_lit(abs, lit):
    if is_not(lit):
        return Not(abstract_atom(abs, lit.arg(0)))
    return abstract_atom(abs, lit)

def abstract_clause(abs, clause):
    return Or([abstract_lit(abs, lit) for lit in clause])

def abstract_clause(abs, clauses):
    return [abstract_clause(abs, clause) for clause in clauses]

def mk_lit(m, p):
    if is_true(m.eval(p)):
        return p
    else:
        return Not(p)

print(tactics())

for name in tactics():
    t = Tactic(name)
    print(name, t.help(), t.param_descrs())

x, y = Reals('x y')
g = Goal()
g.add(2 < x, Exists(y, And(y > 0, x == y + 2)))
print(g)

t1 = Tactic('qe-light')
t2 = Tactic('simplify')
t = Then(t1, t2)
print(t(g))

o = Optimize()
x, y = Ints('x y')
o.maximize(x + 2 * y)

u, v = BitVecs('u v', 32)
o.minimize(u + v)

o.add_soft(x > 4, 4)

x, y = Ints('x y')
opt = Optimize()
opt.set(priority='pareto')
opt.add(x + y == 10, x >= 0, y >= 0)
mx = opt.maximize(x)
my = opt.maximize(y)
while opt.check() == sat:
    print (mx.value(), my.value())

a, b, c = Bools('a b c')
o = Optimize()
o.add(a == c)
o.add(Not(And(a, b)))
o.add_soft(a, 2)
o.add_soft(b, 3)
o.add_soft(c, 1)
print(o.check())
print(o.model())


a, b, c = Bools('a b c')
o = Optimize()
o.add(a == c)
o.add(Not(And(a, b)))
o.add_soft(Or(a, b), 2)
o.add_soft(b, 3)
o.add_soft(c, 1)
print(o.check())
print(o.model())