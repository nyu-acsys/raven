from z3 import *

# class HeapChunk:
#     def __init__(self, nm):
#         self.name        = nm
#         self.size        = Int(nm + '_size')
#         self.initialized = Bool(nm + '_initialized')

#     def __str__(self):
#         return "<Name: %s, Size: %s, Initialized: %s>" % (self.name, self.size, self.initialized)

# # Helper function to grab a variable from a z3 model
# def getVar(m, v):
#     var             = HeapChunk(v.name)
#     var.size        = m[v.size]
#     var.initialized = m[v.initialized]
#     return var

# # Declare a few vars
# myVar1 = HeapChunk('myVar1')
# myVar2 = HeapChunk('myVar2')

# # Add some constraints
# s = Solver()

# s.add(myVar1.size == 12)
# s.add(myVar2.initialized == True);
# s.add(myVar1.size > myVar2.size)
# s.add(myVar1.initialized == Not(myVar2.initialized))

# # Get a satisfying model
# if s.check() == sat:
#     m = s.model()
#     print(getVar(m, myVar1))
#     print(getVar(m, myVar2))


# heap = EmptySet(HeapChunk)

def convertor(f, status="unknown", name="benchmark", logic=""):
    v = (Ast * 0)()
    if isinstance(f, Solver):
        a = f.assertions()
    if len(a) == 0:
        f = BoolVal(True)
    else:
        f = And(*a)
    return Z3_benchmark_to_smtlib_string(f.ctx_ref(), name, logic, status, "", 0, v, f.as_ast())




HeapChunk = Datatype('HeapChunk')
LocSort = DeclareSort('LocSort')

HeapChunk.declare('chunk', ('index', IntSort()), ('loc', LocSort), ('own', RealSort()))
HeapChunk = HeapChunk.create()

l1 = Const('l1', LocSort)

hc1 = HeapChunk.chunk(0, l1, Q(3, 4))
heap = EmptySet(HeapChunk)

heap = SetAdd(heap, hc1)
l2 = Const('l2', LocSort)
heap = SetAdd(heap, HeapChunk.chunk(1, l2, Q(3,4)))

s = Solver()


i1 = Int('i1')
i2 = Int('i2')
ll_1 = Const('ll_1', LocSort)
ll_2 = Const('ll_2', LocSort)
own_val1 = Real('o1')
own_val2 = Real('o2')


s.add(
    ForAll([i1, i2, ll_1, ll_2, own_val1, own_val2],
        Implies (And (IsMember(HeapChunk.chunk(i1, ll_1, own_val1), heap), IsMember(HeapChunk.chunk(i2, ll_2, own_val2), heap), own_val1 + own_val2 > 1, i1 != i2), ll_1 != ll_2)
    )
)

s.add(IsMember(HeapChunk.chunk(i1, ll_1, own_val1), heap),
    IsMember(HeapChunk.chunk(i2, ll_2, own_val2), heap),
    ll_1 == ll_2,
    i1 != i2,
    )

print(s.check())

# print (convertor(s, logic="AUFLIRA"))


# x = Int('x')
# y = Int('y')
# solve(x > 2, y < 10, x + 2*y == 7)

# x = Int('x')
# y = Int('y')
# print (simplify(x + y + 2*x + 3))
# print (simplify(x < y + x + 2))
# print (simplify(And(x + 1 >= 3, x**2 + x**2 + y**2 + 2 >= 5)))

# x = Int('x')
# y = Int('y')
# n = x + y >= 3
# print ("num args: ", n.num_args())
# print ("children: ", n.children())
# print ("1st child:", n.arg(0))
# print ("2nd child:", n.arg(1))
# print ("operator: ", n.decl())
# print ("op name:  ", n.decl().name())

# x = Real('x')
# y = Real('y')
# solve(x**2 + y**2 > 3, x**3 + y < 5)


# x = Real('x')
# y = Real('y')
# solve(x**2 + y**2 == 3, x**3 == 2)

# set_option(precision=30)
# # print "Solving, and displaying result with 30 decimal places"
# solve(x**2 + y**2 == 3, x**3 == 2)

# x = Real('x')
# solve(x**3 == 5)


# x = Real('x')
# y = Real('y')
# s = Solver()
# s.add(x > 1, y > 1, Or(x + y > 3, x - y < 2))
# print( "asserted constraints...")
# for c in s.assertions():
#     print (c)

# print( s.check())
# print ("statistics for the last check method...")
# print (s.statistics())
# # Traversing statistics
# for k, v in s.statistics():
#     print ("%s : %s" % (k, v))


# x, y, z = Reals('x y z')
# s = Solver()
# s.add(x > 1, y > 1, x + y > 3, z - x < 10)
# print (s.check())

# m = s.model()
# print( "x = %s" % m[x])

# print( "traversing model...")
# for d in m.decls():
#     print ("%s = %s" % (d.name(), m[d]))