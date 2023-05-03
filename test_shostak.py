import z3
from euf_shostak import euf_solver_shostak
from euf_shostak import euf_dpllt_solver

# def euf_solver_shostak(flist):
#     ss = z3.Solver()
#     ss.add( z3.And(flist))
#     return ss.check()
#
# def euf_dpllt_solver(formula):
#     ss = z3.Solver()
#     ss.add( formula )
#     return ss.check()

# def euf_solver_shostak(flist):
#     ss = z3.Solver()
#     ss.add( z3.And(flist))
#     return ss.check()
#
# def euf_dpllt_solver(formula):
#     ss = z3.Solver()
#     ss.add( formula )
#     return ss.check()

# def euf_solver_shostak(euf_formula_list):
# def euf_dpllt_solver(general_euf_formula)

################################################################################

x1 = z3.Real('x1')
x2 = z3.Real('x2')
x3 = z3.Real('x3')
x4 = z3.Real('x4')
x5 = z3.Real('x5')
y1 = z3.Real('y1')
y2 = z3.Real('y2')
y3 = z3.Real('y3')
y4 = z3.Real('y4')
y5 = z3.Real('y5')

vx1 = z3.Real('varx1')
vx2 = z3.Real('varx2')
vx3 = z3.Real('varx3')
vx4 = z3.Real('varx4')
vx5 = z3.Real('varx5')
vy1 = z3.Real('vary1')
vy2 = z3.Real('vary2')
vy3 = z3.Real('vary3')
vy4 = z3.Real('vary4')
vy5 = z3.Real('vary5')
x4 = z3.Real('x4')
x5 = z3.Real('x5')
y1 = z3.Real('y1')
y2 = z3.Real('y2')
y3 = z3.Real('y3')
y4 = z3.Real('y4')
y5 = z3.Real('y5')

vx1 = z3.Real('varx1')
vx2 = z3.Real('varx2')
vx3 = z3.Real('varx3')
vx4 = z3.Real('varx4')
vx5 = z3.Real('varx5')
vy1 = z3.Real('vary1')
vy2 = z3.Real('vary2')
vy3 = z3.Real('vary3')
vy4 = z3.Real('vary4')
vy5 = z3.Real('vary5')


R = z3.RealSort()
f1 = z3.Function("f1", R, R)         # R ->
f2 = z3.Function("f2", R, R)
f3 = z3.Function("f3", R, R)
g1 = z3.Function("g1", R, R, R)     # (R,R) -> R
g2 = z3.Function("g2", R, R, R)
g3 = z3.Function("g3", R, R, R)
h1 = z3.Function("h1", R, R, R, R)     # (R,R,R) -> R
h2 = z3.Function("h2", R, R, R, R)
h3 = z3.Function("h3", R, R, R, R)

hh1 = z3.Function("h3", R, R, R, R, R)
hh2 = z3.Function("h3", R, R, R, R, R)

hhh1 = z3.Function("h3", R, R, R, R, R, R)
hhh2 = z3.Function("h3", R, R, R, R, R, R)

# formula1 = z3.And(x1 == x2, x2 == x3, x1 != x3)
# formula2 = z3.Or(x1 == x2, x2 == x3, x1 == x3)

################################################################################
def test_shostak_tc4():       ## new
    euf_elist = [
            x1 == y1,
            x2 == y2,
            g1(x1,x2) == g2(y1, y2),
            ]
    assert euf_solver_shostak(euf_elist)  == z3.sat

################################################################################
def test_shostak_tc5():       ## new
    euf_elist = [
            x1 == y1,
            x2 == y2,
            hh1(x1,x2,x3,x4) == hh2(y1,y2,y3,y4),
            ]
    assert euf_solver_shostak(euf_elist)  == z3.sat
################################################################################
def test_shostak_tc6():       ## new
    euf_elist = [
            x1 == y1,
            x2 == y2,
            hhh1(x1,x2,x3,x4,x5) != hhh2(y1,y2,y3,y4,y5),
            ]
    assert euf_solver_shostak(euf_elist)  == z3.sat

hh1 = z3.Function("h3", R, R, R, R, R)
hh2 = z3.Function("h3", R, R, R, R, R)

################################################################################
def test_shostak_tc4():       ## new
    euf_elist = [
            x1 == y1,
            x2 == y2,
            g1(x1,x2) == g2(y1, y2),
            ]
    assert euf_solver_shostak(euf_elist)  == z3.sat

################################################################################
def test_shostak_tc5():       ## new
    euf_elist = [
            x1 == y1,
            x2 == y2,
            hh1(x1,x2,x3,x4) == hh2(y1,y2,y3,y4),
            ]
    assert euf_solver_shostak(euf_elist)  == z3.sat
################################################################################
def test_shostak_tc6():       ## new
    euf_elist = [
            x1 == y1,
            x2 == y2,
            hhh1(x1,x2,x3,x4,x5) != hhh2(y1,y2,y3,y4,y5),
            ]
    assert euf_solver_shostak(euf_elist)  == z3.sat

################################################################################
def test_shostak_tc7():       ## new
    euf_elist = [
            x1 == y1,
            f1(x1) == f1(y1),
            f1(f1(x1)) == f1(f1(y1)),
            f1(f1(f1(x1))) == f1(f1(f1(y1))),
            f1(f1(f1(f1(x1)))) == f1(f1(f1(f1(y1)))),
            f1(f1(f1(f1(f1(x1))))) != f1(f1(f1(f1(f1(y1))))),
            ]
    assert euf_solver_shostak(euf_elist)  == z3.unsat

################################################################################
def test_shostak_tc8():       ## new
    euf_elist = [
            x1 == y1,
            y1 == x2,
            f1(x2) == g1(y1, x2),
            h1(x1, y1, x2) == f1(x1),
            h1(x1, y1, x2) == f1(x2),
            f1(y1) != g1(x2, x1),
            x1 == y1,
            y1 == x2,
            f1(x2) == g1(y1, x2),
            h1(x1, y1, x2) == f1(x1),
            h1(x1, y1, x2) == f1(x2),
            f1(y1) != g1(x2, x1),
            ]
    assert euf_solver_shostak(euf_elist)  == z3.unsat
    assert euf_solver_shostak(euf_elist)  == z3.unsat

################################################################################
def test_shostak_tc9():       ## new
    euf_elist = [
            x1 == 1,
            y1 == 1,
            x1 != y1,
            f1(x1) == f1(y1),
            x1 == 1,
            y1 == 1,
            x1 != y1,
            f1(x1) == f1(y1),
            ]
    assert euf_solver_shostak(euf_elist)  == z3.unsat
    assert euf_solver_shostak(euf_elist)  == z3.unsat

################################################################################
def test_shostak_tc10():       ## new
    euf_elist = [
            z3.Not(x1 != x2),
            z3.Not(x1 != x2),
            f1(x1) == f1(x2),
            ]
    assert euf_solver_shostak(euf_elist)  == z3.sat

################################################################################
def test_dpllt_tc3():
    euf_formula = z3.And( x1 == x2, x2 == x3, z3.Or(f1(x1) == f1(x2), x3 != x1))
    assert euf_dpllt_solver(euf_formula) == z3.sat

################################################################################
def test_dpllt_tc4():
    euf_formula = z3.And( x1 != f1(x1), x1 == f1(f1(f1(x1))), x1 == f1(f1(f1(f1(f1(f1(x1)))))))
    assert euf_dpllt_solver(euf_formula) == z3.sat

################################################################################
def test_dpllt_tc5():
    euf_formula = z3.Or(z3.And(f1(f2(x1)) == x1, f2(f1(f2(x1))) == x1, f2(f1(x1)) != x1), z3.And(f2(f1(x1)) == x1, f2(f2(f1(x1))) == x1, f2(x1) != f1(x1)))
    assert euf_dpllt_solver(euf_formula) == z3.sat

################################################################################
def test_dpllt_tc6():
    euf_formula = z3.Or(z3.And(g1(f2(x1), f3(x1)) == x1, f2(f1(f2(x1))) == x1, f2(f1(x1)) != x1), z3.And(f2(f1(x1)) == x1, f2(f2(f1(x1))) == x1, f2(x1) != f1(x1)))
    assert euf_dpllt_solver(euf_formula) == z3.sat

################################################################################
def test_dpllt_tc7():
    euf_formula = z3.Or(z3.Not(z3.And(g1(f2(x1), f3(x1)) == x1, f2(f1(f2(x1))) == x1, f2(f1(x1)) != x1), z3.And(f2(f1(x1)) == x1, f2(f2(f1(x1))) == x1, f2(x1)
        != f1(x1))))
    assert euf_dpllt_solver(euf_formula) == z3.sat

################################################################################
def test_dpllt_tc8():
    euf_formula = z3.Or(
                z3.Not(
                    z3.And(
                        g1(f2(1), f3(x1)) == x1),
                        x1 != 1
                    ),
                x1 != x2
                )
    assert euf_dpllt_solver(euf_formula) == z3.sat

################################################################################
def test_dpllt_tc9():
    euf_formula = z3.Or(
            hhh1(x1,x2,x3,x4,x5) != hhh2(y1,y2,y3,y4,y5),
            z3.Not(x1 != x2)
            )
def test_dpllt_tc9():
    euf_formula = z3.Or(
            hhh1(x1,x2,x3,x4,x5) != hhh2(y1,y2,y3,y4,y5),
            z3.Not(x1 != x2)
            )
    assert euf_dpllt_solver(euf_formula) == z3.sat

################################################################################
def test_dpllt_tc10():
    euf_formula = z3.And(
            hhh1(x1,x2,x3,x4,x5) != hhh2(y1,y2,y3,y4,y5),
            z3.Not(x1 != x2)
            )
    assert euf_dpllt_solver(euf_formula) == z3.sat
################################################################################