import z3
from utils import *
from z3.z3consts import *
from collections import deque


def seperate_eq_diseq(euf_formula):
    eq = []
    diseq = []
    for atom in euf_formula:
        rel_kind = atom.decl().kind()
        if rel_kind == Z3_OP_EQ:
            eq.append(atom)
        if rel_kind == Z3_OP_DISTINCT:
            diseq.append(atom)
    return (eq, diseq)


def check_congruent(a, b, eq_rep):
    if not a.decl() == b.decl() or not len(a.children()) == len(b.children()):
        return False
    for i in range(len(a.children())):
        if not eq_rep[a.children()[i]] == eq_rep[b.children()[i]]:
            return False
    return True


def merge(a, b, eq_sets, eq_rep, p_terms):
    if not eq_rep[a].eq(eq_rep[b]):
        pred_a = []
        pred_b = []
        for x in eq_sets[eq_rep[a]]:
            pred_a.extend(p_terms[x])

        for x in eq_sets[eq_rep[b]]:
            pred_b.extend(p_terms[x])

        eq_sets[eq_rep[a]] |= eq_sets[eq_rep[b]]

        for ele in eq_sets[eq_rep[b]]:
            eq_rep[ele] = eq_rep[a]

        for pa in pred_a:
            for pb in pred_b:
                if not eq_rep[pa].eq(eq_rep[pb]) and \
                        check_congruent(pa, pb, eq_rep):
                    merge(pa, pb, eq_sets, eq_rep, p_terms)


def explore_subterms(term, eq_sets, eq_rep, p_terms):
    Q = deque()
    Q.append(term)
    while len(Q) != 0:
        t = Q.pop()
        eq_sets[t] = {t}
        eq_rep[t] = t

        if not t in p_terms:
            p_terms[t] = {t}

        children = t.children()

        for c in children:
            if c not in p_terms:
                p_terms[c] = {t}
            else:
                p_terms[c].add(t)

        Q.extend(children)

    for k in p_terms.keys():
        p_terms[k].add(k)


def initialise_eq(eq):
    eq_sets = {}
    eq_rep = {}
    p_terms = {}
    for atom in eq:
        for term in atom.children():
            explore_subterms(term, eq_sets, eq_rep, p_terms)
    return (eq_sets, eq_rep, p_terms)


def check_sat(eq_rep, diseq):
    for atom in diseq:
        a = atom.arg(0)
        b = atom.arg(1)

        if eq_rep[a].eq(eq_rep[b]):
            return False

    return True


def negate_formula(formula):
    f_kind = formula.decl().kind()
    children = formula.children()
    if f_kind == z3.Z3_OP_AND:
        disjunct = []
        for child in children:
            prop = negate_formula(child)
            disjunct.append(prop)
        return z3.Or(disjunct)
    elif f_kind == z3.Z3_OP_OR:
        conjunct = []
        for child in children:
            prop = negate_formula(child)
            conjunct.append(prop)
        return z3.Or(conjunct)
    elif f_kind == z3.Z3_OP_NOT:
        return children[0]
    else:
        return z3.Not(formula)


def construct_prop_vars(formula, enc_eq, p_eq):
    f_kind = formula.decl().kind()
    children = formula.children()
    if f_kind == z3.Z3_OP_AND:
        conjunct = []
        for child in children:
            prop = construct_prop_vars(child, enc_eq, p_eq)
            conjunct.append(prop)
        return z3.And(conjunct)
    elif f_kind == z3.Z3_OP_OR:
        disjunct = []
        for child in children:
            prop = construct_prop_vars(child, enc_eq, p_eq)
            disjunct.append(prop)
        return z3.Or(disjunct)
    elif f_kind == z3.Z3_OP_NOT:
        negs = []
        for child in children:
            prop = construct_prop_vars(child, enc_eq, p_eq)
            negs.append(prop)

        for p in negs:
            prop = negate_formula(p)
        return prop
    elif f_kind == z3.Z3_OP_EQ:
        key = str(children)
        if not key in enc_eq:
            p_var = z3.Bool("p"+str(formula.hash()))
            enc_eq[key] = p_var
            p_eq[p_var.hash()] = formula
        else:
            p_var = enc_eq[key]
        return p_var
    elif f_kind == z3.Z3_OP_DISTINCT:
        key = str(children)
        if not key in enc_eq:
            p_var = z3.Bool("p"+str(formula.hash()))
            enc_eq[key] = p_var
            p_eq[p_var.hash()] = formula
        else:
            p_var = enc_eq[key]
        return z3.Not(p_var)

    return None


def check_t(p_eq, model):
    conjunct_t = []
    for ass in model:
        if model[ass] == True:
            conjunct_t.append(p_eq[ass.hash()])
        if model[ass] == False:
            conjunct_t.append(p_eq[ass.hash()])
    # euf_formula_list = z3.And(conjunct_t)
    # euf_solver_shostak expects a disjunct as a list
    if euf_solver_shostak(conjunct_t) == z3.unsat:
        return z3.unsat
    else:
        return z3.sat


def learn_clause(enc_eq, p_eq, model):
    clause = []
    for ass in model:
        if model[ass] == True:
            clause.append(enc_eq[str(p_eq[ass.hash()].children())])
        if model[ass] == False:
            clause.append(z3.Not(enc_eq[str(p_eq[ass.hash()].children())]))
    return clause
#########################################################


def euf_solver_shostak(euf_formula_list):
    (eq_sets, eq_rep, p_terms) = initialise_eq(euf_formula_list)
    # print("p_terms : ", p_terms, "\n")
    # print("\neq_sets : ", eq_sets, "\n", "eq_rep : ", eq_rep)
    (eq, diseq) = seperate_eq_diseq(euf_formula_list)
    # print("equalities", eq)
    # print("disequalites", diseq)
    for atom in eq:
        # print("\nConsidering Equality : ", atom)
        a = atom.arg(0)
        b = atom.arg(1)
        merge(a, b, eq_sets, eq_rep, p_terms)

    # print("\n Merged eq_sets : ", eq_sets, "\n Merged eq_rep : ", eq_rep)
    if check_sat(eq_rep, diseq):
        print("IS SAT")
        return z3.sat
    elif not check_sat(eq_rep, diseq):
        print("IS UNSAT")
        return z3.unsat
    else:
        return z3.unknown

        #########################################################


def euf_dpllt_solver(general_euf_formula):
    enc_eq = {}
    p_eq = {}
    print(" EUF Formula: ", general_euf_formula)
    p_form = construct_prop_vars(general_euf_formula, enc_eq, p_eq)
    s = z3.Solver()
    s.add(p_form)
    while True:
        print("EUP P-form : ", s)
        result = s.check()
        if result == z3.unsat:
            print("IS UNSAT")
            break
        elif result == z3.sat:
            result = check_t(p_eq, s.model())
            if result == z3.sat:
                break
            elif result == z3.unsat:
                clause = learn_clause(enc_eq, p_eq, s.model())
                learnt_clause = z3.Not(z3.And(clause))
                print("Learnt Clause : ", learnt_clause)
                s.add(learnt_clause)
            else:
                result = z3.unknown
    return result


#########################################################
# sample dummy unit test functions


def mytest1(msg):
    var_x = z3.Real('x')
    var_y = z3.Real('y')

    formula_1 = z3.And(var_x > 1, var_x < 2, var_y == 3)

    ss = z3.Solver()
    ss.add(formula_1)
    v = ss.check()
    print(msg, v)


def mytest2(msg):
    var_x = z3.Real('x')
    var_y = z3.Real('y')
    formula_2 = z3.Or(var_x == 1, var_y == 2)

    ss = z3.Solver()
    v = ss.check(formula_2)
    print(msg, v)

#########################################################
# write your own unit tests here


def test1():
    print("\n===========")
    print("First Test")
    print("===========")
    x1 = z3.Real('x1')
    x2 = z3.Real('x2')
    x3 = z3.Real('x3')
    euf_elist = [
        x1 == x2,
        x2 == x3,
        x1 != x3,
    ]
    assert euf_solver_shostak(euf_elist) == z3.unsat


def test1a():
    print("\n===========")
    print("First Test A")
    print("===========")
    R = z3.RealSort()
    f1 = z3.Function("f1", R, R)

    x1 = z3.Real('x1')
    x2 = z3.Real('x2')

    euf_elist = [
        x1 == x2,
        f1(x1) == f1(x2),
    ]
    assert euf_solver_shostak(euf_elist) == z3.sat


def test1b():
    print("\n===========")
    print("First Test B")
    print("===========")

    x1 = z3.Real('x1')
    x2 = z3.Real('x2')
    x3 = z3.Real('x3')

    euf_elist = [x1 == x2, x2 == x3, x1 == 2]
    assert euf_solver_shostak(euf_elist) == z3.sat


def test2():
    print("\n===========")
    print("Second Test")
    print("===========")
    S = z3.DeclareSort('S')
    f = z3.Function('f', S, S)
    x = z3.Const('x', S)
    euf_elist = [
        f(f(x)) == x,
        f(f(f(x))) == x
    ]
    assert euf_solver_shostak(euf_elist) == z3.sat


def test3():
    print("\n===========")
    print("Third Test")
    print("===========")
    S = z3.DeclareSort('S')
    f = z3.Function('f', S, S)
    x = z3.Const('x', S)
    euf_elist = [
        f(f(f(f(f(f(x)))))) == x,
        f(f(f(x))) == x,
        f(x) != x
    ]
    assert euf_solver_shostak(euf_elist) == z3.sat


def test3a():
    print("\n===========")
    print("Third Test A")
    print("===========")
    S = z3.DeclareSort('S')
    f = z3.Function('f', S, S)
    x = z3.Const('x', S)
    euf_elist = [
        f(f(f(f(f(x))))) == x,
        f(f(f(x))) == x,
        f(x) != x
    ]
    assert euf_solver_shostak(euf_elist) == z3.unsat


def test4():
    print("\n===========")
    print("Fourth Test")
    print("===========")
    S = z3.DeclareSort('S')
    F = z3.Function('F', S, S)
    G = z3.Function('G', S, S)
    x = z3.Const('x', S)
    euf_elist = [
        G(F(x)) == x,
        F(G(F(x))) == x,
        F(G(x)) != x
    ]
    assert euf_solver_shostak(euf_elist) == z3.unsat


def test5():
    print("\n===========")
    print("Fifth Test")
    print("===========")
    S = z3.DeclareSort('S')
    F = z3.Function('F', S, S)
    G = z3.Function('G', S, S)
    x = z3.Const('x', S)
    euf_elist = [
        F(G(x)) == x,
        F(F(G(x))) == x,
        G(x) != F(x)
    ]
    assert euf_solver_shostak(euf_elist) == z3.sat


def test6():
    print("\n===========")
    print("Sixth Test")
    print("===========")
    S = z3.DeclareSort('S')
    F = z3.Function('F', S, S, S)
    x = z3.Const('x', S)
    y = z3.Const('y', S)
    euf_elist = [
        F(x, y) == x,
        F(F(x, y), y) != x,
    ]
    assert euf_solver_shostak(euf_elist) == z3.unsat


def test7():
    print("\n===========")
    print("Seventh Test")
    print("===========")
    S = z3.RealSort()
    F = z3.Function('F', S, S)
    G = z3.Function('G', S, S, S)
    x = z3.Real('x')
    y = z3.Real('y')
    z = z3.Real('z')
    euf_elist = [
        x == y,
        y == z,
        G(F(x), y) == G(F(z), x),
        F(x) != y,
    ]
    assert euf_solver_shostak(euf_elist) == z3.sat


def test8():
    print("\n===========")
    print("Eighth Test")
    print("===========")
    S = z3.RealSort()
    g = z3.Function('g', S, S, S)
    x1 = z3.Real('x1')
    x2 = z3.Real('x2')
    x3 = z3.Real('x3')
    euf_elist = [x1 == x3, g(x1, x2) == g(x3, x2)]
    assert euf_solver_shostak(euf_elist) == z3.sat


def test9():
    print("\n===========")
    print("Nineth Test")
    print("===========")
    S = z3.RealSort()
    g = z3.Function('g', S, S, S)
    x1 = z3.Real('x1')
    x2 = z3.Real('x2')
    x3 = z3.Real('x3')
    euf_elist = [x1 == x3, g(x1, x2) != g(x3, x2)]
    assert euf_solver_shostak(euf_elist) == z3.unsat


def testdp_1():
    print("\n===========")
    print("DPLL_T 1")
    print("===========")
    x1 = z3.Real('x1')
    x2 = z3.Real('x2')

    R = z3.RealSort()
    f1 = z3.Function("f1", R, R)

    euf_formula = z3.And(x1 == x2, f1(x1) == f1(x2))
    assert euf_dpllt_solver(euf_formula) == z3.sat


def testdp_2():
    print("\n===========")
    print("DPLL_T 2")
    print("===========")
    S = z3.RealSort()
    g = z3.Function('g', S, S, S)
    x1 = z3.Real('x1')
    x2 = z3.Real('x2')
    x3 = z3.Real('x3')
    euf_formula = z3.And(x1 == x3, g(x1, x2) != g(x3, x2))
    assert euf_dpllt_solver(euf_formula) == z3.unsat


def testdp_3():
    print("\n===========")
    print("DPLL_T 3")
    print("===========")
    R = z3.DeclareSort('R')
    f = z3.Function('f', R, R)
    g = z3.Function('g', R, R)
    x = z3.Const('x', R)

    euf_formula = z3.And(f(g(x)) == x, f(f(g(x))) == x, g(x) != f(x))
    assert euf_dpllt_solver(euf_formula) == z3.sat


def testdp_4():
    print("\n===========")
    print("DPLL_T 4")
    print("===========")
    R = z3.DeclareSort('R')
    f = z3.Function('f', R, R)
    x = z3.Const('x', R)

    euf_formula = z3.And(f(f(f(f(f(x))))) == x,
                         f(f(f(x))) == x,
                         f(x) != x)
    assert euf_dpllt_solver(euf_formula) == z3.unsat


def testdp_5():
    print("\n===========")
    print("DPLL_T 5")
    print("===========")
    R = z3.DeclareSort('R')
    f1 = z3.Function('f1', R, R)
    f2 = z3.Function('f2', R, R)
    x1 = z3.Const('x1', R)

    euf_formula = z3.Or(z3.And(f1(f2(x1)) == x1, f2(f1(f2(x1))) == x1, f2(
        f1(x1)) != x1), z3.And(f2(f1(x1)) == x1, f2(f2(f1(x1))) == x1, f2(x1) != f1(x1)))
    assert euf_dpllt_solver(euf_formula) == z3.sat


def testdp_6():
    print("\n===========")
    print("DPLL_T 6")
    print("===========")
    R = z3.DeclareSort('R')
    f1 = z3.Function('f1', R, R)
    f2 = z3.Function('f2', R, R)
    f3 = z3.Function('f3', R, R)
    g1 = z3.Function('g1', R, R, R)
    x1 = z3.Const('x1', R)

    euf_formula = z3.Or(z3.And(g1(f2(x1), f3(x1)) == x1, f2(f1(f2(x1))) == x1, f2(
        f1(x1)) != x1), z3.And(f2(f1(x1)) == x1, f2(f2(f1(x1))) == x1, f2(x1) != f1(x1)))
    assert euf_dpllt_solver(euf_formula) == z3.sat


def testdp_7():
    print("\n===========")
    print("DPLL_T 7")
    print("===========")
    R = z3.DeclareSort('R')
    f1 = z3.Function('f1', R, R)
    f2 = z3.Function('f2', R, R)
    f3 = z3.Function('f3', R, R)
    g1 = z3.Function('g1', R, R, R)
    x1 = z3.Const('x1', R)

    euf_formula = z3.Or(z3.Not(z3.And(g1(f2(x1), f3(x1)) == x1, f2(f1(f2(x1))) == x1, f2(f1(x1)) != x1), z3.And(f2(f1(x1)) == x1, f2(f2(f1(x1))) == x1, f2(x1)
                                                                                                                != f1(x1))))
    assert euf_dpllt_solver(euf_formula) == z3.sat


def testdp_8():
    print("\n===========")
    print("DPLL_T 8")
    print("===========")
    R = z3.DeclareSort('R')
    f2 = z3.Function('f2', R, R)
    f3 = z3.Function('f3', R, R)
    g1 = z3.Function('g1', R, R, R)
    x1 = z3.Const('x1', R)
    x2 = z3.Const('x2', R)

    euf_formula = z3.Or(
        z3.Not(z3.And(g1(f2(1), f3(x1)) == x1), x1 != 1), x1 != x2)
    assert euf_dpllt_solver(euf_formula) == z3.sat


def testdp_9():
    print("\n===========")
    print("DPLL_T 9")
    print("===========")
    R = z3.DeclareSort('R')
    hhh1 = z3.Function("hhh1", R, R, R, R, R, R)
    hhh2 = z3.Function("hhh2", R, R, R, R, R, R)
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

    euf_formula = z3.Or(
        hhh1(x1, x2, x3, x4, x5) != hhh2(y1, y2, y3, y4, y5),
        z3.Not(x1 != x2)
    )
    assert euf_dpllt_solver(euf_formula) == z3.sat


def testdp_10():
    print("\n===========")
    print("DPLL_T 10")
    print("===========")
    R = z3.DeclareSort('R')
    hhh1 = z3.Function("hhh1", R, R, R, R, R, R)
    hhh2 = z3.Function("hhh2", R, R, R, R, R, R)
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

    euf_formula = z3.And(
        hhh1(x1, x2, x3, x4, x5) != hhh2(y1, y2, y3, y4, y5),
        z3.Not(x1 != x2)
    )
    assert euf_dpllt_solver(euf_formula) == z3.sat
    #########################################################


def test_main():
    # TODO edit this function as you need

    mytest1("formual1")
    mytest2("formual2")
    # my tests

    test1()
    test1a()
    test1b()
    test2()
    test3a()
    test3()
    test4()
    test5()
    test6()
    test7()
    test8()
    test9()


#    testdp_1()
#    testdp_2()
#    testdp_3()
#    testdp_4()
#    testdp_5()
#    testdp_6()

    testdp_7()
    testdp_8()
    testdp_9()
    testdp_10()


#########################################################
# Dont edit this function


def main():
    test_main()


# Dont edit this block
if __name__ == "__main__":
    main()

#########################################################
# EOF
