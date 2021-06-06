from cspbase import *
import itertools
import traceback

from tenner_csp import tenner_csp_model_1, tenner_csp_model_2
from propagators import prop_FC,  prop_GAC, ord_mrv

b1 = ([[-1, 0, 1,-1, 9,-1,-1, 5,-1, 2],
       [-1, 7,-1,-1,-1, 6, 1,-1,-1,-1],
       [-1,-1,-1, 8,-1,-1,-1,-1,-1, 9],
       [ 6,-1, 4,-1,-1,-1,-1, 7,-1,-1],
       [-1, 1,-1, 3,-1,-1, 5, 8, 2,-1]],
      [29,16,18,21,24,24,21,28,17,27])

b1_sol = ([[3, 0, 1, 7, 9, 4, 8, 5, 6, 2],
       [9, 7, 5, 3, 0, 6, 1, 2, 8, 4],
       [2, 3, 1, 8, 7, 5, 4, 6, 0, 9],
       [6, 5, 4, 0, 2, 9, 3, 7, 1, 8],
       [9, 1, 7, 3, 6, 0, 5, 8, 2, 4]],
      [29,16,18,21,24,24,21,28,17,27])

b2 = ([[-1, -1, -1, 3, -1, -1, 8, 6, 5, -1],
       [-1, -1, -1, -1, -1, -1, -1, 1, 2, -1],
       [7, -1, -1, 9, -1, 6, 8, 5, -1, 4],
       [-1, -1, -1, -1, 5, -1, 1, 4, 6, -1],
       [-1, -1, -1, -1, -1, -1, -1, -1, 0, 4],
       [-1, -1, -1, 8, -1, -1, -1, -1, -1, -1],
       [5, 8, -1, 7, -1, 4, -1, 0, 2, -1],],
      [26, 29, 40, 50, 20, 46, 26, 28, 16, 34])

b2_sol = ([[1, 2, 4, 3, 0, 9, 8, 6, 5, 7],
       [9, 6, 5, 7, 4, 3, 0, 1, 2, 8],
       [7, 2, 3, 9, 1, 6, 8, 5, 0, 4],
       [3, 0, 8, 7, 5, 9, 1, 4, 6, 2],
       [1, 7, 5, 9, 2, 8, 6, 3, 0, 4],
       [0, 4, 6, 8, 5, 7, 2, 9, 1, 3],
       [5, 8, 9, 7, 3, 4, 1, 0, 2, 6],],
      [26, 29, 40, 50, 20, 46, 26, 28, 16, 34])

#Puzzle b2 does not have a unique solution! 
b2_sol_alternative = ([[1, 2, 4, 3, 0, 9, 8, 6, 5, 7],
       [8, 6, 5, 7, 4, 3, 0, 1, 2, 9],
       [7, 2, 3, 9, 1, 6, 8, 5, 0, 4],
       [3, 0, 8, 7, 5, 9, 1, 4, 6, 2],
       [2, 7, 5, 9, 1, 8, 6, 3, 0, 4],
       [0, 4, 6, 8, 3, 7, 2, 9, 1, 5],
       [5, 8, 9, 7, 6, 4, 1, 0, 2, 3],],
      [26, 29, 40, 50, 20, 46, 26, 28, 16, 34])

b3 = ([[-1,-1, 3,-1, 5,-1,-1,-1, 6,-1],
       [ 6,-1, 5, 9, 3, 8,-1,-1,-1,-1],
       [-1, 0,-1,-1,-1,-1, 6,-1, 8, 5],
       [ 2, 5,-1, 9,-1,-1,-1,-1, 3,-1]],
      [18,12,19,27,18,19,15,17,19,16])

b3_sol = ([[ 1, 0, 3, 8, 5, 2, 4, 9, 6, 7],
       [ 6, 7, 5, 9, 3, 8, 1, 0, 2, 4],
       [ 9, 0, 3, 1, 4, 2, 6, 7, 8, 5],
       [ 2, 5, 8, 9, 6, 7, 4, 1, 3, 0]],
      [18,12,19,27,18,19,15,17,19,16])

b4 = ([[ 1, 5, 4, 7,-1,-1,-1,-1, 2,-1],
       [-1,-1,-1, 5, 8, 1, 2, 7, 4,-1],
       [-1,-1, 4, 7, 2, 9,-1,-1,-1, 1],
       [ 3,-1, 1, 8,-1,-1, 2, 6,-1, 4],
       [ 0, 9, 6, 2, 1, 3, 4, 5,-1, 7],
       [ 5,-1, 1,-1,-1, 6, 8, 7, 3, 9]],
      [18,28,22,33,20,27,19,41,26,36])

b4_sol = ([[ 1, 5, 4, 7, 9, 3, 0, 8, 2, 6],
       [ 3, 0, 6, 5, 8, 1, 2, 7, 4, 9],
       [ 6, 5, 4, 7, 2, 9, 3, 8, 0, 1],
       [ 3, 7, 1, 8, 0, 5, 2, 6, 9, 4],
       [ 0, 9, 6, 2, 1, 3, 4, 5, 8, 7],
       [ 5, 2, 1, 4, 0, 6, 8, 7, 3, 9]],
      [18,28,22,33,20,27,19,41,26,36])

empty = ([[-1,-1,-1,-1,-1,-1,-1,-1,-1,-1],
       [-1,-1,-1,-1,-1,-1,-1,-1,-1,-1],
       [-1,-1,-1,-1,-1,-1,-1,-1,-1,-1],
       [-1,-1,-1,-1,-1,-1,-1,-1,-1,-1],
       [-1,-1,-1,-1,-1,-1,-1,-1,-1,-1]],
      [-1,-1,-1,-1,-1,-1,-1,-1,-1,-1])



def queensCheck(qi, qj, i, j):
    '''Return true if i and j can be assigned to the queen in row qi and row qj
       respectively. Used to find satisfying tuples.
    '''
    return i != j and abs(i-j) != abs(qi-qj)

def nQueens(n):
    '''Return an n-queens CSP'''
    i = 0
    dom = []
    for i in range(n):
        dom.append(i+1)

    vars = []
    for i in dom:
        vars.append(Variable('Q{}'.format(i), dom))

    cons = []
    for qi in range(len(dom)):
        for qj in range(qi+1, len(dom)):
            con = Constraint("C(Q{},Q{})".format(qi+1,qj+1),[vars[qi], vars[qj]])
            sat_tuples = []
            for t in itertools.product(dom, dom):
                if queensCheck(qi, qj, t[0], t[1]):
                    sat_tuples.append(t)
            con.add_satisfying_tuples(sat_tuples)
            cons.append(con)

    csp = CSP("{}-Queens".format(n), vars)
    for c in cons:
        csp.add_constraint(c)
    return csp

##Tests FC after the first queen is placed in position 1.
def test_simple_FC():
    did_fail = False
    score = 0
    try:
        queens = nQueens(8)
        curr_vars = queens.get_all_vars()
        curr_vars[0].assign(1)
        prop_FC(queens,newVar=curr_vars[0])
        answer = [[1],[3, 4, 5, 6, 7, 8],[2, 4, 5, 6, 7, 8],[2, 3, 5, 6, 7, 8],[2, 3, 4, 6, 7, 8],[2, 3, 4, 5, 7, 8],[2, 3, 4, 5, 6, 8],[2, 3, 4, 5, 6, 7]]
        var_domain = [x.cur_domain() for x in curr_vars]
        for i in range(len(curr_vars)):
            if var_domain[i] != answer[i]:
                details = "Failed simple FC test: variable domains don't match expected results"
                did_fail = True
                break
        if not did_fail:
            score = 1
            details = ""
    except Exception:
        details = "One or more runtime errors occurred while testing simple FC: %r" % traceback.format_exc()

    return score,details


##Tests GAC after the first queen is placed in position 1.
def test_simple_GAC():
    did_fail = False
    score = 0
    try:
        queens = nQueens(8)
        curr_vars = queens.get_all_vars()
        curr_vars[0].assign(1)
        prop_GAC(queens,newVar=curr_vars[0])
        answer = [[1],[3, 4, 5, 6, 7, 8],[2, 4, 5, 6, 7, 8],[2, 3, 5, 6, 7, 8],[2, 3, 4, 6, 7, 8],[2, 3, 4, 5, 7, 8],[2, 3, 4, 5, 6, 8],[2, 3, 4, 5, 6, 7]]
        var_domain = [x.cur_domain() for x in curr_vars]
        print(var_domain)
        print(answer)
        for i in range(len(curr_vars)):
            if var_domain[i] != answer[i]:
                details = "Failed simple GAC test: variable domains don't match expected results."
                did_fail = True
                break
        if not did_fail:
            score = 1
            details = ""

    except Exception:
        details = "One or more runtime errors occurred while testing simple GAC: %r" % traceback.format_exc()

    return score,details


def three_queen_GAC():
    score = 0
    try:
        queens = nQueens(8)
        curr_vars = queens.get_all_vars()
        curr_vars[0].assign(4)
        curr_vars[2].assign(1)
        curr_vars[7].assign(5)
        prop_GAC(queens)
        answer = [[4],[6, 7, 8],[1],[3, 8],[6, 7],[2, 8],[2, 3, 7, 8],[5]]
        var_vals = [x.cur_domain() for x in curr_vars]

        print(var_vals)
        print(answer)
        if var_vals != answer:
            details = "Failed three queens GAC test: variable domains don't match expected results"

        else:
            score = 1
            details = ""
    except Exception:
        details = "One or more runtime errors occurred while testing GAC with three queens: %r" % traceback.format_exc()

    return score,details


def three_queen_FC():
    score = 0
    try:
        queens = nQueens(8)
        curr_vars = queens.get_all_vars()
        curr_vars[0].assign(4)
        curr_vars[2].assign(1)
        curr_vars[7].assign(5)
        prop_FC(queens)

        answer = [[4],[6, 7, 8],[1],[3, 6, 8],[6, 7],[2, 6, 8],[2, 3, 7, 8],[5]]
        var_vals = [x.cur_domain() for x in curr_vars]

        if var_vals != answer:
            details = "Failed three queens FC test: variable domains don't match expected results"

        else:
            score = 1
            details = ""

    except Exception:
        details = "One or more runtime errors occurred while testing FC with three queens: %r" % traceback.format_exc()

    return score,details
  

def print_tenner_soln(var_array):
    for row in var_array:
        print([var.get_assigned_value() for var in row])

if __name__ == "__main__":
    #import propagators as stu_propagators
    #import tenner_csp as stu_models

    print("Model and Propagator Tests")
    for b in [b3, b4]:
        print("Solving board:")
        for row in b[0]:
            print(row)

        print("Using Model 1")
        csp, var_array = tenner_csp_model_1(b)
        if csp != None:
            solver = BT(csp)
            print("=======================================================")
            print("GAC")
            solver.bt_search(prop_GAC, var_ord=ord_mrv)
            print("Solution")
            print_tenner_soln(var_array)

        print("Using Model 2")        
        csp, var_array = tenner_csp_model_2(b)
        if csp != None:        
            solver = BT(csp)
            print("=======================================================")
            print("FC")
            solver.bt_search(prop_FC, var_ord=ord_mrv)
            print("Solution")
            print_tenner_soln(var_array)

    total = 0
    print("Propagator Tests")

    print("---starting test_simple_FC---")
    score,details = test_simple_FC()
    total += score
    print(details)
    print("---finished test_simple_FC---\n")

    print("---starting test_simple_GAC---")
    score,details = test_simple_GAC()
    total += score
    print(details)
    print("---finished test_simple_GAC---\n")

    print("---starting three_queen_FC---")
    score,details = three_queen_FC()
    total += score
    print(details)
    print("---finished three_queen_FC---\n")

    print("---starting three_queen_GAC---")
    score,details = three_queen_GAC()
    total += score
    print(details)
    print("---finished three_queen_GAC---\n")
    print("Total score %d/4\n" % total)        
