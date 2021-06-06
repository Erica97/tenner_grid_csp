#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete the warehouse domain.  
from cspbase import *
import itertools

def get_binary_row_constraints(vars, values):
  binary_row_cons = []
  for i in range(10):
      for j in range(i+1, 10):
          con = Constraint("C(T{},T{})".format(i,j),[vars[i], vars[j]])  
          sat_tuples = []
          #get all pair-wise comparisons between values of i and values of all variables after i
          pairwise_comparison = itertools.product(values[i], values[j])
          for tup in pairwise_comparison:
            if tup[0] != tup[1]:
              sat_tuples.append(tup) 
          con.add_satisfying_tuples(sat_tuples)  
          binary_row_cons.append(con)
  return binary_row_cons

def get_n_ary_row_constraints(initial_tenner_board, vars, values):
  n_ary_row_cons = []
  num_rows = len(initial_tenner_board[0])
  for i in range(num_rows):
    scope = []
    for j in range(10): #possible values: 0-9
        if len(values[i*10+j]) != 1: #variables not filled out
            scope.append(vars[i*10+j])
            ind = i*10+j
        else:
            #special case when only one var in the row is not filled out.
            #set to x+10 to differentiate from given vars, then recover to x
            if values[i*10+j][0] >= 10:
                scope.append(vars[i*10+j])
                values[i*10+j][0] -= 10 
                ind = i*10+j
    con = Constraint("C(Trow{})".format(i),scope)  
    sat_tuples = []
    for tup in itertools.permutations(values[ind]):
        sat_tuples.append(tup)
    con.add_satisfying_tuples(sat_tuples)
    n_ary_row_cons.append(con)
  return n_ary_row_cons

def get_column_constraints(initial_tenner_board, vars, values):
  column_cons = []
  num_rows = len(initial_tenner_board[0])
  for i in range(10):
    scope = []
    domain = []
    for j in range(num_rows):
      scope.append(vars[j*10+i])
      domain.append(values[j*10+i])
    con = Constraint("C(Tcolumn{})".format(i),scope)  
    sat_tuples = []
    #get all possible permutations
    for tup in itertools.product(*domain):
      if sum(tup) == initial_tenner_board[1][i]:
        sat_tuples.append(tup)
    con.add_satisfying_tuples(sat_tuples)
    #print("col con:", con)
    column_cons.append(con)
  return column_cons

def get_contigous_indices(num):
  '''
  return all up/down and diagonal pairs of indicies
  '''
  indices = []
  for i in range(num):
    for j in range(10):
      if j != 0:
        indices.append([[i,j], [i+1,j-1]]) #diagonal
      if j != 9:
        indices.append([[i,j], [i+1,j+1]]) #diagonal
      indices.append([[i,j], [i+1,j]]) #up,down
  return indices

def get_contiguous_constraints(initial_tenner_board, vars, values):
  contiguous_cons = []
  num_rows = len(initial_tenner_board[0])
  indices = get_contigous_indices(num_rows-1)
  for i in range(len(indices)):
    scope = [vars[indices[i][0][0]*10+indices[i][0][1]], vars[indices[i][1][0]*10+indices[i][1][1]]] #multiply by 10 to match row
    domain = [values[indices[i][0][0]*10+indices[i][0][1]], values[indices[i][1][0]*10+indices[i][1][1]]]
    con = Constraint("C(Tcontiguous{},{})".format(indices[i][0], indices[i][1]),scope)  
    sat_tuples = []
    for tup in itertools.product(*domain):#all permutations
      if tup[0] != tup[1]: #current var cannot be the same as any of its neighbors
        sat_tuples.append(tup)
    con.add_satisfying_tuples(sat_tuples)
    #print("contiguous con:", con)
    contiguous_cons.append(con)
  return contiguous_cons

def tenner_csp_model_1(initial_tenner_board):
  variables = []
  vars = []
  values = []
  num_rows = len(initial_tenner_board[0])
  for i in range(num_rows):
    dom = [0,1,2,3,4,5,6,7,8,9]
    dom_pruned = [0,1,2,3,4,5,6,7,8,9]
    for j in range(10):
      if initial_tenner_board[0][i][j] != -1: #assigned
        dom_pruned.remove(initial_tenner_board[0][i][j])
    for j in range(10):
      if initial_tenner_board[0][i][j] == -1:
        vars.append(Variable('V{},{}'.format(i,j), dom_pruned))
        values.append(dom_pruned)
      else:
        vars.append(Variable('V{},{}'.format(i,j), [initial_tenner_board[0][i][j]]))
        values.append([initial_tenner_board[0][i][j]])
  cons = []
  for i in range(num_rows):
    cons += get_binary_row_constraints(vars[i*10:i*10+10], values[i*10:i*10+10]) #row by row
    variables.append(vars[10*i:10*i+10]) 
  cons += get_contiguous_constraints(initial_tenner_board, vars, values)
  cons += get_column_constraints(initial_tenner_board, vars, values)
  csp = CSP("TENNER-Model1", vars)
  for con in cons:
    csp.add_constraint(con)
  return csp, variables

##############################

def tenner_csp_model_2(initial_tenner_board):
  variables = []
  vars = []
  values = []
  num_rows = len(initial_tenner_board[0])
  for i in range(num_rows):
    dom = [0,1,2,3,4,5,6,7,8,9]
    dom_pruned = [0,1,2,3,4,5,6,7,8,9]
    for j in range(10):
      if initial_tenner_board[0][i][j] != -1: #assigned
        dom_pruned.remove(initial_tenner_board[0][i][j])
    for j in range(10):
      if initial_tenner_board[0][i][j] == -1:
        vars.append(Variable('V{},{}'.format(i,j), dom))
        if len(dom_pruned) != 1:
            values.append(dom_pruned)
        else:
            single_val = dom_pruned[0] + 10 #differentiate from filled out cells, will -10 later
            values.append([single_val])
      else:
        vars.append(Variable('V{},{}'.format(i,j), [initial_tenner_board[0][i][j]]))
        values.append([initial_tenner_board[0][i][j]])
        #print("values for predefined cell:", values[10*i+j])
  cons = []
  cons += get_n_ary_row_constraints(initial_tenner_board, vars, values)
  cons += get_contiguous_constraints(initial_tenner_board, vars, values)
  cons += get_column_constraints(initial_tenner_board, vars, values)
  for i in range(num_rows):
    variables.append(vars[10*i:10*i+10]) #append row by row
  csp = CSP("TENNER-Model2", vars)
  for con in cons:
    csp.add_constraint(con)
  return csp, variables