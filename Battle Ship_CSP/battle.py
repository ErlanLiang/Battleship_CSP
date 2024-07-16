from csp import Constraint, Variable, CSP
from constraints import *
from backtracking import bt_search
import sys
import argparse

def print_solution(s, size):
  s_ = {}
  for (var, val) in s:
    s_[int(var.name())] = val
  for i in range(1, size-1):
    for j in range(1, size-1):
      print(s_[-1-(i*size+j)],end="")
    print('')

#parse board and ships info
#file = open(sys.argv[1], 'r')
#b = file.read()
parser = argparse.ArgumentParser()
parser.add_argument(
  "--inputfile",
  type=str,
  required=True,
  help="The input file that contains the puzzles."
)
parser.add_argument(
  "--outputfile",
  type=str,
  required=True,
  help="The output file that contains the solution."
)
args = parser.parse_args()
file = open(args.inputfile, 'r')
b = file.read()
b2 = b.split()
size = len(b2[0])
size = size + 2
b3 = []
b3 += ['0' + b2[0] + '0']
b3 += ['0' + b2[1] + '0']
b3 += [b2[2] + ('0' if len(b2[2]) == 3 else '')]
b3 += ['0' * size]
for i in range(3, len(b2)):
  b3 += ['0' + b2[i] + '0']
b3 += ['0' * size]
board = "\n".join(b3)

varlist = []
varn = {}
conslist = []

#1/0 variables
for i in range(0,size):
  for j in range(0, size):
    v = None
    if i == 0 or i == size-1 or j == 0 or j == size-1:
      v = Variable(str(-1-(i*size+j)), [0])
    else:
      v = Variable(str(-1-(i*size+j)), [0,1])
    varlist.append(v)
    varn[str(-1-(i*size+j))] = v

#make 1/0 variables match board info
ii = 0
for i in board.split()[3:]:
  jj = 0
  for j in i:
    if j != '0' and j != '.':
      conslist.append(TableConstraint('boolean_match', [varn[str(-1-(ii*size+jj))]], [[1]]))
    elif j == '.':
      conslist.append(TableConstraint('boolean_match', [varn[str(-1-(ii*size+jj))]], [[0]]))
    jj += 1
  ii += 1

#row and column constraints on 1/0 variables
row_constraint = []
for i in board.split()[0]:
  row_constraint += [int(i)]

for row in range(0,size):
  conslist.append(NValuesConstraint('row', [varn[str(-1-(row*size+col))] for col in range(0,size)], [1], row_constraint[row], row_constraint[row]))

col_constraint = []
for i in board.split()[1]:
  col_constraint += [int(i)]

for col in range(0,size):
  conslist.append(NValuesConstraint('col', [varn[str(-1-(col+row*size))] for row in range(0,size)], [1], col_constraint[col], col_constraint[col]))

#diagonal constraints on 1/0 variables
for i in range(1, size-1):
    for j in range(1, size-1):
      for k in range(9):
        conslist.append(NValuesConstraint('diag', [varn[str(-1-(i*size+j))], varn[str(-1-((i-1)*size+(j-1)))]], [1], 0, 1))
        conslist.append(NValuesConstraint('diag', [varn[str(-1-(i*size+j))], varn[str(-1-((i-1)*size+(j+1)))]], [1], 0, 1))

#./S/</>/v/^/M variables
#these would be added to the csp as well, before searching,
#along with other constraints
#for i in range(0, size):
#  for j in range(0, size):
#    v = Variable(str(i*size+j), ['.', 'S', '<', '^', 'v', 'M', '>'])
#    varlist.append(v)
#    varn[str(str(i*size+j))] = v
    #connect 1/0 variables to W/S/L/R/B/T/M variables
#    conslist.append(TableConstraint('connect', [varn[str(-1-(i*size+j))], varn[str(i*size+j)]], [[0,'.'],[1,'S'],[1,'<'],[1,'^'],[1,'v'],[1,'M'],[1,'>']]))

#find all solutions and check which one has right ship #'s
csp = CSP('battleship', varlist, conslist)
solutions, num_nodes = bt_search('BT', csp, 'mrv', True, False)
sys.stdout = open(args.outputfile, 'w')
for i in range(len(solutions)):
    print_solution(solutions[i], size)
    print("--------------")
