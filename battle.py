from csp import Constraint, Variable, CSP
from constraints import *
from backtracking import bt_search
import sys
import argparse
import time

def print_solution(s, size):
  s_ = {}
  for (var, val) in s:
    s_[int(var.name())] = val
  for i in range(1, size-1):
    for j in range(1, size-1):
      print(s_[-1-(i*size+j)],end="")
    print('')

def match_result(solutions, reuqired_ships, size):
  '''match the result with required ships
  by checking all the variables in each solution start from -1 to -size*size
  if the variable is 1, then check the ship around it, and add the variable visited to the set.
  if a new variable is visited, then skip it.
  if the variable is 0, then skip it.
  ship[first_variable] = [visited_variables]
  solution[0] 对应的是Variable -1, solution[1] 对应的是Variable -2, 以此类推
  当我们想找到variable上下左右对应solution具体的值我们可以按以下公式：
  top: ((int(var.name()) * -1) - 1) - size
  bottom: ((int(var.name()) * -1) - 1) + size
  left: ((int(var.name()) * -1) - 1) - 1
  right: ((int(var.name()) * -1) - 1) + 1
  '''
  # print("size: ", size)
  for y in range(len(solutions)):
    result = solutions[y]
    ships = [0, 0, 0, 0]
    ship = {}
    visited = set()
    for i in range(len(result)):
      var, val = result[i]
      if val == 1 and var.name() not in visited:
        ship[var.name()] = [i]
        visited.add(var.name())

        bottom = ((int(var.name()) * -1) - 1) + size
        right = ((int(var.name()) * -1) - 1) + 1

        if bottom < size*size and result[bottom][1] == 1:
          result[i] = (var, '^')
          while bottom < size*size and result[bottom][1] == 1:
            ship[var.name()].append(bottom)
            visited.add(result[bottom][0].name())
            bottom = bottom + size
          if len(ship[var.name()]) == 4:
            ships[3] += 1
            if ships[3] > reuqired_ships[3]:
              # print("vertical ships[3]: ", ships[3])
              break
            result[ship[var.name()][1]] = (result[ship[var.name()][1]][0], 'M')
            result[ship[var.name()][2]] = (result[ship[var.name()][2]][0], 'M')
            result[ship[var.name()][3]] = (result[ship[var.name()][3]][0], 'v')
          elif len(ship[var.name()]) == 3:
            ships[2] += 1
            if ships[2] > reuqired_ships[2]:
              # print("vertical ships[2]: ", ships[2])
              break
            result[ship[var.name()][1]] = (result[ship[var.name()][1]][0], 'M')
            result[ship[var.name()][2]] = (result[ship[var.name()][2]][0], 'v')
          elif len(ship[var.name()]) == 2:
            ships[1] += 1
            if ships[1] > reuqired_ships[1]:
              # print("vertical ships[1]: ", ships[1])
              break
            result[ship[var.name()][1]] = (result[ship[var.name()][1]][0], 'v')
        elif i%size != size - 1 and result[right][1] == 1:
          result[i] = (var, '<')
          while right%size != size - 1 and  result[right][1] == 1:
            ship[var.name()].append(right)
            visited.add(result[right][0].name())
            right = right + 1
          if len(ship[var.name()]) == 4:
            ships[3] += 1
            if ships[3] > reuqired_ships[3]:
              # print("horzontal ships[3]: ", ships[3])
              break
            result[ship[var.name()][1]] = (result[ship[var.name()][1]][0], 'M')
            result[ship[var.name()][2]] = (result[ship[var.name()][2]][0], 'M')
            result[ship[var.name()][3]] = (result[ship[var.name()][3]][0], '>')
          elif len(ship[var.name()]) == 3:
            ships[2] += 1
            if ships[2] > reuqired_ships[2]:
              # print("horzontal ships[2]: ", ships[2])
              break
            result[ship[var.name()][1]] = (result[ship[var.name()][1]][0], 'M')
            result[ship[var.name()][2]] = (result[ship[var.name()][2]][0], '>')
          elif len(ship[var.name()]) == 2:
            ships[1] += 1
            if ships[1] > reuqired_ships[1]:
              # print("horzontal ships[1]: ", ships[1])
              break
            result[ship[var.name()][1]] = (result[ship[var.name()][1]][0], '>')
        else:
          result[i] = (var, 'S')
          ships[0] += 1
          if ships[0] > reuqired_ships[0]:
            # print("ships[0]: ", ships[0])
            break
      elif var.name() in visited:
        pass
      else:
        result[i] = (var, '.')
    if ships == reuqired_ships:
      # check if all the special positions are correct
      correct = True
      for i in range(len(result)):
        if i in special_positions:
          if result[i][1] != special_positions[i]:
            correct = False
            break
      if correct:
        return result, y
  return [], -1


        
  

start = time.time()
#parse board and ships inforow_constraint
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

special_positions = {}
# get all the special positions that are not 0
count = 0
for i in range(3, len(b3)):
  for j in b3[i]:
    if j != '0':
      special_positions[count] = (j)
    count += 1


# print("board: ", board)

reuqired_ships = [int(i) for i in board.split()[2]]
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
    # print(-1-(i*size+j))
    varn[str(-1-(i*size+j))] = v

# print("size: ", size)
# print("varlist: ", varlist)
# print("varn: ", varn)

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

# print("conslist1: ", conslist)

col_constraint = []
for i in board.split()[1]:
  col_constraint += [int(i)]

for col in range(0,size):
  conslist.append(NValuesConstraint('col', [varn[str(-1-(col+row*size))] for row in range(0,size)], [1], col_constraint[col], col_constraint[col]))

# print("conslist2: ", conslist)

#diagonal constraints on 1/0 variables
for i in range(1, size-1):
    for j in range(1, size-1):
      conslist.append(NValuesConstraint('diag', [varn[str(-1-(i*size+j))], varn[str(-1-((i-1)*size+(j-1)))]], [1], 0, 1))
      conslist.append(NValuesConstraint('diag', [varn[str(-1-(i*size+j))], varn[str(-1-((i-1)*size+(j+1)))]], [1], 0, 1))

# print("conslist3: ", conslist)

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
# for i in range(1, size-1):
#     for j in range(1, size-1):
#       conslist.append(WaterAroundShipConstraint('ship', [varn[str(-1-(i*size+j))]], size, varn))

csp = CSP('battleship', varlist, conslist, varn, size)

# solutions, num_nodes = bt_search('BT', csp, 'mrv', True, False)
solutions, num_nodes = bt_search('GAC', csp, 'mrv', True, False)
print("run time: ", time.time()-start)

# print("solution: ", solutions)
# for s in solutions:
#   print(s[0].name(), ": ", s[1])
# print(solutions)
# for i in range(len(solutions)):
#   print(solutions[i])
#   print_solution(solutions[i], size)
#   print("--------------")

final_result, num = match_result(solutions, reuqired_ships, size)
# print(final_result)
# print("num: ", num)

sys.stdout = open(args.outputfile, 'w')
# for i in range(len(solutions)):
#     print("solution: ", i)
#     print_solution(solutions[i], size)
#     print("--------------")
# print("num_sol: ", len(solutions))
print_solution(final_result, size)
print("finish time: ", time.time()-start)
