from csp import Constraint, Variable


class TableConstraint(Constraint):
    '''General type of constraint that can be use to implement any type of
       constraint. But might require a lot of space to do so.

       A table constraint explicitly stores the set of satisfying
       tuples of assignments.'''

    def __init__(self, name, scope, satisfyingAssignments):
        '''Init by specifying a name and a set variables the constraint is over.
           Along with a list of satisfying assignments.
           Each satisfying assignment is itself a list, of length equal to
           the number of variables in the constraints scope.
           If sa is a single satisfying assignment, e.g, sa=satisfyingAssignments[0]
           then sa[i] is the value that will be assigned to the variable scope[i].


           Example, say you want to specify a constraint alldiff(A,B,C,D) for
           three variables A, B, C each with domain [1,2,3,4]
           Then you would create this constraint using the call
           c = TableConstraint('example', [A,B,C,D],
                               [[1, 2, 3, 4], [1, 2, 4, 3], [1, 3, 2, 4],
                                [1, 3, 4, 2], [1, 4, 2, 3], [1, 4, 3, 2],
                                [2, 1, 3, 4], [2, 1, 4, 3], [2, 3, 1, 4],
                                [2, 3, 4, 1], [2, 4, 1, 3], [2, 4, 3, 1],
                                [3, 1, 2, 4], [3, 1, 4, 2], [3, 2, 1, 4],
                                [3, 2, 4, 1], [3, 4, 1, 2], [3, 4, 2, 1],
                                [4, 1, 2, 3], [4, 1, 3, 2], [4, 2, 1, 3],
                                [4, 2, 3, 1], [4, 3, 1, 2], [4, 3, 2, 1]])
          as these are the only assignments to A,B,C respectively that
          satisfy alldiff(A,B,C,D)
        '''

        Constraint.__init__(self,name, scope)
        self._name = "TableCnstr_" + name
        self.satAssignments = satisfyingAssignments

    def check(self):
        '''check if current variable assignments are in the satisfying set'''
        assignments = []
        for v in self.scope():
            if v.isAssigned():
                assignments.append(v.getValue())
            else:
                return True
        return assignments in self.satAssignments

    def hasSupport(self, var,val):
        '''check if var=val has an extension to an assignment of all variables in
           constraint's scope that satisfies the constraint. Important only to
           examine values in the variable's current domain as possible extensions'''
        if var not in self.scope():
            return True   #var=val has support on any constraint it does not participate in
        vindex = self.scope().index(var)
        found = False
        for assignment in self.satAssignments:
            if assignment[vindex] != val:
                continue   #this assignment can't work it doesn't make var=val
            found = True   #Otherwise it has potential. Assume found until shown otherwise
            for i, v in enumerate(self.scope()):
                if i != vindex and not v.inCurDomain(assignment[i]):
                    found = False  #Bummer...this assignment didn't work it assigns
                    break          #a value to v that is not in v's curDomain
                                   #note we skip checking if val in in var's curDomain
            if found:     #if found still true the assigment worked. We can stop
                break
        return found     #either way found has the right truth value

def findvals(remainingVars, assignment, finalTestfn, partialTestfn=lambda x: True):
    '''Helper function for finding an assignment to the variables of a constraint
       that together with var=val satisfy the constraint. That is, this
       function looks for a supporing tuple.

       findvals uses recursion to build up a complete assignment, one value
       from every variable's current domain, along with var=val.

       It tries all ways of constructing such an assignment (using
       a recursive depth-first search).

       If partialTestfn is supplied, it will use this function to test
       all partial assignments---if the function returns False
       it will terminate trying to grow that assignment.

       It will test all full assignments to "allVars" using finalTestfn
       returning once it finds a full assignment that passes this test.

       returns True if it finds a suitable full assignment, False if none
       exist. (yes we are using an algorithm that is exactly like backtracking!)'''

    # print "==>findvars([",
    # for v in remainingVars: print v.name(), " ",
    # print "], [",
    # for x,y in assignment: print "({}={}) ".format(x.name(),y),
    # print ""

    #sort the variables call the internal version with the variables sorted
    remainingVars.sort(reverse=True, key=lambda v: v.curDomainSize())
    return findvals_(remainingVars, assignment, finalTestfn, partialTestfn)

def findvals_(remainingVars, assignment, finalTestfn, partialTestfn):
    '''findvals_ internal function with remainingVars sorted by the size of
       their current domain'''
    if len(remainingVars) == 0:
        return finalTestfn(assignment)
    var = remainingVars.pop()
    for val in var.curDomain():
        assignment.append((var, val))
        if partialTestfn(assignment):
            if findvals_(remainingVars, assignment, finalTestfn, partialTestfn):
                return True
        assignment.pop()   #(var,val) didn't work since we didn't do the return
    remainingVars.append(var)
    return False


class NValuesConstraint(Constraint):
    '''NValues constraint over a set of variables.  Among the variables in
       the constraint's scope the number that have been assigned
       values in the set 'required_values' is in the range
       [lower_bound, upper_bound] (lower_bound <= #of variables
       assigned 'required_value' <= upper_bound)

       For example, if we have 4 variables V1, V2, V3, V4, each with
       domain [1, 2, 3, 4], then the call
       NValuesConstraint('test_nvalues', [V1, V2, V3, V4], [1,4], 2,
       3) will only be satisfied by assignments such that at least 2
       the V1, V2, V3, V4 are assigned the value 1 or 4, and at most 3
       of them have been assigned the value 1 or 4.

    '''

    def __init__(self, name, scope, required_values, lower_bound, upper_bound):
        Constraint.__init__(self,name, scope)
        self._name = "NValues_" + name
        self._required = required_values
        self._lb = lower_bound
        self._ub = upper_bound

    def check(self):
        assignments = []
        for v in self.scope():
            if v.isAssigned():
                assignments.append(v.getValue())
            else:
                return True
        rv_count = 0

        #print "Checking {} with assignments = {}".format(self.name(), assignments)

        for v in assignments:
            if v in self._required:
                rv_count += 1

        #print "rv_count = {} test = {}".format(rv_count, self._lb <= rv_count and self._ub >= rv_count)


        return self._lb <= rv_count and self._ub >= rv_count

    def hasSupport(self, var, val):
        '''check if var=val has an extension to an assignment of the
           other variable in the constraint that satisfies the constraint

           HINT: check the implementation of AllDiffConstraint.hasSupport
                 a similar approach is applicable here (but of course
                 there are other ways as well)
        '''
        if var not in self.scope():
            return True   #var=val has support on any constraint it does not participate in

        #define the test functions for findvals
        def valsOK(l):
            '''tests a list of assignments which are pairs (var,val)
               to see if they can satisfy this sum constraint'''
            rv_count = 0
            vals = [val for (var, val) in l]
            for v in vals:
                if v in self._required:
                    rv_count += 1
            least = rv_count + self.arity() - len(vals)
            most =  rv_count
            return self._lb <= least and self._ub >= most
        varsToAssign = self.scope()
        varsToAssign.remove(var)
        x = findvals(varsToAssign, [(var, val)], valsOK, valsOK)
        return x
    
class WaterAroundShipConstraint(Constraint):
    ''' according to the rules of the game, there must be at least one water cell around each ship cell.
    If a ship cell is at the edge of the board, then the against wall side water can be ignored.
    '''
    def __init__(self, name, scope, size, varn):
        Constraint.__init__(self,name, scope)
        self._name = "WaterAroundShip_" + name
        # self.position = self.setup_position(scope)
        self.size = size
        self.varn = varn
        # TODO: 修改结构为 scope只包括一个variable，每次判断单个的周围，同样是ship的话放入对应的horizonal或者vertical的set,
        # 当一个variable同时出现在两个set里面的时候，return False
    
    # def setup_position(self, scope):
    #     p = set()
    #     for v in scope:
    #         p.add(int(v.name()))

    def check(self):
        '''check if current variable assignments are in the satisfying set, return True if the assignment is valid, False otherwise
        '''
        # if len(self.scope()) >= 4:
        #     return False
        # for v in self.scope():
        
        v = self.scope()[0]
        if v.getValue() == 1:
            num = int(v.name())
            # check if the current variable is on the left or right edge of the board

            if (num * -1) % self.size == 0:
                # right = 1
                top_right = 1
                bottom_right = 1
            else:
                # right = num - 1
                bottom_right = num - self.size - 1
                top_right = num + self.size - 1

            if (num * -1) % self.size == 1:
                # left = 1
                top_left = 1
                bottom_left = 1
            else:
                # left = num + 1
                bottom_left = num - self.size + 1
                top_left = num + self.size + 1
            # print("num: ", num)
            # print("top_right: ", top_right)
            # print("top_left: ", top_left)
            # print("bottom_right: ", bottom_right)
            # print("bottom_left: ", bottom_left)

            for i in [ top_right, top_left, bottom_right, bottom_left]:
                if i < 0 and i > self.size * self.size * -1:
                    # print(self.varn[str(i)].isAssigned())
                    
                    if self.varn[str(i)].isAssigned() and self.varn[str(i)].getValue() == 1:
                        return False
        return True
    
    def hasSupport(self, var, val):
        pass

    # def add_new_var(self, var):
    #     self.scope().append(var)
    #     self.position.add(int(var.name()))

    # def unAssignVars(self):
    #     for v in self.scope():
    #         if not v.isAssigned():
    #             self.scope().remove(v)
    #             self.position.remove(int(v.name()))
                    


# class ShipConstraint(Constraint):
#     ''' This constraint will saved the ship cells and the ship length.
#     The scope of this constraint will be all the variables that are ship cells.
#     water_spot_dic is a dictionary [variable that is a ship cell] = [water cells around it(4 edge coners: top left, top right, bottom left, bottom right)]
#     water_spot is a set of variables that cant not be ship cells
#     available_spot is a set of variables that can be ship cells, when adding a new available spot, if already exist, then delete it from the available spot 
#     and add it to the water spot

#     cur_ship1 is the list of ship that length is 1
#     cur_ship2 is the list of ship that length is 2
#     cur_ship3 is the list of ship that length is 3
#     cur_ship4 is the list of ship that length is 4
#     ''' 

#     def __init__(self, name, scope, size):
#         Constraint.__init__(self,name, scope)
#         self._name = "Ship_" + name
#         self.size = size
#         # self.cur_var = cur_var
#         # self.last = None
#         self._water_spot_dic, self._water_spot = self.create_water_spot(scope)
#         self._available_spot = set()
#         self._REavailable_spot = {}
#         self._cur_ship1 = []
#         self._cur_ship2 = []
#         self._cur_ship3 = []
#         self._cur_ship4 = []
    
#     def check(self):
#         pass

#     def water_spot(self):
#         return self._water_spot
    
#     def water_spot_dic(self):
#         return self._water_spot_dic
    
#     def available_spot(self):
#         return self._available_spot
    
#     def REavailable_spot(self):
#         return self._REavailable_spot
    
#     def cur_ship1(self):
#         return self._cur_ship1
    
#     def cur_ship2(self):
#         return self._cur_ship2
    
#     def cur_ship3(self):
#         return self._cur_ship3
    
#     def cur_ship4(self):
#         return self._cur_ship4
    
#     def create_water_spot(self, scope):
#         water_spot_dic = {}
#         water_spot = set()
#         for v in scope:
#             water_spot_dic[v] = []
#             top_left = int(v.name()) + self.size + 1
#             top_right = int(v.name()) + self.size - 1
#             bottom_left = int(v.name()) - self.size + 1
#             bottom_right = int(v.name()) - self.size - 1
#             for i in [top_left, top_right, bottom_left, bottom_right]:
#                 if i >= 0 and i < self.size * self.size:
#                     water_spot_dic[v.name()].append(i)
#                     water_spot.add(i)
#         return water_spot_dic, water_spot
    
#     def add_new_var(self, var):
#         '''
#         add new variable to the ship constraint
#         first check if it is next to a exist ship cell, if so add it to the ship cell and update the ship length
#         if not, add create a new ship cell with length 1
#         '''
#         self.create_water_spot([var])                           # update the water spot around the new ship cell
#         if var.name() not in self.available_spot():
#             self.cur_ship1().append(var)                        # add the new ship cell to the ship cell list
#             self.update_available_spot(var, ShipCell([var], 1)) # update the available spot around the new ship cell
#         else:
#             ship_cell = self.REavailable_spot()[var.name()] # get the ship cell that is next to the new ship cell
#             self.available_spot().remove(var.name())        # remove the new ship cell from the available spot
#             ship_cell.addvars(var)                    # add the new ship cell to the ship cell list
#             self.update_available_spot(var, ship_cell)      # update the available spot around the new ship cell
    
#     def update_available_spot(self, var, ship_cells):
#         num = int(var.name())
#         # calculate the available spot for the ship cell(top, right, bottom, left)
#         if len(ship_cells.vars) == 1:
#             if (-1 * num) % self.size == 0:
#                 right = 1
#             if (-1 * num) % self.size == 1:
#                 left = 1
#             for i in [right, left, num - self.size, num + self.size]:
#                 if i < 0 and i < self.size * self.size * -1:
#                     self.available_spot().add(str(i))
#                     self.REavailable_spot()[i] = ship_cells
#         else:
#             if ship_cells.direction == "horizontal":
#                 for i in [num - 1, num + 1]:
#                     if i < 0 and i < self.size * self.size * -1:
#                         self.available_spot().add(str(i))
#                         self.REavailable_spot()[i] = ship_cells
#             else:
#                 for i in [num - self.size, num + self.size]:
#                     if i < 0 and i < self.size * self.size * -1:
#                         self.available_spot().add(str(i))
#                         self.REavailable_spot()[i] = ship_cells
    
#     def unAssignVars(self):
#         for i in 

# class ShipCell:

#     def __init__(self, var, size):
#         self.vars = var
#         self.size = size
#         self.direction = None

#     def addvars(self, var):
#         '''
#         add new variable to the ship cell, update the size of the ship cell
#         if direction is None, then calculate the direction of the ship cell
#         "horizontal" if the new variable is in the same row, "vertical" if the new variable is in the same column
#         '''
#         self.vars.append(var)
#         self.size += 1
#         if self.direction is None:
#             if int(self.vars[0].name()) + 1 == int(var.name()) or int(self.vars[0].name()) - 1 == int(var.name()):
#                 self.direction = "horizontal"
#             else:
#                 self.direction = "vertical"

class IfAllThenOneConstraint(Constraint):
    '''if each variable in left_side equals each value in left_values 
    then one of the variables in right side has to equal one of the values in right_values. 
    hasSupport tested only, check() untested.'''
    def __init__(self, name, left_side, right_side, left_values, right_values):
        Constraint.__init__(self,name, left_side+right_side)
        self._name = "IfAllThenOne_" + name
        self._ls = left_side
        self._rs = right_side
        self._lv = left_values
        self._rv = right_values

