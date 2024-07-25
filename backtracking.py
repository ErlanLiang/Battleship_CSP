from csp import Constraint, Variable, CSP
from constraints import *
import random

class UnassignedVars:
    '''class for holding the unassigned variables of a CSP. We can extract
       from, re-initialize it, and return variables to it.  Object is
       initialized by passing a select_criteria (to determine the
       order variables are extracted) and the CSP object.

       select_criteria = ['random', 'fixed', 'mrv'] with
       'random' == select a random unassigned variable
       'fixed'  == follow the ordering of the CSP variables (i.e.,
                   csp.variables()[0] before csp.variables()[1]
       'mrv'    == select the variable with minimum values in its current domain
                   break ties by the ordering in the CSP variables.
    '''
    def __init__(self, select_criteria, csp):
        if select_criteria not in ['random', 'fixed', 'mrv']:
            pass #print "Error UnassignedVars given an illegal selection criteria {}. Must be one of 'random', 'stack', 'queue', or 'mrv'".format(select_criteria)
        self.unassigned = list(csp.variables())
        self.csp = csp
        self._select = select_criteria
        if select_criteria == 'fixed':
            #reverse unassigned list so that we can add and extract from the back
            self.unassigned.reverse()

    def extract(self):
        if not self.unassigned:
            pass #print "Warning, extracting from empty unassigned list"
            return None
        if self._select == 'random':
            i = random.randint(0,len(self.unassigned)-1)
            nxtvar = self.unassigned[i]
            self.unassigned[i] = self.unassigned[-1]
            self.unassigned.pop()
            return nxtvar
        if self._select == 'fixed':
            return self.unassigned.pop()
        if self._select == 'mrv':
            nxtvar = min(self.unassigned, key=lambda v: v.curDomainSize())
            self.unassigned.remove(nxtvar)
            return nxtvar

    def empty(self):
        return len(self.unassigned) == 0

    def insert(self, var):
        if not var in self.csp.variables():
            pass #print "Error, trying to insert variable {} in unassigned that is not in the CSP problem".format(var.name())
        else:
            self.unassigned.append(var)

def bt_search(algo, csp, variableHeuristic, allSolutions, trace):
    '''Main interface routine for calling different forms of backtracking search
       algorithm is one of ['BT', 'FC', 'GAC']
       csp is a CSP object specifying the csp problem to solve
       variableHeuristic is one of ['random', 'fixed', 'mrv']
       allSolutions True or False. True means we want to find all solutions.
       trace True of False. True means turn on tracing of the algorithm

       bt_search returns a list of solutions. Each solution is itself a list
       of pairs (var, value). Where var is a Variable object, and value is
       a value from its domain.
    '''
    varHeuristics = ['random', 'fixed', 'mrv']
    algorithms = ['BT', 'FC', 'GAC']

    #statistics
    bt_search.nodesExplored = 0

    if variableHeuristic not in varHeuristics:
        pass #print "Error. Unknown variable heursitics {}. Must be one of {}.".format(
            #variableHeuristic, varHeuristics)
    if algo not in algorithms:
        pass #print "Error. Unknown algorithm heursitics {}. Must be one of {}.".format(
            #algo, algorithms)

    uv = UnassignedVars(variableHeuristic,csp)
    Variable.clearUndoDict()
    for v in csp.variables():
        v.reset()
    if algo == 'BT':
         solutions = BT(uv, csp, allSolutions, trace)
    elif algo == 'FC':
        for cnstr in csp.constraints():
            if cnstr.arity() == 1:
                FCCheck(cnstr, None, None)  #FC with unary constraints at the root
        solutions = FC(uv, csp, allSolutions, trace)
    elif algo == 'GAC':
        GacEnforce(csp.constraints(), csp, None, None) #GAC at the root
        solutions = GAC(uv, csp, allSolutions, trace)

    return solutions, bt_search.nodesExplored

def GAC(unAssignedVars, csp, allSolutions, trace):
    '''
    GAC Search. unAssignedVars is the current set of unassigned variables.'''
    if unAssignedVars.empty():
        sol = []
        for v in csp.variables():
            # print(v.name(), ": ", v.getValue())
            sol.append((v, v.getValue()))
        return [sol] #each call returns a list of solutions found
    sols = []
    v = unAssignedVars.extract()
    for val in v.curDomain():
        v.setValue(val)
        noDWO = True
        if GacEnforce(csp.constraintsOf(v), csp, v, val) == "DWO":
            noDWO = False
        if noDWO:
            new_sol = GAC(unAssignedVars, csp, allSolutions, trace)
            if new_sol:
                sols.extend(new_sol)
        #restore values pruned by var = val assignment
        v.restoreValues(v, val)
    v.unAssign()
    unAssignedVars.insert(v)
    return sols

def GacEnforce(constraints, csp, var, val):
    '''Enforce GAC on all active constraints of var.  If var is None
       then enforce GAC on all constraints of the csp.  If var is
       assigned then enforce GAC on all constraints containing var.
       If var is unassigned then enforce GAC on all constraints containing var
       and possibly other unassigned variables.  val is the value being
       assigned to var.  If var is None then val is ignored.  Returns
       False if a DWO is detected, True otherwise.  If trace is True
       then print out the changes to the variable domains.'''
    while constraints:
        c = constraints.pop()
        for cur_var in c.scope():
            # print("cur_var: ", cur_var)
            # print("cur_var.curDomain(): ", cur_var.curDomain())
            for cur_val in cur_var.curDomain():
                # print("cur_val: ", cur_val)
                if not c.hasSupport(cur_var, cur_val):
                    cur_var.pruneValue(cur_val, var, val)
                    if cur_var.curDomainSize() == 0:
                        return "DWO"
                    for recheck in csp.constraintsOf(cur_var):
                        if recheck != c and recheck not in constraints:
                            csp.constraintsOf(cur_var).append(recheck)
    return "OK"

def BT(unAssignedVars, csp, allSolutions, trace):
    '''Backtracking Search. unAssignedVars is the current set of
       unassigned variables.  csp is the csp problem, allSolutions is
       True if you want all solutionss trace if you want some tracing
       of variable assignments tried and constraints failed. Returns
       the set of solutions found.

      To handle finding 'allSolutions', at every stage we collect
      up the solutions returned by the recursive  calls, and
      then return a list of all of them.

      If we are only looking for one solution we stop trying
      further values of the variable currently being tri  ed as
      soon as one of the recursive calls returns some solutions.
    '''
    if unAssignedVars.empty():
        if trace: pass #print "{} Solution Found".format(csp.name())
        soln = []
        for v in csp.variables():
            soln.append((v, v.getValue()))
        return [soln]  #each call returns a list of solutions found
    bt_search.nodesExplored += 1
    solns = []         #so far we have no solutions recursive calls
    nxtvar = unAssignedVars.extract()
    if trace: pass #print "==>Trying {}".format(nxtvar.name())
    for val in nxtvar.domain():
        if trace: pass #print "==> {} = {}".format(nxtvar.name(), val)
        nxtvar.setValue(val)
        # add the WaterAroundShipConstraint to the csp if the variable is a ship(not 0)
        #TODO: add the constraint
        constraintsOK = True
        if val == 1:
            # check top left right bottom to see if there is a ship
            # if there is a ship, add the variable to the constraint
            # print("in")
            if not check_ships(csp, nxtvar, csp.size):
                constraintsOK = False
                print("got")

       
        if constraintsOK:
            for cnstr in csp.constraintsOf(nxtvar):
                # print("cnstr: ", cnstr)
                # i`f type(cnstr) == WaterAroundShipConstraint:
                #     print("in")`
                if cnstr.numUnassigned() == 0:
                    if not cnstr.check():
                        # print("falsified constraint")
                        constraintsOK = False
                        if trace: pass #print "<==falsified constraint\n"
                        break
            if constraintsOK:
                new_solns = BT(unAssignedVars, csp, allSolutions, trace)
                if new_solns:
                    solns.extend(new_solns)
                if len(solns) > 0 and not allSolutions:
                    break  #don't bother with other values of nxtvar
                        #as we found a soln.
    
    nxtvar.unAssign()
    unAssignedVars.insert(nxtvar)
    return solns

def check_ships(csp, var, size):
    # check top left right bottom to see if there is a ship
    # if there is a ship, add the variable to the constraint
    num = int(var.name())
    top = num + size
    bottom = num - size
    left = num + 1
    right = num - 1

    has_top = str(top) in csp.ship_con
    has_bottom = str(bottom) in csp.ship_con
    has_left = str(left) in csp.ship_con
    has_right = str(right) in csp.ship_con

    if (has_top or has_bottom) and (has_left or has_right):
        return False
    # elif has_top and has_bottom:
    #     # if len(csp.ship_con[str(top)].scope()) + len(csp.ship_con[str(bottom)].scope()) + 1 > 4:
    #     #     return False
    #     csp.vertical.add(top)
    #     csp.vertical.add(bottom)
    # elif has_left and has_right:
    #     # if len(csp.ship_con[str(left)].scope()) + len(csp.ship_con[str(right)].scope()) + 1 > 4:
    #     #     return False
    #     csp.horizontal.add(left)
    #     csp.horizontal.add(right)
    return True
    

