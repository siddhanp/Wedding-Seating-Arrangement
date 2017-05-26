import copy
import random


def main():

    global M
    global N
    global NOT
    global OR
    global AND
    global lor


    NOT = "NOT"
    OR = "OR"
    AND = "AND"
    lor = ['OR']

    infile = open("input.txt", "r")
    firstline = infile.readline()
    data = firstline.split()
    M = int(data[0])
    N = int(data[1])

    #print M, N

    flag, allConstraints = constraintList(infile)
    #print allConstraints
    infile.close()


    allNClauses = generateNClauses(allConstraints)
    #for l in range(0, len(allClauses)):
    #    print "CNF", allClauses[l]

    allClauses = generateClauses(allConstraints)
    opfile = open("output.txt", "w")

    if flag == True:
        #print "no"
        opfile.write("no")

    elif M == 0 or N == 0:
        #print "no"
        opfile.write("no")

    else:

        m = dpllSatisfiable(allNClauses)
        if m:
            #print "yes"
            opfile.write("yes"+"\n")

            result, newBooleanValues = walkSAT(allClauses, 0.6, 250)
            for i in range(0, M):
                if i == M - 1:
                    #print i+1, newBooleanValues[i]
                    opfile.write(str(i+1) + " " + str(newBooleanValues[i]))
                else:
                    #print i+1, newBooleanValues[i]
                    opfile.write(str(i+1) + " " + str(newBooleanValues[i])+"\n")
        else:
            #print "no"
            opfile.write("no")

    opfile.close()


def constraintList(infile):

    allConstraints = []
    flag = False
    for line in infile:
        data = line.split()
        allConstraints.append([data[0], data[1], data[2]])
        x = copy.deepcopy(data[0])
        y = copy.deepcopy(data[1])
        if int(x) > M:
            flag = True

        if int(y) > M:
            flag = True

        if x == y:
            flag = True

    return flag, allConstraints

#DPLL

def generateNClauses(allConstraints):

    allClauses = []

    # Constraint: Only one table
    for j in range(0, M):
        temp = []
        for k in range(0, N):
            if k != 0:
                temp.append(OR)
            temp.append("X" + str(j+1) + "X" + str(k+1))
        allClauses.append(temp)

    for j in range(0, M):
        for k in range(0, N):
            for l in range(0, N):
                if k != l and k < l:
                    allClauses.append(["NOTX" + str(j+1) + "X" + str(k+1), OR, "NOTX" + str(j+1) + "X" + str(l+1)])

    # Constraint: Enemies & Friends respectively
    for i in range(0,len(allConstraints)):

        p1 = allConstraints[i][0]
        p2 = allConstraints[i][1]
        relationship = allConstraints[i][2]

        if relationship == 'E':

            for j in range(0, N):
                allClauses.append(["NOTX" + str(p1) + "X" + str(j+1), OR, "NOTX" + str(p2) + "X" + str(j+1)])

        if relationship == 'F':

            for m in range(0, N):
                for n in range(0, N):
                    if m != n:
                        allClauses.append(["NOTX" + str(p1) + "X" + str(m+1), OR, "NOTX" + str(p2) + "X" + str(n+1)])

    return allClauses


def getAllSymbolsWithoutNot(c): #Returns all positive literals

    symbols = []

    for i in range(0, len(c)):
        for j in range(0, len(c[i])):
            if c[i][j] != 'OR' and c[i][j][0] != 'N':
                if c[i][j] not in symbols:
                    symbols.append(c[i][j])
    return symbols


def findPureSymbol(symbols, clauses):

    for c in symbols:
        cp, cn = 0, 0
        for i in range(0, len(clauses)):
            for j in range(0, len(clauses[i])):
                if clauses[i][j] == c:
                    cp = cp + 1
                f = "NOT" + c
                if clauses[i][j] == f:
                    cn = cn + 1

        if cp > 0 and cn > 0:
            return None, None

        elif cp > 0 and cn == 0:
            return c, True

        elif cp == 0 and cn > 0:
            return c, False
        else:
            return None, None


def getSymbol(s):

     if s[0] == 'N':
          return s.split("T")[1]
     else:
          return s


def getBoolean(a):

     if a[0] == 'N':
          return False
     else:
          return True


def findUnitClause(clauses, model):

     #print "findUnitClause"
     #if not bool(model):
     #    return "", True

     for i in range(0, len(clauses)):
          n = 0
          #print clauses[i]
          for j in range(0, len(clauses[i])):
               if clauses[i][j] != 'OR':
                    t = getSymbol(clauses[i][j])
                    #print t, model
                    if t not in model:
                         n = n + 1
                         #print n
                         s, v = t, getBoolean(clauses[i][j])

          if n == 1:
               #print("In here")
               return s, v

     return "", True


def ifSatisfied(clause1, model):


    clause = copy.deepcopy(clause1)

    if OR in clause:
        clause.remove('OR')

    count = 0

    for j in range(0, len(clause)):
        if clause[j] != 'OR':
            if model.get(clause[j]) is True:
                return True
            elif model.get(clause[j]) is False:
                count = count + 1
            elif clause[j][0] == 'N':
                t = clause[j].split('T')
                t = t[1]
                if model.get(t) is False:
                    return True
                elif model.get(t) is True:
                    count = count + 1

    if count == len(clause):
        return False
    else:
        return None


def dpllSatisfiable(allClauses):

    model = dict()
    symbols = getAllSymbolsWithoutNot(allClauses)
    return dpll(allClauses, symbols, model)


def addToDict(c, value, model):

    t = model.copy()
    t[c] = value
    return t


def removeSymbol(symbols, p):

    return [v for v in symbols if v != p]


def dpll(clauses, symbols, model):

    #print symbols
    #print ("*********In DPLL", clauses, model)
    u = []

    for i in range(0, len(clauses)):
        if ifSatisfied(clauses[i], model) is False:
            return False
        if ifSatisfied(clauses[i], model) is not True:
            u.append(clauses[i])

    #print "UNKNOWN##########"
    #for i in range(0, len(u)):
    #    print u[i]

    if not u:
        return True

    #print ("GOING IN PURE SYMBOL", u)
    p, value = findPureSymbol(symbols, u)
    #print ("BACK FROM PURE SYMBOL", p, value)

    if p:
        #print ("Case1")
        return dpll(clauses, removeSymbol(symbols, p), addToDict(p, value, model))

    #print ("GOING IN FIND UNIT CLAUSE", u, model)
    p, value = findUnitClause(u, model)
    #print ("BACK FROM UNIT CLAUSE", p, value)

    if p:
        #print ("Case2")
        return dpll(clauses, removeSymbol(symbols, p), addToDict(p, value, model))

    p = symbols.pop()
    #print "return dpll(clauses, symbols, addToDict(p, True, model)) or dpll(clauses, symbols, addToDict(p, False, model))"
    return dpll(clauses, symbols, addToDict(p, True, model)) or dpll(clauses, symbols, addToDict(p, False, model))




#WALKSAT

def generateClauses(allConstraints):

    allClauses = []

    # Constraint: Only one table
    for j in range(0, M):
        temp = []
        for k in range(0, N):
            if k != 0:
                temp.append(OR)
            temp.append("X" + str(j+1) + "X" + str(k+1))
        allClauses.append(temp)

    for j in range(0, M):
        for k in range(0, N):
            for l in range(0, N):
                if k != l and k < l:
                    allClauses.append([NOT, "X" + str(j+1) + "X" + str(k+1), OR, NOT, "X" + str(j+1) + "X" + str(l+1)])

    # Constraint: Enemies & Friends respectively
    for i in range(0,len(allConstraints)):

        p1 = allConstraints[i][0]
        p2 = allConstraints[i][1]
        relationship = allConstraints[i][2]
        #print p1, p2, relationship

        if relationship == 'E':

            for j in range(0, N):
                #print "Enemy: Different Table"
                #print [NOT, "X" + str(p1) + "X" + str(j+1), OR, NOT, "X" + str(p2) + "X" + str(j+1)]
                allClauses.append([NOT, "X" + str(p1) + "X" + str(j+1), OR, NOT, "X" + str(p2) + "X" + str(j+1)])

        if relationship == 'F':

            for m in range(0, N):
                for n in range(0, N):
                    if m != n:
                        #print "Friend: Same Table"
                        allClauses.append([NOT, "X" + str(p1) + "X" + str(m+1), OR, NOT, "X" + str(p2) + "X" + str(n+1)])
            #for j in range(0, N):
            #    allClauses.append([NOT, "X" + str(p1) + str(j+1), OR, "X" + str(p2) + str(j+1)])
            #    allClauses.append(["X" + str(p1) + str(j+1), OR, NOT, "X" + str(p2) + str(j+1)])

    return allClauses


def getAllSymbols(c):

    symbols = []

    for i in range(0, len(c)):
        for j in range(0, len(c[i])):
            if c[i][j] != 'OR' and c[i][j] != 'AND' and c[i][j] != 'NOT':
                if c[i][j] not in symbols:
                    symbols.append(c[i][j])
    return symbols


def getBooleanValues(s):

    c = [" "] * s
    #print c

    for i in range(0, len(c)):
        c[i] = random.choice([True, False])

    return c


def isSatisfied(c, symbols, values):

    if c[0] == 'NOT' and c[3] == 'NOT':

        if (not values[symbols.index(c[1])]) or (not values[symbols.index(c[4])]): #'NOTX3X1', 'OR', 'NOTX3X2'
            return True
        else:
            return False

    else:

            op = 9
            for k in range(0, len(c) - 1):

                if c[k] in symbols and c[k+1] is OR:
                    a = values[symbols.index(c[k])]
                    k = k + 1
                if op == 9:
                    op = a
                else:
                    op = op or a

            if op == 9:
                return values[symbols.index(c[len(c) - 1])]
            else:
                return op or values[symbols.index(c[len(c) - 1])]


def findBestSymbol(allClauses, symbols, booleanValues, clause):

    #print ("IN FIND BEST SYMBOL")

    maxCount, bestIndex = 0, 0
    #print ("SELECTED CLAUSE", clause)
    for x in range(0, len(booleanValues)):
        if symbols[x] in clause:
            booleanValues[x] = not booleanValues[x]
            count = 0
            #print "FOR", symbols[x]
            for y in range(0, len(allClauses)):

                if isSatisfied(allClauses[y], symbols, booleanValues):
                    #print "SATISFIED", allClauses[y]
                    count = count + 1

            if count > maxCount:
                maxCount = count
                bestIndex = x

            booleanValues[x] = not booleanValues[x]

    return symbols[bestIndex]


def getSymbols(clause):

    m = []
    for i in range(0, len(clause)):
        if clause[i] != OR and clause[i] != NOT:
            m.append(clause[i])

    return m


def findSeating(booleanValues, symbols):

    guests = [" "] * M
    for i in range(0, len(booleanValues)):
        if booleanValues[i]:
            t = symbols[i]
            if guests[int(t.split('X')[1]) - 1] == " ":
                guests[int(t.split('X')[1]) - 1] = t.split('X')[2]

    return guests


def walkSAT(allClauses, p, maxFlips):

    Symbols = getAllSymbols(allClauses)
    #print "ALL SYMBOLS:", Symbols, p, maxFlips

    booleanValues = getBooleanValues(len(Symbols))
    #print booleanValues

    for m in range(0, maxFlips):

        flag = True
        for i in range(0, len(allClauses)):
            #print isSatisfied(allClauses[i], Symbols, booleanValues)
            if not isSatisfied(allClauses[i], Symbols, booleanValues):
                flag = False
                break

        if flag is True:
            #print booleanValues
            return "PASS", findSeating(booleanValues, Symbols)

        falseClauses = []
        for i in range(0, len(allClauses)):
            #print isSatisfied(allClauses[i], Symbols, booleanValues)
            if not isSatisfied(allClauses[i], Symbols, booleanValues):

                #print ("Adding", allClauses[i])
                falseClauses = falseClauses + [allClauses[i]]

        randomClause = falseClauses[random.randint(0, len(falseClauses)-1)]
        #print randomClause

        if random.uniform(0, 1) < p:
            #print random.uniform(0, 1)
            #print("RANDOM SYMBOL")
            symbolList = getSymbols(randomClause)
            randomSymbol = symbolList[random.randint(0, len(symbolList)-1)]
            itemIndex = Symbols.index(randomSymbol)
            booleanValues[itemIndex] = not booleanValues[itemIndex]

        else:
            #print random.uniform(0, 1)
            #print("BEST SYMBOL")
            bestSymbol = findBestSymbol(allClauses, Symbols, booleanValues, randomClause)
            itemIndex = Symbols.index(bestSymbol)
            booleanValues[itemIndex] = not booleanValues[itemIndex]

    return "FAIL", 0

if __name__ == "__main__": main()

#Walksat you need normal clauses, while DPLL needs the NOT appended clauses, you need generate N function for DPLL

