from z3 import *
import dis

IGNORE_LIST = {"LOAD_GLOBAL", "CALL_FUNCTION", "POP_TOP"}
DEBUG = 0

# EDITABLE - invariants
INVARIANTS = {"_p": {"!= -3"}}
# EDITABLE - core conditions list
CORE_CONDITIONS = {"x": {"!= 0"}}
# EDITABLE - post conditions list
POST_CONDITIONS = {"<= -3"}
# EDITABLE - pre conditions list
PRE_CONDITIONS = {"< 2"}

def to_analyse(_p):
    if _p > 0:
        x = 0
    else:
        x = _p

    return x


def addPreCondition(solver, symbolRetriever):
    # parameter in
    parameterName = "_p"

    for cond in PRE_CONDITIONS:
        assertion = "symbolRetriever[\"" + parameterName + "@0\"] " + cond
        if DEBUG:
            print("preCond: " + assertion)
        solver.add(eval(assertion))


def addPostConditions(solver, symbolRetriever, returnedSymbol):
    for cond in POST_CONDITIONS:
        assertion = returnedSymbol + " " + cond
        if DEBUG:
            print("postCond: " + assertion)
        solver.add(eval(assertion))


def addCoreConditions(solver, symbolRetriever, symbolVersions):
    for symbol in CORE_CONDITIONS.keys():
        for cond in CORE_CONDITIONS[symbol]:
            for i in range(1, symbolVersions[symbol] + 1):
                assertion = "symbolRetriever[\"" + symbol + "@" + str(i) + "\"] " + cond
                if DEBUG:
                    print("coreCond: " + assertion)
                solver.add(eval(assertion))


def addInvariants(solver, symbolRetriever, symbolVersions):
    for symbol in INVARIANTS.keys():
        for cond in INVARIANTS[symbol]:
            for i in range(0, symbolVersions[symbol] + 1):
                assertion = "symbolRetriever[\"" + symbol + "@" + str(i) + "\"] " + cond
                if DEBUG:
                    print("coreCond: " + assertion)
                solver.add(eval(assertion))


def Solve(solver, symbolRetriever, returnedSymbol, symbolVersions):
    print("_____ SOLVER _____")

    addPreCondition(solver, symbolRetriever)
    addCoreConditions(solver, symbolRetriever, symbolVersions)
    addPostConditions(solver, symbolRetriever, returnedSymbol)
    addInvariants(solver, symbolRetriever, symbolVersions)

    isSat = solver.check()

    print("check:")
    print("\t" + str(isSat))
    if str(isSat) == 'sat':
        # print(solver.statistics())
        print("model:")
        print("\t" + str(solver.model()))
    print("assertions:")
    for assertion in solver.assertions():
        print("\t" + str(assertion))


def instructionRetriver(bytecode, offset):
    for instr in bytecode:
        if instr.offset == offset:
            return instr
    return instr


def previousSymbolRetriever(inAirConsts, inAirVariables, inAirBinaryOps, loadOrder):
    loadType = loadOrder.pop()

    if loadType == "LOAD_FAST":
        return "symbolRetriever[\"" + inAirVariables.pop() + "\"]"
    elif loadType == "LOAD_CONST":
        return inAirConsts.pop()
    elif loadType == "BINARY_OP":
        return sequenceSymbolRetriever(inAirConsts, inAirVariables, loadOrder, inAirBinaryOps)
    else:
        raise RuntimeError('Failed to read values')


def sequenceSymbolRetriever(inAirConsts, inAirVariables, loadOrder, inAirBinaryOps):
    opSymbol = inAirBinaryOps.pop()
    loadType = loadOrder.pop()

    if loadType == "LOAD_FAST":
        toReturn = opSymbol + " symbolRetriever[\"" + inAirVariables.pop() + "\"]"
    elif loadType == "LOAD_CONST":
        toReturn = opSymbol + " " + str(inAirConsts.pop())
    else:
        raise RuntimeError('Failed to read values')

    loadType = loadOrder.pop()
    if loadType == "LOAD_FAST":
        toReturn = "symbolRetriever[\"" + inAirVariables.pop() + "\"] " + toReturn
    elif loadType == "LOAD_CONST":
        toReturn = str(inAirConsts.pop()) + " " + toReturn
    elif loadType == "BINARY_OP":
        return sequenceSymbolRetriever(inAirConsts, inAirVariables, loadOrder, inAirBinaryOps) + " " + toReturn
    else:
        raise RuntimeError('Failed to read values')

    return toReturn


def explorer(bytecode,
             offset,
             solver,
             symbolVersions,
             symbolRetriever,
             inAirConsts,
             inAirVariables,
             inAirCompareOps,
             inAirBinaryOps,
             loadOrder):
    instr = instructionRetriver(bytecode, offset)
    if DEBUG:
        print(instr.offset)

    if instr.opname == "RETURN_VALUE":
        # Return 0
        returnedSymbol = previousSymbolRetriever(inAirConsts, inAirVariables, inAirBinaryOps, loadOrder)

        if DEBUG:
            print(symbolVersions)
            print(symbolRetriever)
            print(inAirConsts)
            print(inAirVariables)
            print(inAirCompareOps)
            print(inAirBinaryOps)
            print(loadOrder)
            print("RETURN_VALUE reached!")
        Solve(solver, symbolRetriever, returnedSymbol, symbolVersions)

    else:
        if instr.opname == "LOAD_CONST":
            # stack
            inAirConsts.append(instr.argval)
            loadOrder.append(instr.opname)

        elif instr.opname == "LOAD_FAST":
            if instr.argval not in symbolVersions.keys():
                # version
                symbolVersions[instr.argval] = 0
                # create symbol
                name = str(instr.argval) + "@" + str(symbolVersions[instr.argval])
                symbolRetriever[name] = Int(name)
            # stack
            inAirVariables.append(str(instr.argval) + "@" + str(symbolVersions[instr.argval]))
            loadOrder.append(instr.opname)

        elif instr.opname == "STORE_FAST":
            # version
            if instr.argval in symbolVersions.keys():
                symbolVersions[instr.argval] = symbolVersions[instr.argval] + 1
            else:
                symbolVersions[instr.argval] = 1
            # create symbol
            name = str(instr.argval) + "@" + str(symbolVersions[instr.argval])
            symbolRetriever[name] = Int(name)
            # ___ assertion ___
            previousSymbol = previousSymbolRetriever(inAirConsts, inAirVariables, inAirBinaryOps, loadOrder)
            expressionTrue = "symbolRetriever[\"" + name + "\"] == " + str(previousSymbol)
            if DEBUG:
                print(expressionTrue)
            solver.add(eval(expressionTrue))

        elif instr.opname == "COMPARE_OP":
            # stack
            inAirCompareOps.append(instr.argval)

        elif instr.opname == "BINARY_ADD":
            # stack
            inAirBinaryOps.append("+")
            loadOrder.append("BINARY_OP")

        elif instr.opname == "BINARY_SUBTRACT":
            # stack
            inAirBinaryOps.append("-")
            loadOrder.append("BINARY_OP")

        elif instr.opname == "POP_JUMP_IF_FALSE":
            # ___ assertion ___
            previousSymbolA = previousSymbolRetriever(inAirConsts, inAirVariables, inAirBinaryOps, loadOrder)
            previousSymbolB = previousSymbolRetriever(inAirConsts, inAirVariables, inAirBinaryOps, loadOrder)
            compareOp = inAirCompareOps.pop()

            solverForkB = Solver()
            expressionFalse = "Not(" + str(previousSymbolB) + " " + compareOp + " " + str(previousSymbolA) + ")"
            solverForkB.add(solver.assertions())
            solverForkB.add(eval(expressionFalse))

            solverForkA = Solver()
            expressionTrue = str(previousSymbolB) + " " + compareOp + " " + str(previousSymbolA)
            solverForkA.add(solver.assertions())
            solverForkA.add(eval(expressionTrue))

            if DEBUG:
                print(expressionTrue)
                print(expressionFalse)

            explorer(bytecode,
                     offset + 2,
                     solverForkA,
                     symbolVersions,
                     symbolRetriever,
                     inAirConsts,
                     inAirVariables,
                     inAirCompareOps,
                     inAirBinaryOps,
                     loadOrder)

            explorer(bytecode,
                     instr.argval,
                     solverForkB,
                     symbolVersions,
                     symbolRetriever,
                     inAirConsts,
                     inAirVariables,
                     inAirCompareOps,
                     inAirBinaryOps,
                     loadOrder)

            return

        elif instr.opname == "JUMP_FORWARD":
            explorer(bytecode,
                     instr.argval,
                     solver,
                     symbolVersions,
                     symbolRetriever,
                     inAirConsts,
                     inAirVariables,
                     inAirCompareOps,
                     inAirBinaryOps,
                     loadOrder)
            return

        elif instr.opname not in IGNORE_LIST:
            raise RuntimeError('Failed to read assembly instruction: ' + instr.opname)

        explorer(bytecode,
                 offset + 2,
                 solver,
                 symbolVersions,
                 symbolRetriever,
                 inAirConsts,
                 inAirVariables,
                 inAirCompareOps,
                 inAirBinaryOps,
                 loadOrder)
        return


if __name__ == '__main__':
    solver = Solver()
    dis.dis(to_analyse)
    bytecode = dis.Bytecode(to_analyse)

    explorer(bytecode,
             0,
             solver,
             {},
             {},
             [],
             [],
             [],
             [],
             [])
