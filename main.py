from z3 import *
import dis

IGNORE_LIST = {"LOAD_GLOBAL", "CALL_FUNCTION", "POP_TOP"}


def dead_code(x, y):
    if x < 3:
        y = 4
    if x > 4:
        y = y + 1
    else:
        x = x + 3
        y = y - 2


def dead_code_z3(solver):
    solver.push()

    x = Int('x')

    solver.add(x < 3)
    solver.add(x > 4)

    Solve(solver)
    solver.pop()


def test(a):
    x = 0

    if a > 0 and a < 5:
        x = 1

    b = a + 3
    # b = a + 3

    if x == 1 and b > 6:
        print("Hello")

    return 0


def Solve(solver):
    isSat = solver.check()

    print(isSat)
    if str(isSat) == 'sat':
        print(solver.statistics())
        print(solver.model())


def instructionRetriver(bytecode, offset):
    for instr in bytecode:
        if instr.offset == offset:
            return instr
    return instr


"""
def Explorater(bytecode, index):
    instr = instructionRetriver(bytecode, index)

    print(instr.offset)

    if instr.opname == "RETURN_VALUE":
        print("RETURN_VALUE reached!")
    else:
        if instr.opname == "POP_JUMP_IF_FALSE":
            Explorater(bytecode, instr.arg)
            Explorater(bytecode, index + 2)
        else:
            Explorater(bytecode, index + 2)
"""


def previousSymbolRetriever(inAirConsts, inAirVariables, inAirBinaryOps, loadOrder):
    loadType = loadOrder.pop()
    if loadType == "LOAD_FAST":
        return "symbolRetriever[\"" + inAirVariables.pop() + "\"]"
    elif loadType == "LOAD_CONST":
        return inAirConsts.pop()
    elif loadType == "BINARY_OP":
        return sequenceSymbolRetriever(inAirConsts, inAirVariables, loadOrder, inAirBinaryOps.pop())
    else:
        raise RuntimeError('Failed to read values')


def sequenceSymbolRetriever(inAirConsts, inAirVariables, loadOrder, opSymbol):
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
    else:
        raise RuntimeError('Failed to read values')

    return toReturn


def Explorater(bytecode,
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

    print(instr.offset)

    if instr.opname == "RETURN_VALUE":
        # Return 0
        loadOrder.pop()
        inAirConsts.pop()

        print(symbolVersions)
        print(symbolRetriever)
        print(inAirConsts)
        print(inAirVariables)
        print(inAirCompareOps)
        print(inAirBinaryOps)
        print(loadOrder)
        print("RETURN_VALUE reached!")
        Solve(solver)

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
                symbolVersions[instr.argval] = 0
            # create symbol
            name = str(instr.argval) + "@" + str(symbolVersions[instr.argval])
            symbolRetriever[name] = Int(name)
            # ___ assertion ___
            previousSymbol = previousSymbolRetriever(inAirConsts, inAirVariables, inAirBinaryOps, loadOrder)
            expression = "symbolRetriever[\"" + name + "\"] == " + str(previousSymbol)
            print(expression)
            solver.add(eval(expression))

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
            expression = str(previousSymbolB) + " " + inAirCompareOps.pop() + " " + str(previousSymbolA)
            print(expression)
            solver.add(eval(expression))

        elif instr.opname not in IGNORE_LIST:
            raise RuntimeError('Failed to read assembly instruction: ' + instr.opname)

        Explorater(bytecode,
                   offset + 2,
                   solver,
                   symbolVersions,
                   symbolRetriever,
                   inAirConsts,
                   inAirVariables,
                   inAirCompareOps,
                   inAirBinaryOps,
                   loadOrder)


if __name__ == '__main__':
    solver = Solver()
    # dead_code_z3(s)
    dis.dis(test)
    bytecode = dis.Bytecode(test)

    Explorater(bytecode,
               0,
               solver,
               {},
               {},
               [],
               [],
               [],
               [],
               [])
