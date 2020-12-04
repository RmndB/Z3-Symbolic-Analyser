from z3 import *
import dis


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

    b = a

    if x == 1 and b > 6:
        print("Hello")


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


def previousSymbolRetriever(inAirConsts, inAirVariables, loadOrder):
    loadType = loadOrder.pop()
    if loadType == "LOAD_FAST":
        return "symbolRetriever[\"" + inAirVariables.pop() + "\"]"
    elif loadType == "LOAD_CONST":
        return inAirConsts.pop()
    else:
        raise RuntimeError('Failed to read values')


def Explorater(bytecode,
               offset,
               solver,
               symbolVersions,
               symbolRetriever,
               inAirConsts,
               inAirVariables,
               inAirOps,
               loadOrder):

    instr = instructionRetriver(bytecode, offset)

    print(instr.offset)

    if instr.opname == "RETURN_VALUE":
        print(inAirConsts)
        print(symbolVersions)
        print(inAirVariables)
        print(inAirOps)
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
            previousSymbol = previousSymbolRetriever(inAirConsts, inAirVariables, loadOrder)
            expression = "symbolRetriever[\"" + name + "\"] == " + str(previousSymbol)
            print(expression)
            solver.add(eval(expression))

        elif instr.opname == "COMPARE_OP":
            # stack
            inAirOps.append(instr.argval)

        elif instr.opname == "POP_JUMP_IF_FALSE":
            # ___ assertion ___
            previousSymbolA = previousSymbolRetriever(inAirConsts, inAirVariables, loadOrder)
            previousSymbolB = previousSymbolRetriever(inAirConsts, inAirVariables, loadOrder)
            expression = str(previousSymbolB) + " " + inAirOps.pop() + " " + str(previousSymbolA)
            print(expression)
            solver.add(eval(expression))

        Explorater(bytecode,
                   offset + 2,
                   solver,
                   symbolVersions,
                   symbolRetriever,
                   inAirConsts,
                   inAirVariables,
                   inAirOps,
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
               [])
