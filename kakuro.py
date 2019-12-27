from csp import CSP, backtracking_search, mrv, forward_checking, lcv, mac, min_conflicts
import datetime

kakuro1 = [
    ['*', '*', '*', [6, ''], [3, '']],
    ['*', [4, ''], [3, 3], '_', '_'],
    [['', 10], '_', '_', '_', '_'],
    [['', 3], '_', '_', '*', '*']]

kakuro2 = [
    ['*', [10, ''], [13, ''], '*'],
    [['', 3], '_', '_', [13, '']],
    [['', 12], '_', '_', '_'],
    [['', 21], '_', '_', '_']]

kakuro3 = [
    ['*', [17, ''], [28, ''], '*', [42, ''], [22, '']],
    [['', 9], '_', '_', [31, 14], '_', '_'],
    [['', 20], '_', '_', '_', '_', '_'],
    ['*', ['', 30], '_', '_', '_', '_'],
    ['*', [22, 24], '_', '_', '_', '*'],
    [['', 25], '_', '_', '_', '_', [11, '']],
    [['', 20], '_', '_', '_', '_', '_'],
    [['', 14], '_', '_', ['', 17], '_', '_']]

kakuro4 = [
    ['*', '*', '*', '*', '*', [4, ''], [24, ''], [11, ''], '*', '*', '*', [11, ''], [17, ''], '*', '*'],
    ['*', '*', '*', [17, ''], [11, 12], '_', '_', '_', '*', '*', [24, 10], '_', '_', [11, ''], '*'],
    ['*', [4, ''], [16, 26], '_', '_', '_', '_', '_', '*', ['', 20], '_', '_', '_', '_', [16, '']],
    [['', 20], '_', '_', '_', '_', [24, 13], '_', '_', [16, ''], ['', 12], '_', '_', [23, 10], '_', '_'],
    [['', 10], '_', '_', [24, 12], '_', '_', [16, 5], '_', '_', [16, 30], '_', '_', '_', '_', '_'],
    ['*', '*', [3, 26], '_', '_', '_', '_', ['', 12], '_', '_', [4, ''], [16, 14], '_', '_', '*'],
    ['*', ['', 8], '_', '_', ['', 15], '_', '_', [34, 26], '_', '_', '_', '_', '_', '*', '*'],
    ['*', ['', 11], '_', '_', [3, ''], [17, ''], ['', 14], '_', '_', ['', 8], '_', '_', [7, ''], [17, ''], '*'],
    ['*', '*', '*', [23, 10], '_', '_', [3, 9], '_', '_', [4, ''], [23, ''], ['', 13], '_', '_', '*'],
    ['*', '*', [10, 26], '_', '_', '_', '_', '_', ['', 7], '_', '_', [30, 9], '_', '_', '*'],
    ['*', [17, 11], '_', '_', [11, ''], [24, 8], '_', '_', [11, 21], '_', '_', '_', '_', [16, ''], [17, '']],
    [['', 29], '_', '_', '_', '_', '_', ['', 7], '_', '_', [23, 14], '_', '_', [3, 17], '_', '_'],
    [['', 10], '_', '_', [3, 10], '_', '_', '*', ['', 8], '_', '_', [4, 25], '_', '_', '_', '_'],
    ['*', ['', 16], '_', '_', '_', '_', '*', ['', 23], '_', '_', '_', '_', '_', '*', '*'],
    ['*', '*', ['', 6], '_', '_', '*', '*', ['', 15], '_', '_', '_', '*', '*', '*', '*']]

class Kakuro(CSP):
    def __init__(self, puzzle):
        self.puzzle = puzzle
        self.rows = len(self.puzzle)
        self.columns = len(self.puzzle[0])
        self.vars = []
        self.doms = {}
        self.neghbs = {}
        self.sums = []

        for i, row in enumerate(self.puzzle):
            for j, symbol in enumerate(row):
                if symbol == '_':
                    self.vars.append((i, j))
                    self.neghbs[(i, j)] = list()
                elif type(symbol) is list:
                    if symbol[0] != '':
                        tmpList = []
                        x = i + 1
                        while x < self.rows and self.puzzle[x][j] == '_':
                            tmpList.append((x, j))
                            x += 1
                        self.sums.append((symbol[0], (i, j), "top", tmpList))
                    if symbol[1] != '':
                        tmpList = []
                        y = j + 1
                        while y < self.columns and self.puzzle[i][y] == '_':
                            tmpList.append((i, y))
                            y += 1
                        self.sums.append((symbol[1], (i, j), "left", tmpList))

        for var in self.vars:
            self.doms[var] = [i for i in range(1,10)]

        for tally in self.sums:
            numb = len(tally[3])
            maxValue = tally[0] - (numb*(numb-1)/2)
            minValue = tally[0] - ((20-numb)*(numb-1)/2)

            for tile in tally[3]:
                tmpList = []
                for value in self.doms[tile]:
                    if value > maxValue or value < minValue:
                        tmpList.append(value) # removing the value when i find it causes weird behavior
                for value in tmpList: # so i store it and remove it later
                    self.doms[tile].remove(value)

        for tally1 in self.sums:
            for tally2 in self.sums:
                for tile1 in tally1[3]:
                    if tile1 in tally2[3]:
                        for tile2 in tally2[3]:
                            if tile2 not in self.neghbs[tile1] and tile2!=tile1:
                                self.neghbs[tile1].append(tile2)

        CSP.__init__(self, self.vars, self.doms, self.neghbs, self.constraint_handler)


    def constraint_handler(self, var1, value1, var2, value2):

        if(value1 == value2):
            return False

        assignment = self.infer_assignment()
        tmpList = []

        for tally in self.sums:
            if var1 in tally[3]:
                tmpList.append(tally)
            elif var2 in tally[3]:
                tmpList.append(tally)

        for tally in tmpList:
            tmpSum = 0
            notFull = False
            for tile in tally[3]:
                if tile == var1:
                    tmpSum += value1
                elif tile == var2:
                    tmpSum += value2
                elif tile in assignment:
                    tmpSum += assignment[tile]
                else:
                    notFull = True
            if not notFull and tmpSum != tally[0]:
                return False
            elif notFull and tmpSum > tally[0]:
                return False

        return True


    def print_res(self, solved):

        assignment = self.infer_assignment()
        puzzleToString = []

        for i, row in enumerate(self.puzzle):
            puzzleToString.append([])
            for j, symbol in enumerate(row):
                if type(symbol) is list:
                    mStr = "["
                    mStr += ' '.join([str(elem) for elem in symbol])
                    mStr += "]"
                    puzzleToString[i].append(mStr)
                else:
                    if solved and symbol == '_':
                        if (i, j) in assignment:
                            puzzleToString[i].append(str(assignment[(i, j)]))
                    else:
                        puzzleToString[i].append(symbol)

        maxWidth = max([len(item) for row in puzzleToString for item in row])
        for row in puzzleToString:
            print('|'.join(symbol.ljust(maxWidth) for symbol in row))
        print()


def kakuroSolver(puzzle):
    Kakuro(puzzle).print_res(False)

    start = datetime.datetime.now()
    game = Kakuro(puzzle)
    print("Backtracking (BT):")
    backtracking_search(game)
    time = datetime.datetime.now() - start
    print("Assigns made:",game.nassigns)
    print("Time:",time.seconds,"seconds and",time.microseconds,"microseconds")
    game.print_res(True)

    if puzzle!=kakuro4: # Takes too much time to compute!
        start = datetime.datetime.now()
        game = Kakuro(puzzle)
        print("\nBacktracking with minimum residual heuristic (BT+MRV):")
        backtracking_search(game, select_unassigned_variable=mrv)
        time = datetime.datetime.now() - start
        print("Assigns made:",game.nassigns)
        print("Time:",time.seconds,"seconds and",time.microseconds,"microseconds")
        game.print_res(True)

    start = datetime.datetime.now()
    game = Kakuro(puzzle)
    print("\nForward checking (FC):")
    backtracking_search(game, inference=forward_checking)
    time = datetime.datetime.now() - start
    print("Assigns made:",game.nassigns)
    print("Time:",time.seconds,"seconds and",time.microseconds,"microseconds")
    game.print_res(True)

    start = datetime.datetime.now()
    game = Kakuro(puzzle)
    print("\nForward checking with minimum residual heuristic (FC+MRV):")
    backtracking_search(game, inference=forward_checking, select_unassigned_variable=mrv)
    time = datetime.datetime.now() - start
    print("Assigns made:",game.nassigns)
    print("Time:",time.seconds,"seconds and",time.microseconds,"microseconds")
    game.print_res(True)

    start = datetime.datetime.now()
    game = Kakuro(puzzle)
    print("\nMaintaining Arc Consistency (MAX OR AC3):")
    backtracking_search(game, inference=mac)
    time = datetime.datetime.now() - start
    print("Assigns made:",game.nassigns)
    print("Time:",time.seconds,"seconds and",time.microseconds,"microseconds")
    game.print_res(True)
    print()

if __name__== "__main__":

    print("Puzzle1:")
    print("#"*115, "\n")
    kakuroSolver(kakuro1)

    print("Puzzle2:")
    print("#"*115, "\n")
    kakuroSolver(kakuro2)

    print("Puzzle3:")
    print("#"*115, "\n")
    kakuroSolver(kakuro3)

    print("Puzzle4:")
    print("#"*115, "\n")
    kakuroSolver(kakuro4)