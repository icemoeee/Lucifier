CONSTANT_PUSH = '-*-PUSH*-*'
CONSTANT_POP = '*-*POP-*-'


class solverstack:
    def __init__(self):
        self.stack = []

    def add(self, formula):
        self.stack.append(formula)

    def push(self):
        self.stack.append(CONSTANT_PUSH)

    def pop(self):
        if self.stack.count(CONSTANT_PUSH) != 0:
            stacklen = len(self.stack)
            index = stacklen - 1 - self.stack[::-1].index(CONSTANT_PUSH)
            self.stack = self.stack[:index]

    def getstack(self):
        realstack = self.stack.copy()
        while realstack.count(CONSTANT_PUSH) != 0:
            realstack.remove(CONSTANT_PUSH)
        return realstack
    