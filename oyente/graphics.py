from collections import defaultdict


class Graph:
    def __init__(self):
        self.edgeSet = set()
        self.verticeSet = set()
        self.graph = defaultdict(list)

    def updateState(self):
        self.verticeSet.clear()
        self.graph.clear()
        for e in self.edgeSet:
            self.verticeSet.update(set(e))
            # self.graph.update({e[0]: [e[1]]})
            self.graph[e[0]].append(e[1])

    def addEdge(self, edge):
        if edge not in self.edgeSet:
            self.edgeSet.add(edge)
            self.updateState()
            # self.graph[edge[0]].append(edge[1])

    def removeEdge(self, edge):
        if edge in self.edgeSet:
            self.edgeSet.remove(edge)
            self.updateState()
            # self.graph[edge[0]].remove(edge[1])

    def size(self):
        return len(self.verticeSet)

    def isCyclicUtil(self, v, visited, recStack):
        visited.update({v: True})
        recStack.update({v: True})

        for neighbour in self.graph[v]:
            if not visited[neighbour]:
                if self.isCyclicUtil(neighbour, visited, recStack):
                    return True
            elif recStack[neighbour]:
                return True

        recStack[v] = False
        return False

    def isCyclic(self):
        visited = defaultdict(bool)
        recStack = defaultdict(bool)
        for node in self.verticeSet:
            if not visited[node]:
                if self.isCyclicUtil(node, visited, recStack):
                    return True
        return False

    def copy(self):
        tmp = Graph()
        tmp.graph = self.graph.copy()
        tmp.edgeSet = self.edgeSet.copy()
        tmp.verticeSet = self.verticeSet.copy()
        return tmp

