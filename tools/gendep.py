import sys
import os
from collections import Counter, defaultdict



def draw (graph, sort, fd):
    fd.write('digraph {')
    for x in graph:
        for y in graph[x]:
            fd.write('"{0}" -> "{1}";'.format(x,y))
    if sort:
        prev = sort[0]
        for x in sort[1:]:
            fd.write('"{0}" -> "{1}" [constraint=false color=red];'.format(prev,x))
            prev = x
    
    fd.write('}')


def transitive_reduction(graph, start):
    aux = defaultdict(Counter)
    result = defaultdict(list)

    waiting = list(start)
    visited = list()

    while waiting:
        x = waiting[-1]
        if not (x in visited):
            sons = graph[x]
            all_son_visited = True
            for son in sons:
                if not (son in visited):
                    all_son_visited = False
            if all_son_visited:
                aux[x].update(sons)
                for son in sons:
                    if son <> x:
                        aux[x].update(aux[son])
                        aux[x].update(aux[son])
                waiting.pop()
                visited.append(x)
            else : 
                waiting.extend(graph[x])
        else : 
            waiting.pop()

    for x in aux:
        deps = list(k for k in aux[x] if aux[x][k] == 1)
        result[x] = deps
    return result

def topological_sort(graph, start):
    def aux (fullfilled, position):
        if not position in fullfilled:
            for son in graph[position]:
                aux(fullfilled, son)
            fullfilled.append(position)
    result = list()
    for x in start:
        aux (result, x)
    return result

output = './output.dot'
fd = open(output, 'w')

graph = defaultdict(list)

for line in sys.stdin.readlines():
  line_splitted = line.split(':')
  targets, needs = line_splitted[0].split(), line_splitted[1].split()
  targets = list (os.path.splitext(x)[0] for x in targets if x.endswith('.vo'))

  needs = list (os.path.splitext(x)[0] for x in needs if x.endswith('.vo') or x.endswith('.v'))

  for x in targets:
      graph[x].extend(y for y in needs if x <> y)

if len(sys.argv) == 2:
    start = sys.argv[1:] 
else :
    start = list(graph)

reduction = transitive_reduction(graph, start)
sort = topological_sort(graph, start)
draw(reduction, sort, fd)
print(' '.join(os.path.basename(x) for x in sort))

