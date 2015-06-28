import sys
import os
import re
from collections import Counter, defaultdict


def module_name(x):
    if 'theories/' in x:
        y = re.sub(r'^.*theories/','', x)
        y = re.sub(r'/','.', y)
        return y
    else:
        return os.path.basename(x)


def draw (graph, sort, fd):
    fd.write('digraph {')
    for x in graph:
        for y in graph[x]:
            fd.write('"{0}" -> "{1}";\n'.format(x,y))
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

def reverse(graph): 
    result = defaultdict(set)
    for x in graph: 
        for son in graph[x]:
            result[son].add(x)
    return result

def remove(graph, starts):
    rev_graph = reverse(graph)
    removed = list()
    while starts :
        current = starts.pop()
        if current in graph:
            for son in rev_graph[current]:
              starts.append(son)
            del graph[current]
            removed.append(current)
      

output = './graph.dot'
fd = open(output, 'w')

graph = defaultdict(list)

for line in sys.stdin.readlines():
  line_splitted = line.split(':')
  targets, needs = line_splitted[0].split(), line_splitted[1].split()
  targets = list (os.path.splitext(x)[0] for x in targets if x.endswith('.vo'))

  needs = list (os.path.splitext(x)[0] for x in needs if x.endswith('.vo') or x.endswith('.v'))

  for x in targets:
      graph[x].extend(y for y in needs if x <> y)


if len(sys.argv) >= 2:
    removed_nodes = list(os.path.splitext(x)[0] for x in sys.argv[1:])
    remove(graph, removed_nodes)

init = list(x for x in list(graph) if 'Init/' in x)
for x in list(graph) : 
    if not (x in init) : 
        graph[x].extend(init)
start = list(graph)
reduction = transitive_reduction(graph, start)
sort = topological_sort(graph, start)
draw(reduction, sort, fd)
sort = map(module_name, sort)
def aliasing(l):
    done = defaultdict(int)
    result = []
    for x in l:
        basename = re.sub(r'^.*\.','', x)
        done[basename]+=1
        if done[basename] > 1:
            result.append('{0}-{1}{2}_R'.format(x, basename, done[basename]))
        else:
            result.append(x)
    return result
    
sort = aliasing(sort)
print(' '.join(sort))
