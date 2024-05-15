### tests for Union-Find v2 data structure
import test_base
import time
import ivy_union_find2 as uf 

from random import randint as ri

N = ri(10, 100)
M = ri(1000, 2000)


# congruence closure
CC = {}

klasses = [uf.UFNode() for x in range(N)]
for x in range(N):
    CC[x] = []

t_start = time.time()

print('testing UF on ', N, ' nodes')
print('  we will have ', M, ' unions and queries')


for y in range(M):
    i = ri(0, N-1)
    j = ri(0, N-1)
    print(' union of ', i, ' and ', j, '...')
    uf.unify(klasses[i], klasses[j])
    CC[i].append(j)
    CC[j].append(i)
    assert uf.find(klasses[i]) == uf.find(klasses[j])
    print('                  ...passed')

print('Generating offline queries on congruence closure graph')
K = ri(300, 500)
print(' # queries = ', K)
for x in range(K):
    # arbitrarily pick a node
    i = ri(0, N-1)
    j = i
    print(' checking CC of node ', i, '  #neighbors=', len(CC[i]))
    # try and verify some neighbors in the CC
    going = len(CC[i]) > 0
    while going:
        k = CC[j][ri(0, len(CC[j]) - 1)]
        print('   checking node ', k, ' in CC of node ', i)
        assert uf.find(klasses[k]) == uf.find(klasses[j])
        assert uf.find(klasses[i]) == uf.find(klasses[j])
        assert uf.find(klasses[i]) == uf.find(klasses[k])
        j = k
        going = (ri(0, 3) != 0)
    print(' ...check passed')


t_end = time.time()
print('elapsed time: ', t_end - t_start, ' (s)')

