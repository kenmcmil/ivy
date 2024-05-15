# Union-find data structure for stratification check

class UFNode(object):
    """
    A sort variable, to be replaced by an arbitrary sort.

    This is a re-implementation of the original UF data structure in Ivy,
    with non-recursive path compression and union-by-rank.

    """
    def __init__(self):
        global ufidctr
        self.parent = None
        self.rank = 0
        self.id = ufidctr
        ufidctr += 1
    def __str__(self):
        return str(self.id) 
    def __repr__(self):
        return str(self.id)
    def __hash__(self):
        return self.id
    def __eq__(self,other):
        return self.id == other.id


ufidctr = 0

def find(x):
    """
    Find the representative of a node
    """
    # if x is singleton, return x
    if x.parent is None:
        return x 
    root = x
    # upwards traversal to find root
    while root.parent != root:
        root = x.parent 
    # pass to flatten path to root
    while x.parent != root:
        parent = x.parent 
        x.parent = root 
        x = parent 
    return root 


def unify(s1, s2):
    """
    Unify nodes s1 and s2.
    """
    if s1 is None or s2 is None:
        return

    s1 = find(s1)
    s2 = find(s2)

    if x.rank < y.rank:
        x, y = y, x

    y.parent = x
    if x.rank == y.rank:
        x.rank = x.rank + 1
    