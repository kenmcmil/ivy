### check/nocheck theorem names for Ivy.
import yaml

# no check list
_ignores = set()
_assumes = set()

def register_from_file(filename):
    global _ignores 
    global _assumes
    with open(filename, "r") as fd:
        lines = fd.readlines()
    f = "".join(lines)
    y = yaml.load(f, Loader=yaml.CLoader)
    if 'ignores' in y:
        _ignores = set(y['ignores'])
    if 'assumes' in y:
        _assumes = set(y['assumes'])
    print(' +++ IVY_ACL: ignoring property names: ', _ignores)
    print(' +++ IVY_ACL: assuming property names: ', _assumes)

def register(ignores, assumes):
    for x in ignores:
        _ignores.add(x)
    for x in assumes:
        _assumes.add(x)
    print(' +++ IVY_ACL: ignoring property names: ', _ignores)
    print(' +++ IVY_ACL: assuming property names: ', _assumes)


def is_ignored(name):
    if str(name) in _ignores:
        return True 
    return False

def is_assumed(name):
    print('looking up name = ', str(name))
    if str(name) in _assumes:
        return True
    print('... name not in assumed list')
    return False

