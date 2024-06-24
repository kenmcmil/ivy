### check/nocheck theorem names for Ivy.
import yaml
import re
from . import ivy_utils as iu

# no check list
_ignores = set()
_ignores_regex = None
_assumes = set()
_assumes_regex = None


def append_r(x, acc):
    assert x[-1] == ')'
    regex_str = x[6:-1]
    if acc=='':
        return regex_str
    return acc + '|' + regex_str


def register_ignores(ign_list):
    global _ignores
    global _ignores_regex
    ignores_regex_acc=''
    ignores_list = []
    for x in ign_list:
        if x.startswith('regex('):
            ignores_regex_acc=append_r(x, ignores_regex_acc)
        else:
            ignores_list.append(x)
    _ignores = set(ignores_list)
    try: 
        if ignores_regex_acc!='':
            _ignores_regex = re.compile(ignores_regex_acc)
    except:
        raise iu.IvyError('invalid regex encountered when parsing unchecked assertions YAML file. ') 

def register_assumes(ass_list):
    global _assumes
    global _assumes_regex
    assumes_list = []
    assumes_regex_acc=''
    for x in ass_list:
        if x.startswith('regex('):
            assumes_regex_acc=append_r(x, assumes_regex_acc)
        else:
            assumes_list.append(x)
    _assumes = set(assumes_list)
    try:
        if assumes_regex_acc!='':
            _assumes_regex = re.compile(assumes_regex_acc)
    except:
        raise iu.IvyError('invalid regex encountered when parsing unchecked assertions YAML file. ')

def register_from_file(filename):
    global _ignores
    global _assumes
    global _ignores_regex
    global _assumes_regex
    with open(filename, "r") as fd:
        lines = fd.readlines()
    f = "".join(lines)
    y = yaml.load(f, Loader=yaml.CLoader)
    if y == None:
        return # XXX: pyyaml returns a 'None' object on empty YAML files
    if 'ignores' in y:
        ign_list = list(y['ignores'])
        register_ignores(ign_list)
    if 'assumes' in y:
        ass_list = list(y['assumes'])
        register_assumes(ass_list)

def register(ignores, assumes):
    global _ignores
    global _assumes
    global _ignores_regex
    global _assumes_regex
    register_ignores(ignores)
    register_assumes(assumes)

def get_ignores_list():
    return _ignores

def get_assumes_list():
    return _assumes

def get_ignores_regex():
    return _ignores_regex

def get_assumes_regex():
    return _assumes_regex

def is_ignored(name):
    global _ignores_regex
    global _ignores
    if str(name) in _ignores:
        return True 
    elif _ignores_regex != None and _ignores_regex.match(str(name)) != None:
        return True
    return False

def is_assumed(name):
    global _assumes_regex
    global _assumes
    if str(name) in _assumes:
        return True
    elif _assumes_regex != None and _assumes_regex.match(str(name)) != None:
        return True
    return False


