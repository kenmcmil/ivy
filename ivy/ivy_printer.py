from . import ivy_logic
from . import ivy_utils as iu
from . import ivy_actions as ia
from . import ivy_ast

def labeled_fmlas_to_str(kwd,lfmlas):
    res = ''
    for f in lfmlas:
        if f.unprovable:
            res += 'unprovable '
        res += kwd + ' '
        if f.label:
            res += '[{}] '.format(f.label)
        res += str(f.formula) + '\n'
    return res

def print_module(mod,code_only=False):
    print(ivy_logic.sig)
    thing = ''
    if code_only:
        thing += labeled_fmlas_to_str('definition',mod.definitions)
    else: 
        for x,y in mod.schemata.items():
            thing += 'schema [' + x + ']' + str(y) + '\n' 
        for kwd,lst in [('axiom',mod.labeled_axioms),
                        ('property',mod.labeled_props),
                        ('init',mod.labeled_inits),
                        ('invariant',mod.labeled_conjs),
                        ('definition',mod.definitions),
                        ('definition',mod.native_definitions),]:

            thing += labeled_fmlas_to_str(kwd,lst)

    for tn in sorted(mod.sig.interp):
        thing += "interpret {} -> {}\n".format(tn,mod.sig.interp[tn])
    print(thing)

    for name,action in mod.initializers:
        print(iu.pretty("after init {" + str(action) + "}"))

    externed = set(x.externed() for x in mod.externs)
    for x,y in mod.actions.items():
        if x in externed:
            print('extern ' + iu.pretty(ia.action_def_to_str(x,y,body=False)))
        else:
            print(iu.pretty(ia.action_def_to_str(x,y)))

    for x in sorted(mod.public_actions):
        print('export {}'.format(x))

