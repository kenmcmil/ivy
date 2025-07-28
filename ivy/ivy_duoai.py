#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

from . import ivy_module as im
from . import ivy_actions as ia
from . import ivy_logic as il
from . import ivy_transrel as tr
from . import ivy_logic_utils as ilu
from . import ivy_utils as iu
from . import ivy_art as art
from . import ivy_interp as itp
from . import ivy_theory as thy
from . import ivy_ast
from . import ivy_proof
from . import ivy_trace
from . import ivy_solver as slvr
from . import ivy_printer

from ivy.z3 import simplify, is_func_decl, DatatypeSortRef
import tempfile
import subprocess
from collections import defaultdict
import itertools
import sys
import os
from contextlib import redirect_stdout
import io

def check_isolate(method="duoai",tagged_dfns=[],use_array_encoding=True):
    mod = im.module

    usorts = []
    usyms = []
    laxs = []
    for sort in il.sig.sorts.values():
        if isinstance(sort,il.EnumeratedSort):
            usort = il.ConstantSort(sort.name)
            usorts.append(usort)
            usortsyms = [il.Symbol(name,usort) for name in sort.extension]
            usyms.extend(usortsyms)
            facts = []
            for i,sym1 in enumerate(usortsyms):
                for sym2 in usortsyms[i+1:]:
                    facts.append(il.Not(il.Equals(sym1,sym2)))
            v = il.Variable('X',usort)
            ax = il.And(il.ForAll([v],il.Or(*[il.Equals(v,y) for y in usortsyms])),
                        il.And(*facts))
            laxs.append(ivy_ast.LabeledFormula(ivy_ast.Atom('ax_' + usort.name),ax))
    mod.labeled_axioms = mod.labeled_axioms + laxs
    mod.schemata = dict()
    mod.definitions = [] # Should have been unfolded by now
    conjs = [x.formula for x in mod.labeled_conjs]
    conj = ivy_ast.LabeledFormula(ivy_ast.Atom('1000000'),il.And(*conjs))
    mod.labeled_conjs = [conj]

    new_actions = dict()
    for name in mod.public_actions:
        act = mod.actions[name]
        def inline(act):
            if isinstance(act,ia.CallAction):
                callee = act.args[0].rep
                v = mod.actions[callee]
                return act.inline(mod,v)
            return act.clone([inline(x) for x in act.args])
        newact = inline(act)
        newact.formal_params = act.formal_params
        newact.formal_returns = act.formal_returns 
        new_actions[name] = newact
    mod.actions = new_actions
                
    new_actions = dict()
    for name,act in mod.actions.items():
        rn = iu.UniqueRenamer()
        def extract_locals(act,syms):
            if isinstance(act,ia.LocalAction):
                subs = dict()
                for sym in act.args[:-1]:
                    newsym = sym.rename(rn)
                    subs[sym] = newsym
                    syms.append(newsym)
                sub = extract_locals(act.args[-1],syms)
                return ilu.rename_ast(sub,subs)
            return act.clone([extract_locals(x,syms) for x in act.args])
        syms = []
        newact = extract_locals(act,syms)
        newact.formal_params = act.formal_params + syms
        newact.formal_returns = act.formal_returns 
        new_actions[name] = newact
    mod.actions = new_actions
    

    new_actions = dict()
    for name,act in mod.actions.items():
        rn = iu.UniqueRenamer()
        def extract_bindolds(act,syms):
            if isinstance(act,ia.BindOldsAction):
                if any(x.name.startswith('old_') for x in ilu.symbols_ast(act)):
                    raise iu.IvyError(act,'cannot translate "old" operator to duai')
                return act.args[0]
            return act.clone([extract_bindolds(x,syms) for x in act.args])
        syms = []
        newact = extract_bindolds(act,syms)
        newact.formal_params = act.formal_params + syms
        newact.formal_returns = act.formal_returns 
        new_actions[name] = newact
    mod.actions = new_actions

    f = io.StringIO()
    with redirect_stdout(f):
        with il.WithSorts(usorts):
            with il.WithSymbols(usyms):
                ivy_printer.print_module(mod)
    f = f.getvalue().replace('. ','%%%').replace('.','_').replace('%%%','. ')
    f = f.replace('prm:','prm_').replace('loc:','loc_').replace('fml:','fml_')
    f = f.replace('ext:','ext_')
    file_name = mod.name + '_duoai.ivy'
    try:
        with open(file_name,'w') as g:
            g.write(f)
    except:
        print (f'failed to write to {file_name}')
        exit(1)
        
