#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
#
#  Construct counterexample traces suitable for viewing with the GUI
#

import ivy_solver as islv
import ivy_art as art
import ivy_interp as itp
import ivy_actions as act
import ivy_logic as lg
import ivy_transrel as itr
import ivy_logic_utils as lut
import ivy_utils as iu
import ivy_module as im
import ivy_solver as slv
from collections import defaultdict

################################################################################
#
# Class of traces
#
# A trace is an ARG representing a counterexample
#
# The trace object acts as a handler for match_action (see ivy_actions.py)
# allowing a trace to be constructed from a counterexample.
#
################################################################################

option_detailed = iu.BooleanParameter("detailed",True)

class TraceBase(art.AnalysisGraph):
    def __init__(self):
        art.AnalysisGraph.__init__(self)
        self.last_action = None
        self.sub = None
        self.returned = None
        self.hidden_symbols = lambda sym: False
        self.is_full_trace = False
        
    def is_skolem(self,sym):
        res = itr.is_skolem(sym) and not (sym.name.startswith('__') and sym.name[2:3].isupper())
        # if not res and self.top_level:
        #     name = sym.name
        #     res = name.startswith('loc:') or name.startswith('fml:')
        return res


    def add_state(self,eqns):
        clauses = lut.Clauses(eqns)
        state = self.domain.new_state(clauses)
        univs = self.get_universes()
        if univs is not None:
            state.universe = univs
        if self.last_action is not None:
            expr = itp.action_app(self.last_action,self.states[-1])
            if self.returned is not None:
                expr.subgraph = self.returned
                self.returned = None
            self.last_action = None
            self.add(state,expr)
        else:
            self.add(state)


    def label_from_action(self,action):
        if hasattr(action,'label'):
            return action.label + '\n'
#        lineno = str(action.lineno) if hasattr(action,'lineno') else ''
        return iu.pretty(str(action),max_lines=4)

    def eval_in_state(self,state,param):
        for c in state.clauses.fmlas:
            if c.args[0] == param:
                return c.args[1]
        return None

    def to_lines(self,lines,hash,indent,hidden,failed=False):
        for idx,state in enumerate(self.states):
            if hasattr(state,'expr') and state.expr is not None:
                expr = state.expr
                action = expr.rep
                if option_detailed.get():
                    if not hasattr(action,'label') and hasattr(action,'lineno'):
                        lines.append(str(action.lineno) + '\n')
                    newlines = [indent * '    ' + x + '\n' for x in self.label_from_action(action).split('\n')]
                    lines.extend(newlines)
                else:
                    if isinstance(action,itp.fail_action):
                        if not isinstance(action.action,(act.EnvAction,act.CallAction)):
                            lines.append("{}error: assertion failed\n".format(action.lineno if hasattr(action,'lineno') else ''))
                        else:
                            action = action.action
                            failed=True
                    elif failed and idx == len(self.states) - 1 and isinstance(action,act.AssertAction):
                        lines.append("{}error: assertion failed\n".format(action.lineno if hasattr(action,'lineno') else ''))
                    if isinstance(action,(act.CallAction,act.EnvAction)):
                        if isinstance(action,act.CallAction):
                            callee_name = action.args[0].rep 
                            callee_name = callee_name if any(x.imported() == callee_name for x in im.module.imports) else None
                            callee = im.module.actions.get(callee_name,None)
                            params = callee.formal_params if callee else []
                        else:
                            callee_name = action.args[0].label if hasattr(action.args[0],'label') else None
                            params = action.args[0].formal_params if hasattr(action.args[0],'formal_params') else None
                        if callee_name:
                            callee_state = expr.subgraph.states[0] if hasattr(expr,'subgraph') else state
                            state_hash = dict((x.args[0],x.args[1]) for x in callee_state.clauses.fmlas)
                            def eval_in_state(param):
                                return state_hash.get(param,None)
#                            param_vals = [eval_in_state(callee_state,param) for param in params]
                            arr = '> ' if isinstance(action,act.EnvAction) else '< '
                            lines.append(arr + callee_name
                                         + (('(' + ','.join(value_to_str(eval_in_state(v),eval_in_state) for v in params) + ')') if params else '')
                                         + '\n')
                    if isinstance(action,act.DebugAction):
                        state_hash = dict((x.args[0],x.args[1]) for x in state.clauses.fmlas)
                        def eval_in_state(param):
                            if lg.is_app(param):
                                args = map(eval_in_state,param.args)
                                args = [x if y is None else y for x,y in zip(param.args,args)]
                                param = param.clone(args)
                            return state_hash.get(param,None)
                        def quote(event):
                            if not event.startswith('"'):
                                event = '"' + event + '"'
                            return event
                        def print_expr(expr):    
                            m = {}
                            for v in lut.variables_ast(expr):
                                sym = lg.Symbol('@'+v.name,v.sort)
                                if sym in state_hash:
                                    m[v.name] = state_hash[sym]
                                else:
                                    sym = lg.Symbol('__'+v.name,v.sort)
                                    if sym in state_hash:
                                        m[v.name] = state_hash[sym]
                            expr = lut.substitute_ast(expr,m)
                            return value_to_str(eval_in_state(expr),eval_in_state)
                        event = quote(action.args[0].rep)
                        lines.append("{\n")
                        lines.append('"event" : {}\n'.format(event))
                        for eqn in action.args[1:]:
                            lines.append('{} : {},\n'.format(quote(eqn.args[0].rep),print_expr(eqn.args[1])))
                        lines.append("}\n")
                if hasattr(expr,'subgraph'):
                    if option_detailed.get():
                        lines.append(indent * '    ' + '{\n')
                    expr.subgraph.to_lines(lines,hash,indent+1,hidden,failed=failed)
                    if option_detailed.get():
                        lines.append(indent * '    ' + '}\n')
                if option_detailed.get():
                    lines.append('\n')
            if option_detailed.get():
                foo = False
                if hasattr(state,"loop_start") and state.loop_start:
                    lines.append('\n--- the following repeats infinitely ---\n\n')
                for c in state.clauses.fmlas:
                    if hidden(c.args[0].rep):
                        continue
                    s1,s2 = map(str,c.args)
                    if not(s1 in hash and hash[s1] == s2): # or state is self.states[0]:
                        hash[s1] = s2
                        if not foo:
                            lines.append(indent * '    ' + '[\n')
                            foo = True
                        lines.append((indent+1) * '    ' + str(c) + '\n')
                if foo:
                    lines.append(indent * '    ' + ']\n')
        
    def __str__(self):
        lines = []
        hash = dict()
        self.to_lines(lines,hash,0,self.hidden_symbols)
        return ''.join(lines)

                

    def handle(self,action,env):
#        iu.dbg('env')
        if self.sub is not None:
            self.sub.handle(action,env)
        elif isinstance(self.last_action,(act.CallAction,act.EnvAction)) and self.returned is None:
            self.sub = self.clone()
            self.sub.handle(action,env)
        else:
            if not (hasattr(action,"lineno") and action.lineno.filename == "nowhere"):
                self.new_state(env)
                self.last_action = action

    def do_return(self,action,env):
        if self.sub is not None:
            if self.sub.sub is not None:
                self.sub.do_return(action,env)
            else:
                if isinstance(self.sub.last_action,act.CallAction) and self.sub.returned is None:
                    self.sub.do_return(action,env)
                    return
                self.returned = self.sub
                self.sub = None
                self.returned.new_state(env)
        elif isinstance(self.last_action,act.CallAction) and self.returned is None:
            self.sub = self.clone()
            self.handle(action,env)
            self.do_return(action,env)
            
    def fail(self):
        self.last_action = itp.fail_action(self.last_action)
    def end(self):
        if self.sub is not None: # return from any unfinished calls, due to assertion failure
            self.sub.end()
            self.returned = self.sub
            self.sub = None
        self.final_state()

class Trace(TraceBase):
    def __init__(self,clauses,model,vocab,top_level=True):
        TraceBase.__init__(self)
        self.clauses = clauses
        self.model = model
        self.vocab = vocab
        self.top_level = top_level
        if clauses is not None:
            ignore = lambda s: islv.solver_name(s) == None
            mod_clauses = islv.clauses_model_to_clauses(clauses,model=model,numerals=True,ignore=ignore)
            self.eqs = defaultdict(list)
            for fmla in mod_clauses.fmlas:
                if lg.is_eq(fmla):
                    lhs,rhs = fmla.args
                    if lg.is_app(lhs):
                        self.eqs[lhs.rep].append(fmla)
                elif isinstance(fmla,lg.Not):
                    app = fmla.args[0]
                    if lg.is_app(app):
                        self.eqs[app.rep].append(lg.Equals(app,lg.Or()))
                else:
                    if lg.is_app(fmla):
                        self.eqs[fmla.rep].append(lg.Equals(fmla,lg.And()))

    def clone(self):
        return Trace(self.clauses,self.model,self.vocab,False)

    def get_universes(self):
        return self.model.universes(numerals=True)
        
    def eval(self,cond):
        truth = self.model.eval_to_constant(cond)
        if lg.is_false(truth):
            return False
        elif lg.is_true(truth):
            return True
        assert False,truth
        
    def get_sym_eqs(self,sym):
        return self.eqs[sym]

    def new_state(self,env):
        sym_pairs = []
        for sym in self.vocab:
            if sym not in env and not itr.is_new(sym) and not self.is_skolem(sym):
                sym_pairs.append((sym,sym))
        for sym,renamed_sym in env.iteritems():
            if not itr.is_new(sym) and not self.is_skolem(sym):
                sym_pairs.append((sym,renamed_sym))
        self.new_state_pairs(sym_pairs,env)

    def new_state_pairs(self,sym_pairs,env):
        eqns = []
        for sym,renamed_sym in sym_pairs:
            rmap = {renamed_sym:sym}
            # TODO: what if the renamed symbol is not in the model?
            for fmla in self.get_sym_eqs(renamed_sym):
                rfmla = lut.rename_ast(fmla,rmap)
                eqns.append(rfmla)
        self.add_state(eqns)
                        
    def final_state(self):
        sym_pairs = []
        for sym in self.vocab:
            if not itr.is_new(sym) and not self.is_skolem(sym):
                sym_pairs.append((sym,sym))
        self.new_state_pairs(sym_pairs,{})


def make_check_art(act_name=None,precond=[]):
    action = act.env_action(act_name)

    ag = art.AnalysisGraph()
    
    pre = itp.State()
    pre.clauses = lut.and_clauses(*precond) if precond else lut.true_clauses()
    pre.clauses.annot = act.EmptyAnnotation()
    
    with itp.EvalContext(check=False): # don't check safety
        post = ag.execute(action, pre)
        post.clauses = lut.true_clauses()

    fail = itp.State(expr = itp.fail_expr(post.expr))

    return ag,post,fail

        
def check_final_cond(ag,post,final_cond,rels_to_min=[],shrink=False,handler_class=None):
    history = ag.get_history(post)
    axioms = im.module.background_theory()
    clauses = history.post
    assert clauses.annot is not None
    clauses = lut.and_clauses(clauses,axioms)
    assert all(x is not None for x in history.actions)
    # work around a bug in ivy_interp
    actions = [im.module.actions[a] if isinstance(a,str) else a for a in history.actions]
    action = act.Sequence(*actions)
    return check_vc(clauses,action,final_cond,rels_to_min,shrink,handler_class)

def check_vc(clauses,action,final_cond=None,rels_to_min=[],shrink=False,handler_class=None):
    assert clauses.annot is not None
    model = slv.get_small_model(clauses,lg.uninterpreted_sorts(),rels_to_min,final_cond=final_cond,shrink=shrink)
    if model is not None:
        failed = ([] if final_cond is None
                  else [final_cond] if not isinstance(final_cond,list)
                  else [c.cond() for c in ffcs if c.failed])
        mclauses = lut.and_clauses(*([clauses] + failed))
        vocab = lut.used_symbols_clauses(mclauses)
        handler = (handler_class(mclauses,model,vocab) if handler_class is not None
                   else Trace(mclauses,model,vocab))
        print "Converting model to trace..."
        act.match_annotation(action,clauses.annot,handler)
        handler.end()
        return handler
    return None

# Generate a VC for an action
#
# - action: an action
# - precond: precondition as list of Clauses
# - postcond: postcondition as list of Clauses
# - check_asserts: True if checking asserts in action


def make_vc(action,precond=[],postcond=[],check_asserts=True):

    ag = art.AnalysisGraph()
    
    pre = itp.State()
    pre.clauses = lut.Clauses([lf.formula for lf in precond])
    pre.clauses.annot = act.EmptyAnnotation()
    
    with itp.EvalContext(check=False): # don't check safety
        post = ag.execute(action, pre)
        post.clauses = lut.true_clauses()

    fail = itp.State(expr = itp.fail_expr(post.expr))

    history = ag.get_history(post)
    axioms = im.module.background_theory()
    clauses = history.post

    #Tricky: fix the annotation so it matches the original action
    stack = []
    while isinstance(clauses.annot,act.RenameAnnotation):
        stack.append(clauses.annot.map)
        clauses.annot = clauses.annot.arg
    clauses.annot = clauses.annot.args[1]
    while stack:
        clauses.annot = act.RenameAnnotation(clauses.annot,stack.pop())
    
    clauses = lut.and_clauses(clauses,axioms)
    fc = lut.Clauses([lf.formula for lf in postcond])
    fc.annot = act.EmptyAnnotation()
    used_names = frozenset(x.name for x in lg.sig.symbols.values())
    def witness(v):
        c = lg.Symbol('@' + v.name, v.sort)
        assert c.name not in used_names
        return c
    fcc = lut.dual_clauses(fc, witness)
    clauses = lut.and_clauses(clauses,fcc)

    return clauses


# Converting values to strings for trace display

def value_to_str(val,eval_in_state):
    if val is None:
        return '...'
    if lg.is_constant(val):
        sort = val.sort
        end = lg.sig.symbols.get(iu.compose_names(sort.name,'end'),None)
        value = lg.sig.symbols.get(iu.compose_names(sort.name,'value'),None)
        if  isinstance(end,lg.Symbol) and isinstance(value,lg.Symbol):
            dom = end.sort.dom
            vdom = value.sort.dom
            if len(dom) == 1 and dom[0] == sort and len(vdom) == 2 and vdom[0] == sort and vdom[1] == end.sort.rng:
                endval = eval_in_state(end(val))
                if endval is not None and lg.is_constant(endval) and endval.is_numeral():
                    endvalnum = int(endval.name)
                    indices = [lg.Symbol(str(i),endval.sort) for i in range(endvalnum)]
                    vals = [eval_in_state(value(val,idx)) for idx in indices]
                    return '[' + ','.join(value_to_str(v,eval_in_state) for v in vals) + ']'
        if sort.name in im.module.sort_destructors:
            destrs = im.module.sort_destructors[sort.name]
            vals = [value_to_str(eval_in_state(destr(val)),eval_in_state) if len(destr.sort.dom) == 1 else '...' for destr in destrs]
            return '{' + ','.join(destr.name + ':' + val for destr,val in zip(destrs,vals)) + '}'
        return val.rep.name
    return str(val) 
