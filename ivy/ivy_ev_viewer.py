
import tkinter as tk
from tkinter import ttk
import os, tkinter.filedialog
from . import ivy_ev_parser as ev
from . import ivy_utils as iu
from . import ivy_ui_util as uu

import signal
signal.signal(signal.SIGINT,signal.SIG_DFL)

Event = ev.Event

class UI(object):
    def __init__(self,tk,root):
        self.tk,self.root = tk,root
                
    def busy(self):
        pass
                
    def ready(self):
        pass

def ask_pat(self,fun,command_label=None):
    global the_ui
    uu.entry_dialog(the_ui.tk,self,"Pattern:",command=lambda s: do_ask_pat(fun,s),command_label=command_label)

def do_ask_pat(fun,pattern):
    global the_ui
    with uu.RunContext(the_ui):
        try:
            pat_evs = ev.parse(pattern)
        except:
            raise iu.IvyError(None,'syntax error')
        fun(pat_evs) 

class EventTree(ttk.Treeview,uu.WithMenuBar):
    DUMMY = '__dummy__'

    def __init__(self,root,notebook,evs):
        uu.WithMenuBar.__init__(self,root)
        ttk.Treeview.__init__(self,root,show='tree')
        self.evs = evs
        self.notebook = notebook
        self._loaded = {''}  # set of iids whose children have been populated
        self._open_callback = None
        self._browse_callback = None
        self.bind('<<TreeviewOpen>>', self._on_open)
        self.bind('<<TreeviewSelect>>', self._on_select)
        for idx,entry in enumerate(evs):
            adddir(self, str(idx) ,entry)

    # Tix Tree['opencmd']/'browsecmd'-style hooks. Keep the existing
    # call-site syntax (tree['opencmd'] = ...) working.
    def __setitem__(self, key, value):
        if key == 'opencmd':
            self._open_callback = value
        elif key == 'browsecmd':
            self._browse_callback = value
        else:
            ttk.Treeview.__setitem__(self, key, value)

    def _on_open(self, event):
        iid = self.focus()
        if self._open_callback is not None:
            self._open_callback(iid)

    def _on_select(self, event):
        sel = self.selection()
        if sel and self._browse_callback is not None:
            self._browse_callback(sel[0])

    def setmode(self, iid, mode):
        # Tix: 'open' means show the (+) indicator. We mimic that by
        # inserting a dummy child so ttk shows the disclosure arrow.
        if mode == 'open':
            dummy = iid + '/' + self.DUMMY
            if not self.exists(dummy):
                self.insert(iid, 'end', iid=dummy)

    def menus(self):
        return [("menu","Events",
                 [("button","Filter...",self.filter),
                  ("button","Find reverse...",self.find_reverse),
                 ],
                ),
               ]

    def filter(self):
        ask_pat(self,self.do_filter,"Filter")

    def do_filter(self,pat_evs):
        result = list(ev.filter(ev.EventGen()(self.evs),pat_evs))
        self.notebook.new_sheet(list(result))

    def find_reverse(self):
        ask_pat(self,self.do_find_reverse,"Find")

    def do_find_reverse(self,pats):
        self.do_find(pats,ev.EventRevGen)

    def do_find_forward(self,pats):
        self.do_find(pats,ev.EventFwdGen)

    def do_find(self,pats,gen):
        sel = self.selection()
        anchor_addr = sel[0] if len(sel) else None
        anchor_ev = lookup(self.evs,anchor_addr) if anchor_addr else None
        res = ev.find(gen(anchor_addr)(self.evs),pats,anchor=anchor_ev)
        if res == None:
            uu.ok_dialog(the_ui.tk,self,'Pattern not found')
            return
        a,e = res
        for s in self.selection():
            self.selection_remove(s)
        self.uncover(a)
        self.selection_set(a)
        self.see(a)

    def uncover(self,addr):
        if '/' in addr:
            cs = addr.rsplit('/',1)
            self.uncover(cs[0])
            opendir(self,cs[0],self.evs)
            self.item(cs[0], open=True)
        
        
class EventNoteBook(ttk.Notebook):
    def __init__(self,root):
        ttk.Notebook.__init__(self,root)
        self.num_sheets = 0
        self.root = root
        self.sheets = {}   # name -> tree widget
        self._tabs = {}    # name -> tab frame
    def new_sheet(self,evs):
        name = "sht{}".format(self.num_sheets)
        tab = ttk.Frame(self)
        self.add(tab, text="Sheet {}".format(self.num_sheets))
        self._tabs[name] = tab
        self.num_sheets += 1
        tree = EventTree(tab,self,evs)
        tree.pack(expand=1, fill=tk.BOTH, padx=10, pady=10, side=tk.LEFT)
        tree['opencmd'] = lambda dir=None, w=tree, t=evs: opendir(w, dir, t)
        tree['browsecmd'] = lambda dir=None, w=tree, t=evs: browsedir(w, dir, t)
        self.sheets[name] = tree
        self.select(tab)
    def busy(self):
        pass
    def ready(self):
        pass
    def current(self):
        selected_path = self.select()
        for name, tab in self._tabs.items():
            if str(tab) == selected_path:
                return self.sheets[name]
        return None

class PatternList(ttk.Frame):
    def __init__(self,root,notebook):
        ttk.Frame.__init__(self,root)
        bbox = ttk.Frame(self)
        bts = [ttk.Button(bbox, text=t, command=c) for t,c in [
            ("<<",self.reverse),
            (">>",self.forward),
            ("+",self.plus),
            ("-",self.minus),]]
        bbox.pack(side=tk.TOP, fill=tk.X)
        for bt in bts:
            bt.pack(side=tk.LEFT, fill=tk.X)
        tlist = tk.Listbox(self)
        tlist.pack(expand=1, fill=tk.BOTH, pady=10, side=tk.TOP)
        bbox = ttk.Frame(self)
        bts = [ttk.Button(bbox, text=t, command=c) for t,c in [
            ("Save",self.save),
            ("Load",self.load),
            ("Clear",self.clear),]]
        bbox.pack(side=tk.TOP, fill=tk.X)
        for bt in bts:
            bt.pack(side=tk.LEFT, fill=tk.X)
        self.tlist = tlist
        self.patlist = []
        self.notebook = notebook

    def reverse(self):
        sel = self.tlist.curselection()
        if len(sel):
            item = int(sel[0])
            self.notebook.current().do_find_reverse(self.patlist[item])

    def forward(self):
        sel = self.tlist.curselection()
        if len(sel):
            item = int(sel[0])
            self.notebook.current().do_find_forward(self.patlist[item])

    def plus(self):
        ask_pat(self,self.do_plus,command_label="Add")

    def do_plus(self,pats):
        self.tlist.insert(tk.END,str(pats))
        self.patlist.append(pats)
        
    def minus(self):
        pass

    def save(self):
        f = tkinter.filedialog.asksaveasfile(mode='w',filetypes=[('event pattern files', '.pats')],title="Save patterns as...",parent=self)
        if f:
            for p in self.patlist:
                f.write('{}\n'.format(p))
            f.close()
                
    def load(self):
        f = tkinter.filedialog.askopenfile(mode='r',filetypes=[('event pattern files', '.pats')],title="Load patterns from...",parent=self)
        if f:
            for pat in f.readlines():
                do_ask_pat(self.do_plus,pat)
                
    def clear(self):
        pass

def RunSample(w,evs):
    top = ttk.Frame(w, relief=tk.RAISED, borderwidth=1)
    global the_ui
    the_ui = UI(w,top)
    notebook = EventNoteBook(top)
    notebook.pack(side=tk.LEFT, fill=tk.BOTH,expand=1)
    notebook.new_sheet(evs)
    pats = PatternList(top,notebook)
    pats.pack(expand=1, fill=tk.BOTH, padx=10, side=tk.LEFT)
    top.pack(side=tk.LEFT, fill=tk.BOTH, expand=1)



def adddir(tree, path, thing):
    text = thing.text()
    parent = path.rsplit('/', 1)[0] if '/' in path else ''
    tree.insert(parent, 'end', iid=path, text=text)
    if thing.subs:
        tree.setmode(path, 'open')

def lookup(things,dir):
    cs = dir.split('/',1)
    thing = things[int(cs[0])]
    res = thing if len(cs) == 1 else lookup(thing.subs,cs[1])
    return res

# This function is called whenever the user presses the (+) indicator or
# double clicks on a directory whose mode is "open". It loads the files
# inside that directory into the Tree widget.
#
# Note we didn't specify the closecmd option for the Tree widget, so it
# performs the default action when the user presses the (-) indicator or
# double clicks on a directory whose mode is "close": hide all of its child
# entries
def opendir(tree, dir, evs):
    if dir in tree._loaded:
        # Already populated. ttk.Treeview keeps children visible across
        # collapse/expand, so there's nothing more to do.
        return
    tree._loaded.add(dir)
    dummy = dir + '/' + tree.DUMMY
    if tree.exists(dummy):
        tree.delete(dummy)
    files = lookup(evs,dir).subs
    for idx,file in enumerate(files):
        adddir(tree, dir + '/' + str(idx),file)

def browsedir(tree, dir, evs):
    pass

def main():
    import sys
    def usage():
        print("usage: \n  {} <file>.iev ".format(sys.argv[0]))
        sys.exit(1)
    if len(sys.argv) != 2:
        usage()
        exit(1)
    fn = sys.argv[1]
    import chardet # $ pip install chardet
    try:
        f = open(fn,'r')
    except:
        print("not found: %s" % fn)
        sys.exit(1)

    with iu.ErrorPrinter():
        with iu.SourceFile(fn):
            s = f.read()
            evs = ev.parse(s)
    root = tk.Tk()
    RunSample(root,evs)
    uu.raise_window(root)
    root.mainloop()

if __name__ == '__main__':
    main()
