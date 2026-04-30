#! /usr/bin/env python
#
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#

from .ivy_init import ivy_init, get_verb
from . import ivy_module
from . import ivy_utils
from . import ivy_trace

def main():
    import signal
    signal.signal(signal.SIGINT,signal.SIG_DFL)

    verbs = ['check','interact','replay']
    verb = get_verb()
    if verb not in verbs:
        print(f'unknown verb: {verb}')
        exit(1)
        
    
    if verb == 'check':
        from . import ivy_check
        ivy_check.main()
        return

    with ivy_module.Module():
        ag = ivy_init(verb=verb)
        if verb == 'interact':
            from .tk_ui import ui_main_loop
            ui_main_loop(ag)
        elif verb == 'replay':
            with ivy_utils.ErrorPrinter():
                print (ag)
            
if __name__ == "__main__":
    main()

