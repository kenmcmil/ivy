
import ivy_init
import sys
import json
import platform
import os
import string
import time
import itertools
import subprocess

def usage():
    print "usage: \n {} {{option=value...}} <file>[.dsc]".format(sys.argv[0])
    sys.exit(1)

next_unused_port = 49123

def get_unused_port(protocol):
    global next_unused_port
    next_unused_port += 1
    return next_unused_port

def lookup_ip_addr(hostname):
    return '0x7f000001'

def run_in_terminal(cmd,name):
#    xcmd = "xterm -T '{}' -e '{}'&\n".format(name,cmd+'; read -p "--press enter--"')
#    print xcmd
#    os.system(xcmd)
    args = ["xterm","-fn",'-adobe-courier-bold-r-normal--18-*-*-*-m-*-iso10646-1',"-T",name,"-e", cmd+'; read -p "--press enter--"']
    return subprocess.Popen(args)
    
def read_params():
    ps = dict()
    args = sys.argv[1:]
    while args and '=' in args[0]:
        thing = string.split(args[0],'=')
        if len(thing) > 2:
            usage()
        ps[thing[0]] = thing[1]
        args = args[1:]
    sys.argv = sys.argv[0:1] + args
    return ps

def main():
    ps = read_params()
    have_runs = False
    runs = 1
    if 'runs' in ps:
        runs = int(ps['runs'])
        have_runs = True
        if runs == 0:
            sys.stderr.write("invalid parameter value runs={}".format(ps['runs']))
            sys.exit(1)
        del ps['runs']
    if len(sys.argv) < 2 or len(sys.argv) > 3:
        usage()
    dscfname = sys.argv[1]
    if dscfname.endswith('.ivy'):
        dscfname = dscfname[:-4]
    if not dscfname.endswith('.dsc'):
        dscfname += '.dsc'
    try:
        with open(dscfname) as inp:
            try:
                descriptor = json.load(inp)
            except json.JSONDecodeError as err:
                sys.stderr.write("error in {}: {}".format(dscfname,err.msg))
                sys.exit(1)
    except:
        sys.stderr.write('not found: {}\n'.format(dscfname))
        sys.exit(1)

    hosts = {}
    processes = descriptor['processes']
    for process in processes:
        hosts[process['name']] = 'localhost'

    param_vals = {}

    legal_params = set(p['name'] for p in processes)
    legal_params.update(set(prm['name'] for p in processes for prm in p['params']))
    if 'test_params' in descriptor:
        legal_params.update(descriptor['test_params'])
    for prm in ps:
        if prm not in legal_params:
            print "unknown parameter: {}".format(prm)
            exit(1)
    
    def get_process_dimensions(process):
        pname = process['name']
        if pname in ps:
            try:
                dim = eval(ps[pname],{},{})
            except:
                print "bad argument: {}={}".format(pname,ps[pname])
                exit(1)
            dim = [x if isinstance(x,list) else [x] for x in dim]
        else:
            pparms = process['indices']
            ranges = []
            for p in pparms:
                if 'range' not in p:
                    sys.stderr.write('parameter {} of process {} is not bounded\n'.format(p['name'],pname))
                    sys.exit(1)
                rng = p['range']
                def get_bound(b):
                    if not isinstance(b,int):
                        if b not in ps:
                            sys.stderr.write('need a value on command line for parameter {}\n'.format(b))
                            sys.exit(1)
                        try:
                            b = int(ps[b])
                        except:
                            sys.stderr.write('need an integer value on command line for parameter {}\n'.format(b))
                            sys.exit(1)
                    return b
                rng = map(get_bound,rng)
                ranges.append(list(range(rng[0],rng[1]+1)))
            dim = list(itertools.product(*ranges))
        return dim
    
    for process in processes:
        pname = process['name']
        dim = get_process_dimensions(process)
        pparms = process['indices']
        if not all(len(d) == len(pparms) for d in dim):
            print "wrong number of parameters in instance list for process {}".format(pname)
            exit(1)
        for param in process['params']:
            ptype = param['type']
            type_rng = ptype if not isinstance(ptype,dict) else ptype['name']
            if type_rng == 'udp.endpoint' or type_rng == 'tcp.endpoint' :
                # if param['name'].startswith(pname+'.') or pname == 'extract' or pname == 'this':
                if param['name'] not in param_vals:
                    ids = []
                    pdim = [[]] if not isinstance(ptype,dict) else get_process_dimensions(ptype)
                    for d in pdim:
                        port = get_unused_port('udp')
                        id = '{{addr:{},port:{}}}'.format(lookup_ip_addr(hosts[pname]),port)
                        ids.append(id)
                    if param['name'] in param_vals:
                        sys.stderr.write("endpoint {} is used by multiple processes".format(param['name']))
                        sys.exit(1)
                    param_vals[param['name']] = '"{}"'.format(ids[0] if len(pdim[0]) == 0 else ('[' + ','.join('[' + ','.join(map(str,d)) + ',' + id + ']' for d,id in zip(pdim,ids)) + ']'))
                    
        ps.update(param_vals)

    process_count = 0
    for process in processes:
        dim = get_process_dimensions(process)
        for d in dim:
            process_count += 1


    logfile = dscfname[:-4]+'.log'
    counts = {}
    for run in range(runs):
        popens = []
        for process in processes:
            dim = get_process_dimensions(process)
            for d in dim:
                binary = process['binary']
                cmd = ["`ivy_shell`;",binary if '/' in binary else './' + binary]
                psc = ps.copy()
                for p,v in zip(process['indices'],d):
                    psc[p['name']] = str(v)
                for param in process['params']:
                    if param['name'] in psc:
                        val = psc[param['name']]
                        if 'default' in param:
                            cmd.append('{}={}'.format(param['name'],val))
                        else:
                            cmd.append('{}'.format(val))
                start_seed = 0  # default start seed
                if 'test_params' in descriptor:
                    for param in descriptor['test_params']:
                        if param in ps:
                            if param == 'seed' and have_runs:
                                start_seed = int(ps[param])
                            else:
                                cmd.append('{}={}'.format(param,ps[param]))
                if have_runs:
                    cmd.append("seed={}".format(start_seed + run))
                print ' '.join(cmd)
                pname = process['name']
                if pname == 'this':
                    pname = dscfname[:-4]
                wname = pname + ('('+','.join(map(str,d))+')' if d else '')
                if process_count > 1:
                    popens.append(run_in_terminal(' '.join(cmd),wname))
                    time.sleep(0.5)
                else:
                    if have_runs:
                        with open(logfile,"w") as file:
                            popens.append(subprocess.Popen(' '.join(cmd),shell=True,stdout=file))
                    else:
                        popens.append(subprocess.Popen(' '.join(cmd),shell=True))
                        
        retcodes = []
        for popen in popens:
            retcodes.append(popen.wait())

        if have_runs:
            try :
                with open(logfile) as file:
                    for x in file.readlines():
                        if x.startswith('< '):
                            x = x[2:]
                            if '(' in x:
                                x = x[:x.find('(')]
                            c = counts.get(x,0)
                            counts[x] = c + 1
                with open(logfile,"a") as file:
                    file.write('{}\n'.format(counts))
            except:
                print "error: cannot find log file: {}".format(logfile)
                
        if any(rc != 0 for rc in retcodes):
            if runs > 1:
                sys.stderr.write("test failed. see log in {}\n".format(logfile))
            exit(1)
        
if __name__ == "__main__":
    main()
