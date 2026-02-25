import pexpect
import os
import sys
import imp
import re

import platform

if platform.system() == 'Windows':
    import pexpect.popen_spawn
    spawn = pexpect.popen_spawn.PopenSpawn
else:
    spawn = pexpect.spawnu

checks = [
    ['.',
      [
          ['modular','OK'],
          ['modular_mc','OK'],
          ['liveness','OK'],
          ['tactic','OK'],
          ['leader_tutorial_without_proof','isolate=abstract_model trace=true','fail call abstract_model.elect'],
          ['leader_tutorial','OK'],
          ['german_bmc_bug','BMC with bound 11 found a counter-example...'],
          ['german_mc_bug','FAIL'],
          ['natural_deduction','OK'],
      ]
    ],
    ['pldi-18',
      [
        ['toy_consensus','OK']
      ]
    ],
    ['pldi-18/multi_paxos',
      [
          ['multi_paxos_system','OK'],
      ],
    ],
    ['cav-18',
      [
          ['german_inv','OK'],
          ['flash_inv','OK'],
          ['tomasulo_inv','OK'],
          ['vs_paxos_inv','OK'],
          ['german_mc','OK'],
          ['flash_mc','OK'],
          ['tomasulo_mc','OK'],
          ['vs_paxos_mc','OK'],
      ]
    ],
    ['liveness',
      [
          ['ticket','OK'],
          ['ticket_nested','OK'],
      ]
    ],
]

tests = [
    ['.',
      [
#          ['token_ring','isolate=token_ring','test_complete']
      ]
     ]
]

repls = [
    ['.',
      [
          ['modular',None],
      ]
     ]
]

to_cpps = [
    ['.',
     [
         ['borrow',''],
     ]
    ],
    ['sigcomm-19',
     [
         ['quic_server_test_max',''],
     ]
    ],
         
]


class Test(object):
    def __init__(self,dir,args):
        self.dir,self.name,self.res,self.opts = dir,args[0],args[-1],args[1:-1]
    def run(self):
        oldcwd = os.getcwd()
        os.chdir(self.dir)
        print('{}/{} ...'.format(self.dir,self.name))
        status = self.run_expect()
        print('PASS' if status else 'FAIL')
        os.chdir(oldcwd)
        return status
    def run_expect(self):
        for pc in self.preprocess_commands():
            print('executing: {}'.format(pc))
            child = spawn(pc)
            child.logfile = sys.stdout
            child.expect(pexpect.EOF)
            child.close()
            if child.exitstatus != 0:
#            if child.wait() != 0:
                print(child.before)
                return False
        return self.expect()
    def expect(self):
        command = self.command()
        print(command)
        child = spawn(command,timeout=1000)
#        print 'timeout = {}'.format(child.timeout)
#        child.logfile = sys.stdout
        try:
            child.expect(self.res)
            return True
        except pexpect.EOF:
            print(child.before)
            return False
    def preprocess_commands(self):
        return []
        
class IvyCheck(Test):
    def command(self):
        import platform
        if platform.system() == 'Windows':
            return 'ivy_check {} {}.ivy'.format(' '.join(self.opts),self.name)
        return 'timeout 1000 ivy_check {} {}.ivy'.format(' '.join(self.opts),self.name)

class IvyTest(Test):
    def command(self):
        import platform
        return './build/'+self.name

    def preprocess_commands(self):
        make_directory_exist('build')
        return ['ivyc target=test '+' '.join(self.opts) + ' '+self.name+'.ivy']

class IvyRepl(Test):
    def command(self):
        return './build/'+self.name
    def preprocess_commands(self):
        make_directory_exist('build')
        return ['ivyc '+' '.join(self.opts) + ' '+self.name+'.ivy']
    def expect(self):
        print('wd:{}'.format(os.getcwd()))
        modname = self.res if self.res != None else (self.name+'_expect')
        mod = imp.load_source(modname,modname+'.py')
        return mod.run('build/'+self.name,self.opts,self.res)
    
class IvyToCpp(Test):
    def command(self):
        res = 'ivyc ' + ' '.join(self.opts) + ' '+self.name+'.ivy'
        print('compiling: {}'.format(res))
        return res

def make_directory_exist(dir):
    if not os.path.exists(dir):
        os.mkdir(dir)

all_tests = []

allpat = re.compile('.*')
test_type = allpat
test_dir = allpat
test_name = allpat

for arg in sys.argv[1:]:
    vals = arg.split('=')
    if len(vals) != 2:
        usage()
    name,val = vals
    if name == 'type':
        test_type = re.compile(val)
    elif name == 'dir':
        test_dir = re.compile(val)
    elif name == 'name':
        test_name = re.compile(val)
    else:
        usage()

def usage():
    print("""usage:
    {} [option...]
options:
    type=<test type pattern>
    dir=<test directory pattern>
    name=<test name pattern>
""".format(sys.argv[0]))
    sys.exit(1)

def get_tests(cls,arr):
    for checkd in arr:
        dir,checkl = checkd
        if test_dir.match(dir):
            for check in checkl:
                if test_name.match(check[0]):
                    all_tests.append(cls(dir,check))

if test_type.match('check'):
    get_tests(IvyCheck,checks)
if test_type.match('test'):
    get_tests(IvyTest,tests)
if test_type.match('repl'):
    get_tests(IvyRepl,repls)
if test_type.match('to_cpp'):
    get_tests(IvyToCpp,to_cpps)

num_failures = 0
for test in all_tests:
    status = test.run()
    if not status:
        num_failures += 1
if num_failures:
    print('error: {} tests(s) failed'.format(num_failures))
else:
    print('OK')

# for checkd in checks:
#     dir,checkl = checkd
#     for check in checkl:
#         name,res = check
#         print '{}/{} ...'.format(dir,name)
#         child = pexpect.spawn('timeout 100 ivy_check {}.ivy'.format(name))
#         try:
#             child.expect(res)
#             print 'PASS'
#         except pexpect.EOF:
#             print child.before
#             print 'FAIL'
        

