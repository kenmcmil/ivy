# Regression test runner.
#
# Tests are described by `ivy_tests.py` files placed in the example
# directories. This script walks the tree (from the repository root by
# default), collects the tests declared in every `ivy_tests.py`, and runs the
# ones selected on the command line.
#
# Each `ivy_tests.py` defines a list `tests` of dictionaries, and optionally a
# dict `defaults` whose entries are applied to every test in that file unless
# the test overrides them. Each test dictionary has:
#
#     type     one of: check, test, repl, to_cpp, ivyc_test, ivyc_repl, ivyc,
#              to_rtl
#     name     the base name of the .ivy file (no extension)
#     args     (optional) list of command-line options passed to the tool
#     expect   the pattern (regex) expected in the output; for the repl
#              types it is instead the name of the expect module, or omitted
#              (None) to use "<name>_expect"
#     validate (to_rtl only, optional) a shell command run after a successful
#              translation; the test passes iff it exits 0. The token {name}
#              is replaced by the test's base name (so it can refer to
#              <name>.il).
#     timeout  (optional) seconds allowed for the test (default 100)
#     group    (optional) a label for selecting the test (default 'normal').
#              For example, 'long' for a slow test or 'unreliable' for one
#              that is expected to fail intermittently.
#
# Command-line options (all values are regular expressions, matched anywhere):
#
#     type=<pat>   select tests whose type matches
#     dir=<pat>    select tests whose directory (relative to root) matches
#     name=<pat>   select tests whose name matches
#     group=<pat>  select tests whose group matches (default: ^normal$, so
#                  non-'normal' groups are skipped unless requested)
#     root=<path>  directory to search (default: the repository root)
#     list         just list the selected tests; do not run them

import pexpect
import os
import sys
import re
import platform
import importlib.util

if platform.system() == 'Windows':
    import pexpect.popen_spawn
    spawn = pexpect.popen_spawn.PopenSpawn
else:
    spawn = pexpect.spawnu

DEFAULT_TIMEOUT = 100


# ----------------------------------------------------------------------------
# Test classes

class Test(object):
    def __init__(self, dir, spec):
        self.dir = dir
        self.type = spec['type']
        self.name = spec['name']
        self.opts = spec.get('args', [])
        self.res = spec.get('expect')       # regex, or (repl) module name / None
        self.timeout = spec.get('timeout', DEFAULT_TIMEOUT)
        self.group = spec.get('group', 'normal')

    def run(self):
        oldcwd = os.getcwd()
        os.chdir(self.dir)
        print('{} [{}] {} ...'.format(self.reldir(), self.type, self.name))
        try:
            status = self.run_expect()
        finally:
            os.chdir(oldcwd)
        print('PASS' if status else 'FAIL')
        return status

    def reldir(self):
        return getattr(self, 'rel', self.dir)

    def run_expect(self):
        for pc in self.preprocess_commands():
            print('executing: {}'.format(pc))
            child = spawn(pc, timeout=self.timeout)
            child.logfile = sys.stdout
            child.expect(pexpect.EOF)
            child.close()
            if child.exitstatus != 0:
                print(child.before)
                return False
        return self.expect()

    def expect(self):
        command = self.command()
        print(command)
        child = spawn(command, timeout=self.timeout)
        try:
            child.expect(self.res)
            return True
        except (pexpect.EOF, pexpect.TIMEOUT):
            print(child.before)
            return False

    def preprocess_commands(self):
        return []


class IvyCheck(Test):
    def command(self):
        if platform.system() == 'Windows':
            return 'ivy_check {} {}.ivy'.format(' '.join(self.opts), self.name)
        return 'timeout {} ivy_check {} {}.ivy'.format(
            self.timeout, ' '.join(self.opts), self.name)


# --- ivy_to_cpp-based tests ---

class IvyTest(Test):
    def preprocess_commands(self):
        make_directory_exist('build')
        return ['ivy_to_cpp target=test build=true {} {}.ivy'.format(
            ' '.join(self.opts), self.name)]
    def command(self):
        return '/bin/bash -c "`ivy_shell`; ./build/{}"'.format(self.name)

class IvyRepl(Test):
    def preprocess_commands(self):
        make_directory_exist('build')
        return ['ivy_to_cpp target=repl build=true {} {}.ivy'.format(
            ' '.join(self.opts), self.name)]
    def command(self):
        return '/bin/bash -c "`ivy_shell`; ./build/{}"'.format(self.name)
    def expect(self):
        return run_expect_module(self)

class IvyToCpp(Test):
    def command(self):
        return 'ivy_to_cpp {} {}.ivy'.format(' '.join(self.opts), self.name)


# --- ivyc-based tests (the v2 compiler; its logic differs from ivy_to_cpp,
#     so both are exercised). ivyc builds an executable under ./build. ---

class IvycTest(Test):
    def preprocess_commands(self):
        make_directory_exist('build')
        return ['ivyc target=test {} {}.ivy'.format(' '.join(self.opts), self.name)]
    def command(self):
        return './build/{}'.format(self.name)

class IvycRepl(Test):
    def preprocess_commands(self):
        make_directory_exist('build')
        return ['ivyc {} {}.ivy'.format(' '.join(self.opts), self.name)]
    def command(self):
        return './build/{}'.format(self.name)
    def expect(self):
        return run_expect_module(self)

class Ivyc(Test):
    def command(self):
        return 'ivyc {} {}.ivy'.format(' '.join(self.opts), self.name)


# --- ivy_to_rtl tests: translate a hardware design to RTLIL and validate it.
#
# A 'to_rtl' test runs `ivy_to_rtl <args> <name>.ivy`. If `expect` is given, it
# is matched against the tool's output (used for tests that expect a specific
# error, e.g. an unsound initialization). If `validate` is given, it is an
# arbitrary shell command run after a successful translation; the test passes
# iff that command exits 0. In `validate`, the token {name} is replaced by the
# test's base name, so a validation can refer to <name>.il (e.g. read it with
# yosys). ---

class IvyToRtl(Test):
    def __init__(self, dir, spec):
        Test.__init__(self, dir, spec)
        self.validate = spec.get('validate')

    def run_expect(self):
        cmd = 'ivy_to_rtl {} {}.ivy'.format(' '.join(self.opts), self.name)
        print(cmd)
        child = spawn(cmd, timeout=self.timeout)
        child.logfile = sys.stdout
        try:
            if self.res is not None:
                child.expect(self.res)      # e.g. an expected error message
            child.expect(pexpect.EOF)
        except (pexpect.EOF, pexpect.TIMEOUT):
            print(child.before)
            return False
        child.close()
        if self.validate is None:
            # pass if the expected output matched, or (no `expect` given) the
            # translation exited cleanly
            return self.res is not None or child.exitstatus == 0
        # a validation command was given: the translation must have succeeded,
        # and then the validation command must exit 0
        if child.exitstatus != 0:
            print('translation failed (exit status {})'.format(child.exitstatus))
            return False
        vcmd = self.validate.replace('{name}', self.name)
        print('validating: {}'.format(vcmd))
        vchild = spawn('/bin/bash', ['-c', vcmd], timeout=self.timeout)
        vchild.logfile = sys.stdout
        vchild.expect(pexpect.EOF)
        vchild.close()
        return vchild.exitstatus == 0


TEST_TYPES = {
    'check': IvyCheck,
    'test': IvyTest,
    'repl': IvyRepl,
    'to_cpp': IvyToCpp,
    'ivyc_test': IvycTest,
    'ivyc_repl': IvycRepl,
    'ivyc': Ivyc,
    'to_rtl': IvyToRtl,
}


def run_expect_module(test):
    """The repl tests are checked by a python module <name>_expect.py (or the
    module named by `expect`) that provides run(exe, opts, res)."""
    modname = test.res if test.res is not None else (test.name + '_expect')
    mod = load_module(modname, modname + '.py')
    return mod.run('build/' + test.name, test.opts, test.res)


def make_directory_exist(dir):
    if not os.path.exists(dir):
        os.mkdir(dir)


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# ----------------------------------------------------------------------------
# Collection

PRUNE = set(['.git', 'vendor', 'build', '_site', '__pycache__',
             'submodules', 'node_modules', '.jekyll-cache'])

def collect(root):
    """Walk `root` and return a list of Test objects from every ivy_tests.py."""
    tests = []
    counter = [0]
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames
                       if d not in PRUNE and not d.startswith('.')]
        if 'ivy_tests.py' not in filenames:
            continue
        counter[0] += 1
        mod = load_module('ivy_tests_{}'.format(counter[0]),
                          os.path.join(dirpath, 'ivy_tests.py'))
        defaults = getattr(mod, 'defaults', {})
        rel = os.path.relpath(dirpath, root)
        for spec in mod.tests:
            merged = dict(defaults)
            merged.update(spec)
            ttype = merged['type']
            if ttype not in TEST_TYPES:
                raise ValueError('{}: unknown test type {!r}'.format(
                    os.path.join(dirpath, 'ivy_tests.py'), ttype))
            t = TEST_TYPES[ttype](os.path.abspath(dirpath), merged)
            t.rel = rel
            tests.append(t)
    return tests


def usage():
    print("""usage:
    {} [option...]
options:
    type=<test type pattern>
    dir=<test directory pattern>
    name=<test name pattern>
    group=<test group pattern>   (default: ^normal$)
    root=<directory to search>
    list        list the selected tests without running them
""".format(sys.argv[0]))
    sys.exit(1)


def main():
    allpat = re.compile('.*')
    pats = {'type': allpat, 'dir': allpat, 'name': allpat,
            'group': re.compile('^normal$')}
    repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    root = repo_root
    list_only = False

    for arg in sys.argv[1:]:
        if arg == 'list':
            list_only = True
            continue
        vals = arg.split('=', 1)
        if len(vals) != 2:
            usage()
        name, val = vals
        if name in pats:
            pats[name] = re.compile(val)
        elif name == 'root':
            root = val
        else:
            usage()

    selected = [t for t in collect(root)
                if pats['type'].search(t.type)
                and pats['dir'].search(t.rel)
                and pats['name'].search(t.name)
                and pats['group'].search(t.group)]

    if list_only:
        for t in selected:
            print('{} [{}] {} ({}) {}'.format(t.rel, t.type, t.name,
                                              t.group, ' '.join(t.opts)))
        print('{} test(s) selected'.format(len(selected)))
        return

    num_failures = 0
    for t in selected:
        if not t.run():
            num_failures += 1
    if num_failures:
        print('error: {} tests(s) failed'.format(num_failures))
        sys.exit(1)
    else:
        print('OK')


if __name__ == "__main__":
    main()
