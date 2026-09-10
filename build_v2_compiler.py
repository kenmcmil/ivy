import sys
import os
import platform
import shutil

def get_cxx():
    """Pick the C++ compiler for the v2 compiler stages.

    On macOS the generated C++ targets libc++ and is most reliable with
    clang++.  Honor $CXX when the environment provides it, otherwise use
    clang++ on Darwin and g++ elsewhere.
    """
    candidates = [os.environ.get('CXX')]
    candidates.append('clang++' if platform.system() == 'Darwin' else 'g++')
    for cxx in candidates:
        if cxx and shutil.which(cxx):
            return cxx
    return 'g++'


def cxx_extra_flags(cxx):
    # clang understands this; GCC only warns about it, so keep it for clang.
    return '-Wno-parentheses-equality ' if 'clang' in os.path.basename(cxx) else ''

def do_cmd(cmd):
    print(cmd)
    status = os.system(cmd)
    if status:
        exit(1)
    
def make_dir_exist(dir):
    if not os.path.exists(dir):
        os.mkdir(dir)
    elif not os.path.isdir(dir):
        print("cannot create directory {}".format(dir))
        exit(1)
        

def find_vs():
    import os
    try:
        windir = os.getenv('WINDIR')
        drive = windir[0]
    except:
        drive = 'C'
    for v in ["2019","2017"]:
        for w in ['',' (x86)']:
            dir = '{}:\\Program Files{}\\Microsoft Visual Studio\{}'.format(drive,w,v)
            if os.path.exists(dir):
                for vers in ['Enterprise','Professional','Community']:
                    vers_dir = dir + '\\' + vers
                    if os.path.exists(vers_dir):
                        vcvars = vers_dir + '\\VC\\Auxiliary\\Build\\vcvars64.bat'
                        if os.path.exists(vcvars):
                            return vcvars
    for v in range(15,9,-1):
        for w in ['',' (x86)']:
            dir = '{}:\\Program Files{}\\Microsoft Visual Studio {}.0'.format(drive,w,v)
            vcvars = dir + '\\VC\\vcvars64.bat'
            if os.path.exists(vcvars):
                return vcvars
    print('Cannot find a suitable version of Visual Studio (require 10.0-15.0 or 2017 or 2019)')


def build_v2_compiler():

    cwd = os.getcwd()
    cxx = get_cxx()
    extra = cxx_extra_flags(cxx)

    os.chdir('ivy/ivy2/s1')
    do_cmd('ivyc target=repl ivyc_s1.ivy')
    do_cmd('{} {}-O2 -o ivyc_s1 ivyc_s1.cpp -pthread'.format(cxx, extra))

    os.chdir('../s2')
    do_cmd('IVY_INCLUDE_PATH=../s1/include ../s1/ivyc_s1 ivyc_s2.ivy')
    do_cmd('{} -I../s1/include {}-O2 -o ivyc_s2 -std=c++17 ivyc_s2.cpp'.format(cxx, extra))

    os.chdir('../s3')
    do_cmd('IVY_INCLUDE_PATH=../s2/include ../s2/ivyc_s2 ivyc_s3.ivy')
    
    os.chdir(cwd)
    
if __name__ == "__main__":
    build_v2_compiler()
    
