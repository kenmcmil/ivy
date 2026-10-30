#!/usr/bin/env python3
"""Build and run concrete CPU/DRAM scenarios against cachemem-abs.ivy.

Run: python3 cachemem_smoke.py
Requirements: the project's Ivy venv, Verilator, a C++ compiler, and Yosys
(native yosys or the venv's yowasp-yosys). Each command has a 180-second cap.
No model source is rewritten: Ivy sources are copied byte-for-byte into a fresh
build directory, ivy_to_rtl extracts their actual memory_system, and Verilator
executes that netlist at its original widths and geometry. The C++ driver is an
external CPU/RAM environment, not another implementation of the cache.

Use --build-dir /tmp/cachemem-smoke-debug to retain generated RTL/build logs.
The directory must not already exist. This is a finite regression, not a proof;
it intentionally permits one outstanding request per CPU and overlaps independent
requests across the CPUs. It does not impose an ordering rule on the hardware.
"""

import argparse
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import tempfile


VENV = Path('/home/anthonydu/memory_sys_verif/ivy/venv/bin')


def run(command, cwd, env):
    print('+ ' + shlex.join(map(str, command)), flush=True)
    subprocess.run(list(map(str, command)), cwd=cwd, env=env,
                   check=True, timeout=180)


def build_and_run(build, source, env):
    for path in source.glob('*.ivy'):
        shutil.copy2(path, build / path.name)
    shutil.copy2(source / 'cachemem_smoke.cpp', build / 'cachemem_smoke.cpp')
    ivy = shutil.which('ivy_to_rtl', path=env['PATH'])
    yosys = (shutil.which('yowasp-yosys', path=env['PATH']) or
             shutil.which('yosys', path=env['PATH']))
    verilator = shutil.which('verilator', path=env['PATH'])
    missing = [name for name, value in [('ivy_to_rtl', ivy), ('yosys', yosys),
                                       ('verilator', verilator)] if not value]
    if missing:
        raise RuntimeError('Missing required tools: ' + ', '.join(missing))
    run([ivy, 'cachemem-abs.ivy'], build, env)
    run([yosys, '-p', 'read_rtlil cachemem-abs.il; hierarchy -check -top '
         'memory_system; proc; memory_map; opt_clean; write_verilog '
         '-noattr cachemem-smoke.v'], build, env)
    run([verilator, '--cc', '--exe', '--build', '-j', '2', '-Wno-fatal',
         '--top-module', 'memory_system', '--prefix', 'Vmemory_system',
         '--Mdir', 'obj_dir', '-CFLAGS', '-std=c++17',
         'cachemem-smoke.v', 'cachemem_smoke.cpp'], build, env)
    run([build / 'obj_dir' / 'Vmemory_system'], build, env)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build-dir', type=Path)
    args = parser.parse_args()
    source = Path(__file__).resolve().parent
    env = os.environ.copy()
    env['PATH'] = str(VENV) + os.pathsep + env.get('PATH', '')
    if args.build_dir:
        build = args.build_dir.resolve()
        build.mkdir(parents=True, exist_ok=False)
        print('Build assets retained at ' + str(build), flush=True)
        build_and_run(build, source, env)
    else:
        with tempfile.TemporaryDirectory(prefix='cachemem-smoke-') as name:
            build_and_run(Path(name), source, env)


if __name__ == '__main__':
    main()
