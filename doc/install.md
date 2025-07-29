---
layout: page
title: Installing IVy
---

There are two ways to install ivy:

1. [Install from source](#source)
2. [Install a binary release](#binary)

<a name="source"></a> Installing from source
--------------------------------------------

1. [Install from source on Linux](#linuxnotes)
3. [Install from source on Mac](#macnotes)


<a name="source"></a> Installing a binary release
--------------------------------------------

1. [Install from source on Linux](#linuxbinary)


<a name="linuxnotes"></a> Installation from source on Linux
===========================================================

This describes the steps need to install IVy on Ubuntu 20.04. This may
also work on other Debian-based distributions.

### Prerequisites

    $ sudo apt-get install python3 python3-pip g++ cmake python3-ply python3-pygraphviz git python3-tk tix pkg-config libssl-dev libreadline-dev

### Install IVy

Get the source like this:

    $ git clone --recurse-submodules https://github.com/kenmcmil/ivy.git
    $ cd ivy

Optional: build the submodules. This is needed to use model checking or automated test generation. Use this command (which takes a while):

    $ python3 build_submodules.py

Optional, recommended: use a python virtal environment:

    $ python3 -m venv venv
    $ . venv/bin/activate
    $ export PATH=`pwd`/venv/bin

Install into your local Python like this:

    $ pip3 install z3-solver
    $ pip3 install .

Instead of installing z3 with pip, as above, you can install it manually in your python environment. You can ask pip to install a specific version of z3 with `z3-solver==X.Y`. 
If you want to run from the source tree for development purposes, do
this instead:

    $ pip3 install z3-solver
    $ pip3 install -e .

Optionally, build the experimental Ivy v2.0 compiler:

    $ python build_v2_compiler.py

### Run

Run Ivy on an example, like this:

    $ cd doc/examples
    $ ivy client_server_example.ivy

Or, if you only want to use Ivy on the command line, test it like this:

    $ ivy_check trace=true doc/examples/client_server_example_new.ivy
    
Ivy should print out a counterexample trace.

### Emacs mode

An emacs major mode for Ivy is available in `lib/emacs/ivy-mode.el`. Put this file
somewhere in your emacs load path and add the following code to your
`.emacs`:

    (add-to-list 'auto-mode-alist '("\\.ivy\\'" . ivy-mode))
    (autoload 'ivy-mode  "ivy-mode.el" "Major mode for editing Ivy code" t nil)

    
<a name="macnotes"></a> Installation from source on MacOS
=========================================================

Install using MacPorts
----------------------

These instructions have not been tested on recent MacOS versions.

1. Install Xcode from App Store
2. Install Xcode command line tools

        $ xcode-select --install

3. Install Xserver

    - [https://www.xquartz.org](https://www.xquartz.org)

4. Macports

        $ sudo xcodebuild -license

   Install Macports from [https://www.macports.org/install.php](https://www.macports.org/install.php). Select
   the version matching the macOS version running on your
   machine.

        $ sudo port install python310 py310-pip graphviz tix py310-tkinter git cmake openssl
        $ sudo port select --set python3 python310
        $ sudo port select --set pip3 pip310
        
5. Install Ivy:

    Follow the Linux instructions above, under "Install Ivy".

    You may have to do this to work around a bug in the python setup tools installed by macports:

        $ sudo ln -s /opt/local/Library/Frameworks/Python.framework/Versions/3.10/bin/ivy* /opt/local/bin




<a name="binary"></a> Binary releases
--------------------

Ivy is released as a Python package in the PyPI repository.

### <a name="linuxbinary"> Install binary release on Linux

    $ sudo apt-get install python3 python3-pip g++ cmake python3-ply python3-pygraphviz git python3-tk tix pkg-config libssl-dev libreadline-dev
    $ sudo pip3 install z3-solver ms-ivy

Note, if you omit `sudo` in the second command, Ivy will be installed
into `~\.local\bin`, which is probably not what you want, so be
careful.

This does not install the documentation and example files. You can get
these from github like this (see the directory `ivy/doc`):

    $ sudo apt-get install git
    $ git clone https://github.com/kenmcmil/ivy.git

### <a name="macbinary"> Install binary release on Mac

Mac binary distributions are not yet available.

 
