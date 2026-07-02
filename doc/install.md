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



<a name="linuxnotes"></a> Installation from source on Linux
===========================================================

This describes the steps need to install IVy on Ubuntu 22.04. This may
also work on other Debian-based distributions.

### Prerequisites

    $ sudo apt-get install python3 python3-pip python3-venv g++ cmake python3-ply python3-pygraphviz git python3-tk pkg-config libssl-dev libreadline-dev

### Install IVy

Get the source like this:

    $ git clone --recurse-submodules https://github.com/kenmcmil/ivy.git
    $ cd ivy

Optional: build the submodules. This is needed to use model checking or automated test generation. Use this command (which takes a while):

    $ python3 build_submodules.py

Optional, recommended: use a python virtal environment:

    $ python3 -m venv venv
    $ . venv/bin/activate

If you want to use a particular version of Z3, you can install it like this:

    $ pip3 install z3-solver==X.Y

where X.Y is the version. 

Install into your local Python like this:

    $ pip3 install .

If Z3 is not already installed in your Python, you'll get the latest
version in PyPI.

If you want to run from the source tree for development purposes, do
this instead:

    $ pip3 install -e .

Optionally, build the experimental Ivy v2.0 compiler:

    $ python3 build_v2_compiler.py

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

Install using Homebrew
----------------------

These instructions have been tested on macOS 26 (Tahoe) on Apple silicon.

1. Install the Xcode command line tools (if not already installed). These
   provide the C/C++ compiler used to build Ivy's submodules; a full Xcode
   installation from the App Store is not required.

        $ xcode-select --install

2. Optional: install [XQuartz](https://www.xquartz.org) if you need the Ivy
   GUI.

3. Install Homebrew (if not already installed), following the instructions
   at [https://brew.sh](https://brew.sh):

        $ /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"

   On Apple silicon, make sure Homebrew is on your `PATH` afterwards. The
   installer prints the exact command; it is usually:

        $ eval "$(/opt/homebrew/bin/brew shellenv)"

4. Install the build prerequisites:

        $ brew install cmake coreutils git graphviz pkgconf openssl@3 readline python@3.10 python-tk@3.10

   `openssl@3` is required to build the `picotls` submodule, and `pkgconf`
   (which provides `pkg-config`) lets that build find it.

5. Use Python 3.10.

   Ivy is built and installed using Python 3.10 (installed above as
   `python3.10`). This version is needed only to build and install Ivy: it
   does not change the Python you use for anything else, and you do not need
   Python at all to *run* Ivy afterwards, since Ivy is used through its
   command-line tools (such as `ivy_check`).

   Homebrew's Python is "externally managed", so install Ivy into a virtual
   environment created with Python 3.10. This also keeps the installation
   self-contained:

        $ python3.10 -m venv ivy-venv
        $ . ivy-venv/bin/activate
        $ python --version        # should print Python 3.10.x

6. Install Ivy:

   With the virtual environment activated, follow the Linux instructions
   above under "Install Ivy", starting from the `git clone` step (you can
   skip the separate virtual-environment step there, since you created one
   above).





<a name="binary"></a> Binary releases
--------------------

Ivy is released as a Python package in the PyPI repository.

### <a name="linuxbinary"> Install binary release on Linux

    $ sudo apt-get install python3 python3-pip g++ cmake python3-ply python3-pygraphviz git python3-tk tix pkg-config libssl-dev libreadline-dev
    $ sudo pip3 install ms-ivy

Note, if you omit `sudo` in the second command, Ivy will be installed
into `~\.local\bin`, which is probably not what you want, so be
careful.

This does not install the documentation and example files. You can get
these from github like this (see the directory `ivy/doc`):

    $ sudo apt-get install git
    $ git clone https://github.com/kenmcmil/ivy.git

### <a name="macbinary"> Install binary release on Mac

A macOS binary wheel (Apple silicon, Python 3.10) is published on PyPI.
Install it into a Python 3.10 environment; a virtual environment is
recommended:

    $ brew install python@3.10 graphviz
    $ python3.10 -m venv ivy-venv
    $ . ivy-venv/bin/activate
    $ pip3 install ms-ivy

`graphviz` provides the `dot` tool used for visualization. As on Linux,
this does not install the documentation and example files; get those from
GitHub:

    $ git clone https://github.com/kenmcmil/ivy.git

 
