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
2. [Install from source on Windows](#windowsnotes)
3. [Install from source on Mac](#macnotes)


<a name="linuxnotes"></a> Installation from source on Linux
===========================================================

This describes the steps need to install IVy on Ubuntu 18.04. This may
also work on other Debian-based distributions.

### <a name="linuxdeps"></a> Prerequisites

    $ sudo apt-get install python python-pip g++ cmake python-ply python-pygraphviz git python-tk tix pkg-config libssl-dev libreadline-dev
    $ sudo pip install pyparsing==2.1.4 pexpect


### Install IVy

Get the source like this:

    $ git clone --recurse-submodules https://github.com/Microsoft/ivy.git
    $ cd ivy

Build the submodules like this (it takes a while):

    $ python build_submodules.py

Install into your local Python like this:

    $ sudo python setup.py install

If you want to run from the source tree for development purposes, do
this instead:

    $ sudo python setup.py develop

It's useful to do this in a Python virtual environment if you don't want to
alter your current Python setup.

See the [python documentation](https://docs.python.org/2/install/) for
general instructions on installing python packages.

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

<a name="windowsdeps"></a> Windows prerequisites
=================================================

### Security exceptions

If you want to compile programs or testers in Ivy, you may need to
install a security exception to prevent the antivirus software from
scanning your programs each time they are run (which makes startup of
programs very slow). This is a generic problem with compiling binary
code on Windows. If you are using Windows 10 and your antivirus is
Windows defender, exceptions are found under Start > Settings > Update
& Security > Windows Security > Virus & Threat Protection > Virus &
Threat Protection Settings > Manage Settings. Add an exception for the
directory in which you plan to do development. This should cover all
subdirecties as well. If you just want to do verification without
compiling, this step is not necessary.

### Visual studio

Install Visual Studio 2019. You may be able to get away with other
versions of the Visual Studio compiler tools, but only Visual Studio
2019 is documented here.  Some free tools that might be helpful are
available [here](https://visualstudio.microsoft.com/downloads/).

### Python and Python packages

Install Python 2.7.11 in the normal way. Make sure to install 64-bit
Python. Install Python in `c:/Python27` and put `c:/Python27` in your
PATH.

The `pip` package installation utility is found in `c:/Python27/Scripts`. You should put
this directory in your `PATH`, since the IVY command line scripts will also be installed there
by default. Try installing the `tarjan` and `ply` packages like this:

    > pip install tarjan
    > pip install ply

### Graphviz

You only need graphviz to use the Ivy GUI. For command line verification and
testing tasks, you don't need this.  Get `graphviz-2.38` from
[graphviz.org](http://graphviz.org). Install into some directory
without spaces in the name, for example `c:/Graphviz2.38`. Make sure that
`c:/Graphviz2.38/bin` is in your `PATH`.

### OPENSSL

OpenSSL binaries for Windows can be found
[here](https://slproweb.com/products/Win32OpenSSL.html).  You need the
full 64-bit version. Be sure to install in the default directory
`c:\OpenSSL-Win64`. These OpenSSL binaries are missing a file
`include/ms/applink.c`. Do this:

    > mkdir c:\OpenSSL-Win64\include\ms
    > copy c:\OpenSSL-Win64\include\openssl\applink.c c:\OpenSSL-Win64\include\ms

You also need to copy the libcrypto DLL into someplace the system will
find it:

    > copy c:\OpenSSL-Win64\libcrypto-1_1-x64.dll c:\Windows\SysWOW64\

### Windows SDK

Install Windows SDK version 10.0.14393.0 from
[here](https://developer.microsoft.com/en-us/windows/downloads/sdk-archive). You
have to get exactly this version, even if you have a newer
version. The windows build tool is very fussy about this. Note, this
version number may change. You'll get an error mesage when compiling
if it does. Install the version that it asks for.

<a name="windowsnotes"></a> Windows installation from source
============================================================

### Installing Ivy

First, install the [Windows prerequisites](#windowsdeps).

### Install git

Install git from [here](https://gitforwindows.org). If you install it
in `c:/Git`, then put `c:\Git\cmd` in your `PATH`.

### Install Ivy

    > cd c:\
    > git clone https://github.com/Microsoft/ivy.git
    > cd ivy
    > git submodule init
    > git submodule update
    > python build_submodules.py
    > python setup.py develop

Using the `develop` command instead of `install` is helpful, since you
then don't have to install again after each time you modify the code
or pull a new version.  If you have put `c:/Python27/Scripts` in your
`PATH`, you should now be able to run IVy like this:

    > ivy ui=cti doc/examples/client_server_example.ivy

Or, if you only want to use Ivy on the command line, test it like this:

    > ivy_check trace=true doc/examples/client_server_example.ivy
    

<a name="macnotes"></a> Installation from source on MacOS
=========================================================

### <a name="macdeps"></a> Mac prerequisites

1. Install Xcode from App Store
2. Install Xcode command line tools

        $ xcode-select --install
        $ sudo xcodebuild -license

3. Install Xserver (only if graphical user interface is needed)

    - [https://www.xquartz.org](https://www.xquartz.org)

4. Install dependencies 

    Needed software can be installed with either MacPorts or Homebrew. For the graphical user interface,
    you must use MacPorts, as not all of the required packages are available on Homebrew.

    To use MacPorts, install it (if needed) from
    [https://www.macports.org/install.php](https://www.macports.org/install.php). Then
    use these commands:

        $ sudo port install python27
        $ sudo port install py27-pip
        $ sudo port install graphviz
        $ sudo port select --set python2 python27
        $ sudo port select --set pip2 pip27
        $ sudo port install Tix
        $ sudo port install py27-tkinter
        $ sudo port install cmake
        $ sudo port install openssl
        # sudo port install readline

    To use Homebrew, first install it (if needed) with this command:

        $ /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"

    Then install packages with these commands:

        $ brew install cmake python@2 openssl@1.1 readline  
        $ sudo easy_install pip==20.2.3
        $ sudo pip install --ignore-installed --force-reinstall pyparsing==2.1.4

### Build and install Ivy on Mac

    $ git clone --recurse-submodules https://github.com/Microsoft/ivy.git
    $ cd ivy

Build the submodules like this (it takes a while):

    $ python build_submodules.py

Install into your local Python like this

    $ sudo python setup.py install
    $ sudo ln -s /opt/local/Library/Frameworks/Python.framework/Versions/2.7/bin/ivy* /opt/local/bin

The second command may not be necessary, but works around a bug in
the python setup tools installed by macports.

If you want to run from the source tree for development purposes, do
this instead:

    $ sudo python setup.py develop

It's useful to do this in a Python virtual environment if you don't want to
alter your current Python setup.

See the [python documentation](https://docs.python.org/2/install/) for
general instructions on installing python packages.

Optionally, build the experimental Ivy v2.0 compiler:

    $ python build_v2_compiler.py

Run a test:

    $ cd doc/examples
    $ ivy_check trace=true client_server_example_new.ivy

This should output a counterexample. To test the GUI (if you installed all the prerequisites):

    $ ivy_check diagnose=true client_server_example_new.ivy


<a name="binary"></a> Binary releases
--------------------

Ivy is released as a Python package in the PyPI repository. The release does 
not install the documentation and example files. You can get
these from github like this (see the directory `ivy\doc`):

    $ git clone https://github.com/Microsoft/ivy.git

### <a name="linuxbinary"> Install binary release on Linux

First install the [Linux prerequisites](#linuxdeps). Then do:

    $ sudo pip install ms-ivy


### <a name="windowsbinary"> Install binary release on Windows

First, install the [Windows prerequisites](#windowsdeps).

Then install the Ivy binaries:

    > pip install ms-ivy

This does not install the documentation and example files. You can get
these from the source repository. See [Windows installation from
source](#windowsnotes).

### <a name="macbinary"> Install binary release on Mac

First install the [Mac prerequisites](#macdeps). Then do:

    $ sudo pip install ms-ivy


 
