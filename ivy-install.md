# Ivy installation

1. [Install on Linux](#linuxbinary)
2. [Install on Mac](#macbinary)
3. [Emacs mode](#emacsmode)

## <a name="linuxbinary"> Install binary release on Linux

On a CS department Linux machine, do the following:

    $ virtualenv ivyenv
    $ source ivyenv/bin/activate
    $ pip install ms-ivy

The second command above must be executed in every new shell in which you wish to iuse Ivy. On other machines, before doing the above you may need to install some system packages. On Ubuntu, use this command:

    $ sudo apt-get install python python-pip g++ python-ply python-pygraphviz python-tk tix libssl-dev libreadline-dev

## <a name="macbinary"> Install binary release on Mac

Ivy is currently available for MacOS Catalina. If you have different version of MacOS, please contact the instructor.

1. Install Xcode from App Store, or just Xcode command-line tools from Apple developer site.
2. Install Xcode command line tools

        $ xcode-select --install

3. Install Xserver

    - [https://www.xquartz.org](https://www.xquartz.org)

4. Macports

        $ sudo xcodebuild -license

    Install Macports from [https://www.macports.org/install.php](https://www.macports.org/install.php). Select
    the version matching The macOS matching the macOS version running on your
    machine. 

        $ sudo port install python27
        $ sudo port install py27-pip
        $ sudo port install graphviz
        $ sudo port select --set python python27
        $ sudo port select --set python2 python27
        $ sudo port select --set pip pip27
        $ sudo port select --set pip2 pip27
        $ sudo pip install pyparsing==2.1.4
        $ sudo port install Tix
        $ sudo port install py27-tkinter

5. Install Ivy

        $ sudo pip install ms-ivy

## <a name="emacsmode">  Emacs mode

An emacs major mode for Ivy is available from github as [ivy-mode.el](https://github.com/kenmcmil/ivy/blob/master/lib/emacs/ivy-mode.el). Put this file
somewhere in your emacs load path and add the following code to your
`.emacs`:

    (add-to-list 'auto-mode-alist '("\\.ivy\\'" . ivy-mode))
    (autoload 'ivy-mode  "ivy-mode.el" "Major mode for editing Ivy code" t nil)

You can also use `flycheck` to check your program for errors while editing. Here are the commands you need in your `.emacs` file:

    (require 'package)

    (add-to-list 'package-archives
                 '("MELPA Stable" . "https://stable.melpa.org/packages/") t)
    (package-initialize)

    (use-package flycheck
      :ensure t
      :init (global-flycheck-mode))

    (flycheck-define-checker ivy
      "An Ivy syntax checker using the Ivy compiler."
      :command ("ivy_check" "assert=none:0" source)
      :error-patterns
        ((error line-start (file-name) ": line " line ": error: " (message) line-end)
         (error line-start (file-name) "(" line "): error: " (message) line-end))
      :modes ivy-mode)

    (add-to-list 'flycheck-checkers 'ivy)
