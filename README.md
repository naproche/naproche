# Naproche-SAD

[![Build Status](https://travis-ci.com/anfelor/Naproche-SAD.svg?branch=master)](https://travis-ci.com/anfelor/Naproche-SAD)

Proof Checking of Natural Mathematical Documents, with optional support
for Isabelle Prover IDE (Isabelle/PIDE – Isabelle/jEdit).


The subsequent explanations are for **development** of the tool, not for end-users!

## Command-line tool

### Prerequisites

  * Supported OS platforms: Linux, macOS, Windows (e.g. with Cygwin terminal)

  * The Haskell Tool Stack: https://www.haskellstack.org

  * The E Theorem Prover as executable "eprover" in the shell PATH (e.g. the
    multi-platform version provided by Isabelle: "isabelle getenv -b E_HOME")
    Supported versions: 2.0 to 2.5

  * Optional (for development): Haskell IDE within VSCode:
    https://marketplace.visualstudio.com/items?itemName=haskell.haskell


### Build and test

    cd .../naproche  #repository

    stack clean

    stack build

    stack test

### Manual checking of proof files

    stack exec Naproche-SAD -- OPTIONS FILE

  It may be necessary to allow the E Prover more time by appending "-t SECONDS"


## Isabelle/Naproche Prover IDE

### Isabelle repository setup

  * Isabelle repository clone from https://isabelle.sketis.net/repos/isabelle
    (see also README_REPOSITORY)

  * Initialize fresh clone:

        hg clone https://isabelle.sketis.net/repos/isabelle isabelle
        cd isabelle
        hg update -C -r f175fd68b6a9
        bin/isabelle components -I
        bin/isabelle components -a

  * Update existing clone:

        cd isabelle
        hg pull https://isabelle.sketis.net/repos/isabelle
        hg update -C -r f175fd68b6a9
        bin/isabelle components -a

  * Isabelle executable: there is no need to have bin/isabelle in the PATH,
    but it is convenient to put it into a standard place once, e.g.:

        bin/isabelle install "$HOME/bin"

### Isabelle component setup

  * remove existing components: ensure there is *no* reference to Naproche-SAD
    in $ISABELLE_HOME_USER/etc/settings or various etc/components files
    (e.g. Isabelle release)

  * update reference to Naproche-SAD repository in $ISABELLE_HOME_USER/etc/components
    like this:

        isabelle components -u .../naproche

### Isabelle build

  * Shutdown Isabelle/jEdit before building Isabelle/Naproche as follows:

        isabelle naproche_build

  * Run some tests as follows (make sure that your current directory is the root of the Naproche repository):

        isabelle naproche_build && isabelle naproche_test -j2

        isabelle naproche_test -o naproche_server_debugging

  * Package the Isabelle/Naproche component as follows:

        isabelle naproche_build && isabelle naproche_component -P

    The result is for the current repository version, and the underlying
    HW + OS platform. The following reference platforms (x86_64) are
    used for Isabelle2021:

      - Linux: Ubuntu 16.04 LTS
      - macOS: Mac OS X 10.13 High Sierra
      - Windows: Windows 10



### Use Isabelle Prover IDE

        cd .../naproche  #repository

* Open ForTheL examples in Isabelle/jEdit, e.g.

        isabelle jedit examples/cantor.ftl

* Open Isabelle development environment with ForTheL examples, e.g.

        isabelle jedit -l Pure Isabelle/Test.thy


## Reference ##

This program is based on the System for Automated Deduction (SAD) by
Andrei Paskevich, see https://github.com/tertium/SAD.
You can find more resources in our [CONTRIBUTING.md](CONTRIBUTING.md).
