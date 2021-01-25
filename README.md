# Naproche-SAD

[![Build Status](https://travis-ci.com/anfelor/Naproche-SAD.svg?branch=master)](https://travis-ci.com/anfelor/Naproche-SAD)

Proof Checking of Natural Mathematical Documents, with optional support
for Isabelle Prover IDE.


## Command-line tool

### Prerequisites

  * Supported OS platforms: Linux, macOS, Windows (e.g. with Cygwin terminal)

  * The Haskell Tool Stack: https://www.haskellstack.org

  * The E Theorem Prover as executable "eprover" in the shell PATH (e.g. the
    multi-platform version provided by Isabelle: "isabelle getenv -b E_HOME")
    Supported versions: 2.0 to 2.5

  * Optional (for development): Haskell IDE within VSCode:
    https://github.com/haskell/haskell-ide-engine


### Build

    cd .../Naproche-SAD  #repository

    stack build


### Check proof files

    stack exec Naproche-SAD -- FILE

  It may be necessary to allow the E Prover more time by appending "-t SECONDS"


### Test

    stack test


## Isabelle Prover IDE (Isabelle/jEdit)

### Prerequisites

  * Isabelle repository clone from https://isabelle.sketis.net/repos/isabelle-release
    (see also README_REPOSITORY)

  * Initialize fresh clone:

        hg clone https://isabelle.sketis.net/repos/isabelle-release
        hg update -r Isabelle2021-RC3
        isabelle/bin/isabelle components -I
        isabelle/bin/isabelle components -a
        isabelle/bin/isabelle jedit -b

  * Update existing clone:

        hg pull
        hg update -r Isabelle2021-RC3
        isabelle/bin/isabelle components -a

  * Use Isabelle/jEdit to edit $ISABELLE_HOME_USER/etc/settings to include
    the Naproche-SAD directory as Isabelle component. E.g. like this:

        init_component "$USER_HOME/Naproche-SAD"


### Build

  * Shutdown Isabelle/jEdit before building Isabelle/Naproche as follows:

        isabelle naproche_build


### Test

      cd .../Naproche-SAD  #repository

* Open ForTheL examples in Isabelle/jEdit, e.g.

      isabelle jedit examples/powerset.ftl

* Open Isabelle development environment with ForTheL examples, e.g.

      isabelle jedit -l Pure Isabelle/Test.thy


### Reference versions for multi-platform executables (x86_64):

  * Linux: Ubuntu 16.04 LTS
  * macOS: Mac OS X 10.13 Yosemite
  * Windows: Windows 10


### Multi-platform application bundling (with Isabelle)

  * Linux build host, e.g. Ubuntu 18.04 LTS with the following packages:
      - curl
      - mercurial
      - p7zip-full
      - texlive-fonts-extra
      - texlive-font-utils
      - texlive-latex-extra
      - texlive-science

  * Standard Isabelle repository clone:

        hg clone https://isabelle.sketis.net/repos/isabelle-release
        hg update -r Isabelle2021-RC3
        isabelle/bin/isabelle components -I
        isabelle/bin/isabelle components -a
        isabelle/bin/isabelle jedit -b

    optional tests, notably of LaTeX packages:

        isabelle/bin/isabelle build Pure
        isabelle/bin/isabelle build -g doc -R -b
        isabelle/bin/isabelle build -g doc -o document=pdf

  * Isabelle/Naproche component, e.g.:

        curl -o naproche-20200303.tar.gz -L https://github.com/Naproche/Naproche-SAD/releases/download/20200303/naproche-20200303.tar.gz

  * Application bundling, e.g. Isabelle/61882acca79b + naproche-20200303:

        isabelle/Admin/build_release -r 61882acca79b -c naproche-20200303.tar.gz -b Pure -R Isabelle_Naproche-20200303 -O -W dist/website dist


## Reference ##

This program is based on the System for Automated Deduction (SAD) by
Andrei Paskevich, see https://github.com/tertium/SAD.
You can find more resources in our [CONTRIBUTING.md](CONTRIBUTING.md).
