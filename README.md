# Naproche-SAD

Proof Checking of Natural Mathematical Documents, with optional support
for Isabelle Prover IDE.


## Command-line tool

### Prerequisites

  * Supported OS platforms: Linux, macOS, Windows (e.g. with Cygwin terminal)

  * The Haskell Tool Stack: https://www.haskellstack.org

  * The E Theorem Prover as executable "eprover" in the shell PATH (e.g. the
    multi-platform version provided by Isabelle: "isabelle getenv -b E_HOME")

  * Optional (for development): Haskell IDE within VSCode:
    https://github.com/haskell/haskell-ide-engine


### Build

    cd .../Naproche-SAD  #repository

    stack build


### Test

    for FILE in examples/*.ftl
    do
      stack exec Naproche-SAD -- "$FILE"
    done


## Isabelle Prover IDE (Isabelle/jEdit)

### Prerequisites

  * Isabelle repository clone from https://isabelle.in.tum.de/repos/isabelle

  * "Quick start in 30min" according to README_REPOSITORY
    (https://isabelle.in.tum.de/repos/isabelle/raw-file/tip/README_REPOSITORY)

  * Use Isabelle/jEdit to edit $ISABELLE_HOME_USER/etc/settings to include
    the Naproche-SAD directory as Isabelle component. E.g. like this:

        init_component "$USER_HOME/Naproche-SAD"

  * Shutdown Isabelle/jEdit before building Isabelle/Naproche as follows.


### Build

    cd .../Naproche-SAD  #repository

    isabelle build -e -d Isabelle Naproche-Build
    stack build

Reference versions for multi-platform executables (x86_64):

  * Linux: Ubuntu 14.04 LTS
  * macOS: Mac OS X 10.10 Yosemite
  * Windows: Windows 10


### Test

* Open ForTheL examples in Isabelle/jEdit, e.g.

      isabelle jedit examples/powerset.ftl

* Open Isabelle development environment with ForTheL examples, e.g.

      isabelle jedit -l Pure Isabelle/Test.thy


### Multi-platform application bundling (with Isabelle)

  * Linux build host, e.g. Ubuntu 18.04 LTS with the following packages:
      - curl
      - lib32stdc++6
      - mercurial
      - p7zip-full
      - texlive-fonts-extra
      - texlive-font-utils
      - texlive-latex-extra
      - texlive-science

  * Standard Isabelle repository clone:

        hg clone https://isabelle.in.tum.de/repos/isabelle
        isabelle/bin/isabelle components -I
        isabelle/bin/isabelle components -a
        isabelle/bin/isabelle jedit -b

    optional tests, notably of LaTeX packages:
    
        isabelle/bin/isabelle build Pure
        isabelle/bin/isabelle build -g doc -R -b
        isabelle/bin/isabelle build -g doc -o document=pdf

  * Isabelle/Naproche component, e.g.:

        curl -o naproche-20181223.tar.gz -L https://github.com/Naproche/Naproche-SAD/releases/download/20181223/naproche-20181223.tar.gz

  * Application bundling, e.g. Isabelle/db001bc11855 + naproche-20181223:

        isabelle/Admin/build_release -r db001bc11855 -c naproche-20181223.tar.gz -R Isabelle_Naproche-20181223 -O -W dist/website dist


## Reference ##

This program is based on the System for Automated Deduction (SAD) by
Andrei Paskevich, see https://github.com/tertium/SAD
