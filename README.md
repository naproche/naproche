# Naproche-SAD

[![Build Status](https://travis-ci.com/anfelor/Naproche-SAD.svg?branch=master)](https://travis-ci.com/anfelor/Naproche-SAD)

Proof Checking of Natural Mathematical Documents, with optional support
for Isabelle Prover IDE (Isabelle/PIDE – Isabelle/jEdit).


NOTE: The subsequent explanations are for **development** of the tool, not for end-users!


## Isabelle/Naproche Prover IDE

### Prerequisites

Ensure that `curl`, `git`, and `hg` (Mercurial) are installed:

  * Linux: e.g. `sudo apt install curl git mercurial`

  * macOS: e.g. `brew install mercurial` or download from https://www.mercurial-scm.org

  * Windows: use Cygwin64 with packages `curl`, `git`, and `mercurial` (via Cygwin setup-x86_64.exe)


### Repository management

Commands below assume the same current directory: repository clones
`isabelle_naproche` and `naproche` are put side-by-side.

* initial clone:
  ```shell
  hg clone https://isabelle.in.tum.de/repos/isabelle isabelle_naproche
  git clone https://github.com/naproche/naproche.git naproche

  isabelle_naproche/Admin/init -I Isabelle_Naproche -V ./naproche/Isabelle
  isabelle_naproche/bin/isabelle components -u ./naproche
  ```
* later updates:
  ```shell
  git --git-dir="./naproche/.git" pull
  isabelle_naproche/Admin/init -V ./naproche/Isabelle
  ```
* using recent eprover:
  since the eprover component of Isabelle is only updated so often, it might be desirable to use a more update to date version of the prover. In the following we assume that a compiled eprover executable is located at `eprover/PROVER/eprover`.
  ```
  export ISABELLE_PLATFORM64=$(isabelle getenv -b ISABELLE_PLATFORM64)
  export ISABELLE_HOME_USER=$(isabelle getenv -b ISABELLE_HOME_USER)
  mkdir -p naproche_e/$ISABELLE_PLATFORM64
  cp eprover/PROVER/eprover naproche_e/$ISABELLE_PLATFORM64/

  mkdir -p naproche_e/etc
  cat > naproche_e/etc/settings << EOF
  # -*- shell-script -*- :mode=shellscript:

  E_HOME="\$COMPONENT/\$ISABELLE_PLATFORM64"
  EOF

  isabelle_naproche/bin/isabelle components -u ./naproche_e
  ```
  Open the document at `$ISABELLE_HOME_USER/etc/components` and move the path corresponding to the `naproche_e` component above that corresponding to the `naproche` component. Finally, verify that the path returend by
  ```
  isabelle getenv -b NAPROCHE_EPROVER
  ```
  points to `naproche_e/$ISABELLE_PLATFORM64/eprover`. 

### Development

* Isabelle executable: there is no need to have `isabelle_naproche/bin/isabelle`
in the PATH, but it is convenient to put it into a standard place once, e.g.:

      isabelle_naproche/bin/isabelle install "$HOME/bin"


* Build and test:

  - Shutdown Isabelle/jEdit before building Isabelle/Naproche as follows:

        isabelle naproche_build


  - Run some tests as follows (make sure that your current directory is the root of the Naproche repository):

        isabelle naproche_build && isabelle naproche_test -j2

        isabelle naproche_test -o naproche_server_debugging


  - Package the Isabelle/Naproche component as follows:

        isabelle naproche_build && isabelle naproche_component -P


    The result is for the current repository version, and the underlying
    HW + OS platform. The following reference platforms (x86_64) are
    used for Isabelle2022:

      - Ubuntu Linux 18.04 LTS
      - macOS 11 Big Sur
      - Windows 10

* Isabelle Prover IDE

    - Open ForTheL examples in Isabelle/jEdit, e.g.

          isabelle jedit examples/cantor.ftl


    - Open Isabelle development environment with ForTheL examples, e.g.

          isabelle jedit -l Pure Isabelle/Test.thy



## Low-level command-line tool (without Isabelle)

### Prerequisites

  * Supported OS platforms: Linux, macOS, Windows (e.g. with Cygwin terminal)

  * The Haskell Tool Stack: https://www.haskellstack.org

  * Install the E Theorem Prover (supported versions: 2.0 to 2.5) and
    set the environment variable NAPROCHE_EPROVER to its executable
    path.

    Note: the E prover executable bundled with Isabelle can be located
    like this:

      ```
      isabelle getenv -b NAPROCHE_EPROVER
      ```

  * Optional (for development): Haskell IDE within VSCode:
    https://marketplace.visualstudio.com/items?itemName=haskell.haskell


### Build and test

    cd .../naproche  #repository

    stack clean

    stack build

    stack test



### Manual checking of proof files


    stack exec Naproche-SAD -- OPTIONS FILE


  It may be necessary to allow the E Prover more time by appending `-t SECONDS`


## Documentation

You can use the tool [Haddock][1] to automatically generate documentation of
Naproche's source code.
Just run the following command:

  ```sh
  stack haddock
  ```

To access this documentation via a local [Hoogle][2] server, proceed the
following steps:

  1.  Generate a local Hoogle database.

      ```sh
      stack hoogle -- generate --local
      ```

  2.  Start a local Hoogle server.

      ```sh
      stack hoogle -- server --local --port=8080
      ```

Now you can access the documentation with your favourite web browser at
<http://localhost:8080>.

If you are developing Naproche and want to add Haddock annotations to the source files, have a look at this guide:
<https://haskell-haddock.readthedocs.io/en/latest/markup.html>


## Reference ##

This program is based on the System for Automated Deduction (SAD) by
Andrei Paskevich, see https://github.com/tertium/SAD.
You can find more resources in our [CONTRIBUTING.md](CONTRIBUTING.md).


[1]: <https://haskell-haddock.readthedocs.io/en/latest/>
[2]: <https://wiki.haskell.org/Hoogle>
