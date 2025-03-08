# Naproche

Proof Checking of Natural Mathematical Documents, with optional support
for [Isabelle Prover IDE (Isabelle/PIDE – Isabelle/jEdit)][isabelle-jedit].


## For End-Users

You can get a fully integrated version of Naproche for Linux, macOS and Windows
that is bundled with [Isabelle][isabelle]: Download and run the application from
<https://isabelle.in.tum.de> and open the file `$ISABELLE_NAPROCHE/Intro.thy` in
its `Documentation` panel.


## For Developers

### Isabelle/Naproche Prover IDE

#### Prerequisites

Ensure that `curl`, `g++`, `gcc`, `git`, `gmp`, `make`, and `hg` (Mercurial) are installed:

  * Linux: e.g. `sudo apt install curl g++ gcc git libgmp-dev make mercurial`

  * macOS: e.g. `brew install mercurial` or download from https://www.mercurial-scm.org

  * Windows: use Cygwin64 with packages `curl`, `gcc-core`, `git`, `make`, and `mercurial` (via Cygwin setup-x86_64.exe)


#### Repository Management

Commands below assume the same current directory: repository clones
`isabelle_naproche` and `naproche` are put side-by-side.

* Initial clone:
  ```shell
  hg clone https://isabelle.sketis.net/repos/isabelle-release isabelle_naproche
  git clone https://github.com/naproche/naproche.git naproche

  isabelle_naproche/Admin/init -U https://isabelle.sketis.net/repos/isabelle-release -I Isabelle_Naproche -V ./naproche/Isabelle
  isabelle_naproche/bin/isabelle components -u ./naproche
  ```

* Later updates:
  ```shell
  git --git-dir="./naproche/.git" pull
  isabelle_naproche/Admin/init -V ./naproche/Isabelle
  ```

#### Development

* Isabelle executable: there is no need to have `isabelle_naproche/bin/isabelle`
in the PATH, but it is convenient to put it into a standard place once, e.g.:
  ```shell
  isabelle_naproche/bin/isabelle install "$HOME/bin"
  ```

* Build and test:
  
  - Shutdown Isabelle/jEdit before building Isabelle/Naproche as follows:
    ```shell
    isabelle naproche_build
    ```
  - Run some tests as follows (make sure that your current directory is the root of the Naproche repository):
    ```shell
    isabelle naproche_build && isabelle naproche_test -j2

    isabelle naproche_test -o naproche_server_debugging
    ```

  - Package the Isabelle/Naproche component as follows:
    ```shell
    isabelle naproche_build && isabelle naproche_component -P
    ```

    The result is for the current repository version, and the underlying
    HW + OS platform. The following reference platforms (x86_64) are
    used for Isabelle2025:
    - Ubuntu Linux 24.04 LTS with packages `texlive-latex-extra` and `texlive-bibtex-extra`
    - macOS 11 Big Sur
    - Windows 10/11

* Isabelle Prover IDE
  
  - Open ForTheL examples in Isabelle/jEdit, e.g.
    ```shell
    isabelle jedit examples/cantor.ftl
    ```
  - Open Isabelle development environment with ForTheL examples, e.g.
    ```shell
    isabelle jedit -l Pure Isabelle/Test.thy
    ```

* Using a recent E Theorem Prover:
  The E Theorem Prover bundled with Isabelle is only updated so often. If you would like to use the latest E Theorem Prover, follow the following instructions.

  1. Download and install the latest version of the E Theorem Prover from [The E Theorem Prover Website](https://wwwlehre.dhbw-stuttgart.de/~sschulz/E/Download.html). Installation instructions are provided in the `README` file. After following these, a working E executable should be located at `E/PROVER/eprover`.
  
  2. To make the `eprover` executable available to Isabelle/Naproche, we will create the `e_naproche` Isabelle component. First, we prepare the directory structure of the component:
      ```shell
      mkdir -p e_naproche/etc
      mkdir e_naproche/$(isabelle_naproche/bin/isabelle getenv -b ISABELLE_PLATFORM64)
      ```

      We then copy the `eprover` exutable into the component:
      ```shell
      cp eprover/PROVER/eprover e_naproche/$(isabelle_naproche/bin/isabelle getenv -b ISABELLE_PLATFORM64)/
      ```

      And create a document at `e_naproche/etc/settings` with the following content:
      ```plain
      # -*- shell-script -*- :mode=shellscript:

      E_HOME="$COMPONENT/$ISABELLE_PLATFORM64"
      ```

      Finally, we add the `e_naproche` component to Isabelle.
      ```shell
      isabelle_naproche/bin/isabelle components -u ./e_naproche
      ```
  
  3. To ensure that Naproche does not fall back to the E Theorem Prover component bundled with Isabelle, we need to ensure that the `e_naproche` component is loaded before the `naproche` component. First, navigate to your Isabelle user home, which can be located using
      ```shell
      isabelle_naproche/bin/isabelle getenv -b ISABELLE_HOME_USER
      ```
    
      Then edit the document at `etc/components`. Move the path pointing to the `e_naproche` component above that pointing to the `naproche` component.
  
      Finally, verify that the path returend by
      ```shell
      isabelle getenv -b NAPROCHE_EPROVER
      ```
      points to the `eprover` executable inside the `e_naproche` component.


### Command Line Interface

#### Prerequisites

* Supported OS platforms: Linux, macOS, Windows (e.g. with a [Cygwin][cygwin]
  terminal or with [Windows Subsystem for Linux][wsl])

* Set the environment variables `NAPROCHE_EPROVER`, `NAPROCHE_SPASS` and
  `NAPROCHE_VAMPIRE` to the locations of the respective executables of [E][e],
  [SPASS][spass] and [Vampire][vampire] that are bundled with
  Isabelle:

  ```shell
  export NAPROCHE_EPROVER="$(isabelle getenv -b NAPROCHE_EPROVER)"
  export NAPROCHE_SPASS="$(isabelle getenv -b NAPROCHE_SPASS)"
  export NAPROCHE_VAMPIRE="$(isabelle getenv -b NAPROCHE_VAMPIRE)"
  ```

* Initialize the environment variable `NAPROCHE_FORMALIZATIONS`:

  ```shell
  export NAPROCHE_FORMALIZATIONS="$(isabelle getenv -b NAPROCHE_FORMALIZATIONS)"
  ```


#### Build

* Build Naproche:

  ```shell
  isabelle naproche_build
  ```

* Add Naproche to your path:

  ```shell
  export PATH="$PATH:$(isabelle getenv -b NAPROCHE_EXE_DIR)"
  ```


#### Run

```shell
Naproche [<options>] [<file>]
```

* `<options>`: A list of options. Run `Naproche -h` for a list of all options.

* `<file>`: A `.ftl` or `.ftl.tex` file. If no file is given, `stdin` is used
  (where by default a ForTheL text in the FTL dialect is expected; to enter a
  text in the TEX dialect, provide the option `--tex=on`).


## Rendering the Formalizations as PDF or HTML

### Prerequisites

* Make sure that up-to-date versions of `pdflatex` and `bibtex` are in your
  `PATH`.

* (Optional – only required to render the formalizations as HTML.)
  Make sure that an up-to-date version of [RusTeX][rustex] is in your `PATH`.


### Rendering as PDF

```shell
Naproche --mode=render <filename>.ftl.tex
```


### Rendering as HTML

```shell
rustex -i <filename>.ftl.tex -o <filename>.ftl.xhtml
bibtex <filename>.ftl

sed -i "s|</style>|</style>\n    <link rel=\"stylesheet\" href=\"$(isabelle getenv -b NAPROCHE_FORMALIZATIONS)/latex/lib/lib.css\"/>\;|g" <filename>.ftl.xhtml
```


## Changelog

See [CHANGELOG.md](CHAMGELOG.md) for a changelog of Naproche.


## License

Naproche is licensed under the [GPL-3][gpl-3]. See [LICENSE.md](LICENSE.md) for
details.


## References

Naproche is based on the [System for Automated Deduction (SAD)][sad] by
[Andrei Paskevich][andrei-paskevich].
You can find more resources in our [CONTRIBUTING.md](CONTRIBUTING.md).


[isabelle]: <https://isabelle.in.tum.de/>
[sad]: <https://github.com/tertium/SAD>
[andrei-paskevich]: <http://www.tertium.org/>
[isabelle-jedit]: <https://isabelle.in.tum.de/dist/doc/jedit.pdf>
[gpl-3]: <https://www.gnu.org/licenses/gpl-3.0.en.html>
[e]: <https://wwwlehre.dhbw-stuttgart.de/~sschulz/E/E.html>
[spass]: <https://www.mpi-inf.mpg.de/departments/automation-of-logic/software/spass-workbench>
[vampire]: <https://vprover.github.io/>
[cygwin]: <https://cygwin.com/>
[wsl]: <https://learn.microsoft.com/en-us/windows/wsl/>
[rustex]: <https://github.com/slatex/RusTeX>
[texlive]: <https://tug.org/texlive/>
