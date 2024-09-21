# Haskell

Naproche is written in the functional programming language [Haskell][haskell].


## Learning Haskell

There are many textbooks and tutorials about Haskell freely available on the
web. See e.g. <https://wiki.haskell.org/Tutorials> for an overview.

**Recommendation:** The book
[*Learn You a Haskell for Great Good!*][learn-you-a-haskell] is an excellent
starting point for learning Haskell and functional programming.


## Haskell IDEs

There are many text editors that can be used as an IDE for Haskell. See e.g.
<https://wiki.haskell.org/IDEs> for an overview.

**Recommendation:** [VSCodium][vscodium] (and also its proprietary counterpart
[VSCode][vscode]) together with its [Haskell][vscode-haskell] extension provides
an easy-to-use Haskell IDE for Linux, macOS and Windows. Note that you need to
have to install GHCup (see [below](#ghcup-optional)) on your system before
launching the extension.


## GHCup

[GHCup][ghcup] is a tool for managing your Haskell infrastructure. It allows to
easily install, manage and update the components of your Haskell toolchain.
Though it is not necessary to use GHCup for those tasks, it can make your life
a lot easier.

See <https://www.haskell.org/ghcup/install/>
for installation instructions for GHCup on Linux, macOs and Windows.


## Stack

Naproche is provided as a [Stack][stack] project. Stack is a tool to build
Haskell projects and manage their dependencies. You only have to install Stack
if you want to build and run the *command line interface* of Naproche. To build
and run the *Isabelle/jEdit interface* of Naproche, you do **not** need to
install Stack on your system.

See <https://docs.haskellstack.org/en/stable/install_and_upgrade/>
for installation instructions for Stack on Linux, macOS and Windows.
In particular, if you are using GHCup (see [above](#ghcup-optional)), Stack can
be installed by executing the command

```
ghcup install stack
```

in a terminal.


## Hoogle

[Hoogle][hoogle] is a search engine for many standard Haskell libraries. These
libraries can be searched by either function name or by (approximate) type
signature via Hoogle's web interface: <https://hoogle.haskell.org/>

To be able to use Hoogle also on the code base of Naproche, you have to set up
a local Hoogle server via the following steps:

  1.  Make sure that Stack is installed on your system (see [above](#stack)).

  2.  Make sure that you have a local clone of the Naproche repository on your
      system.

  3.  Open a terminal and [cd][cd] into your
      [`$NAPROCHE_HOME`](#cloning-the-naproche-repository) directory.

  4.  Generate a local Hoogle database for the Naproche code and the libraries
      it depends on by executing the following command in your terminal:

      ```
      stack hoogle -- generate --local
      ```

  5.  Start a local Hoogle server by executing the following command in your
      terminal:

      ```
      stack hoogle -- server --local --port=8080
      ```

  6.  Open <http://localhost:8080> in your favourite web browser.


## Haddock

[Haddock][haddock] is a tool for automatically generating documentation from
annotated Haskell source code. When editin the source code of Naproche, it is
highly recommended to use Haddock to document the source files,

See <https://haskell-haddock.readthedocs.io/latest/markup.html> for a guide on
how to annotate Haskell code with Haddock.


[learn-you-a-haskell]: <https://www.learnyouahaskell.com/>
[vscodium]: <https://vscodium.com/>
[vscode]: <https://code.visualstudio.com/>
[vscode-haskell]: <https://marketplace.visualstudio.com/items?itemName=haskell.haskell>
[stack]: <https://docs.haskellstack.org/en/stable/>
[ghcup]: <https://www.haskell.org/ghcup/>
[hoogle]: <https://hoogle.haskell.org/>
[cd]: <https://en.wikipedia.org/wiki/Cd_(command)>
[haddock]: <https://haskell-haddock.readthedocs.io/latest/>
