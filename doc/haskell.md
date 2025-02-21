# Haskell

Naproche is written in the functional programming language [Haskell][haskell].


## Learning Haskell

There are many textbooks and tutorials about Haskell freely available on the
web. See e.g. <https://wiki.haskell.org/Tutorials> for an overview.

**Recommendation:** The (freely available) book
[*Learn You a Haskell for Great Good!*][learn-you-a-haskell] is an excellent
starting point for learning Haskell and functional programming.


## GHCup

[GHCup][ghcup] is a tool for managing your Haskell infrastructure. It allows to
easily install, manage and update the components of your Haskell toolchain.
Though it is not necessary to use GHCup for those tasks, it can make your life
a lot easier.


### Installing GHCup

#### Debian, Ubuntu, Linux Mint

  1.  Install required packages:

      * Debian:
      
        ```
        sudo apt install curl build-essential libffi-dev libgmp-dev libncurses-dev libncurses5 libtinfo5 pkg-config
        ```

      * Ubuntu:
      
        ```
        sudo apt install build-essential curl libffi-dev libgmp-dev libncurses-dev pkg-config
        ```

      * Linux Mint:

        ```
        sudo apt install build-essential libffi-dev libgmp-dev libncurses-dev libtinfo-dev
        ```

  2.  Run the installation script:

      ```
      curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
      ```

      The script will ask you a couple of questions to set up the installation
      process. The recommended answers are given below.

      1.  Starting the installation setup:
      
          ```
          Press ENTER to proceed or ctrl-c to abort.
          Note that this script can be re-run at any given time.
          ```

          Press `<ENTER>`.

      2.  Setting the PATH variable:
      
          ```
          Detected bash shell on your system...
          Do you want ghcup to automatically add the required PATH variable to "/home/user/.bashrc"?

          [P] Yes, prepend  [A] Yes, append  [N] No  [?] Help (default is "P").
          ```

          Type `P` and press `<ENTER>`.

      3.  Installing the Haskell language-server:
      
          ```
          Do you want to install haskell-language-server (HLS)?
          HLS is a language-server that provides IDE-like functionality
          and can integrate with different editors, such as Vim, Emacs, VS Code, Atom, ...
          Also see https://haskell-language-server.readthedocs.io/en/stable/

          [Y] Yes  [N] No  [?] Help (default is "N").
          ```

          Type `Y` and press `<ENTER>`.

      4.  Adapt the behaviour of Stack:

          ```
          Do you want to enable better integration of stack with GHCup?
          This means that stack won't install its own GHC versions, but use GHCup's.
          For more information see:
            https://docs.haskellstack.org/en/stable/configure/customisation_scripts/#ghc-installation-customisation
          If you want to keep stack's vanilla behavior, answer 'No'.

          [Y] Yes  [N] No  [?] Help (default is "Y").
          ```

          Type `Y` and press `<ENTER>`.

      5.  Starting the installation:
      
          ```
          Press ENTER to proceed or ctrl-c to abort.
          Installation may take a while.
          ```

          Press `<ENTER>`.

  3.  To be able to execute GHCup re-start your terminal.


#### Other Operating Systems

See <https://www.haskell.org/ghcup/install/>.


## Haskell IDEs

There are many text editors that can be used as an IDE for Haskell. See e.g.
<https://wiki.haskell.org/IDEs> for an overview.

**Recommendation:** [VSCodium][vscodium] together with its
[Haskell][vscode-haskell] extension provides an easy-to-use Haskell IDE for
Linux, macOS and Windows.
Note that you need to have to install GHCup (see [above](#ghcup)) on
your system before launching the extension.


### Installing VSCodium

#### Debian, Ubuntu, Linux Mint

  1.  Add the GPG signature key of the developer of VSCodium to your system:

      ```
      sudo wget https://gitlab.com/paulcarroty/vscodium-deb-rpm-repo/raw/master/pub.gpg -O /usr/share/keyrings/vscodium-archive-keyring.asc
      ```

  2.  Add the repository of VSCodium to your system's `sources.list` file:

      ```
      echo 'deb [ signed-by=/usr/share/keyrings/vscodium-archive-keyring.asc ] https://paulcarroty.gitlab.io/vscodium-deb-rpm-repo/debs vscodium main' | sudo tee /etc/apt/sources.list.d/vscodium.list
      ```

  3.  Install VSCodium:

      ```
      sudo apt update && sudo apt install codium
      ```

#### Other Operating Systems

See <https://vscodium.com/#install>.


### Installing VSCodium's Haskell Extension

  1.  Open VSCodium.

  2.  Open its `Extensions` panel (`View` → `Extensions`).

  3.  Type "Haskell" into its search field.

  4.  Click on the `Install` button attached to the extension `Haskell` that
      should be shown in a list below the search field.


## Stack

Naproche is provided as a [Stack][stack] project. Stack is a tool to build
Haskell projects and manage their dependencies. You only have to install Stack
if you want to build and run the *command line interface* of Naproche. To build
and run the *Isabelle/jEdit interface* of Naproche, you do **not** need to
install Stack on your system.


### Installing Stack

#### Debian, Ubuntu, Linux Mint

If you set up GHCup via the [above](#ghcup) instructions, Stack should already
be installed on your system.
If not, you can install via one of the following methods:

  * Via GHCup (recommended):

    ```
    ghcup install stack
    ```

  * Directly:

    ```
    curl -sSL https://get.haskellstack.org/ | sh
    ```


#### Other Operating Systems

See <https://docs.haskellstack.org/en/stable/#how-to-install-stack>.


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


[haskell]: <https://en.wikipedia.org/wiki/Haskell>
[learn-you-a-haskell]: <https://www.learnyouahaskell.com/>
[vscodium]: <https://vscodium.com/>
[debian]: <https://www.debian.org/>
[ubuntu]: <https://ubuntu.com/>
[mint]: <https://www.linuxmint.com/>
[endeavour]: <https://endeavouros.com/>
[manjaro]: <https://manjaro.org/>
[windows]: <https://www.microsoft.com/windows>
[vscode-haskell]: <https://marketplace.visualstudio.com/items?itemName=haskell.haskell>
[stack]: <https://docs.haskellstack.org/en/stable/>
[ghcup]: <https://www.haskell.org/ghcup/>
[hoogle]: <https://hoogle.haskell.org/>
[cd]: <https://en.wikipedia.org/wiki/Cd_(command)>
[haddock]: <https://haskell-haddock.readthedocs.io/latest/>
