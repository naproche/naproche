# Git and GitHub

Naproche is provided as a [Git][git] repository. Git is a distributed version
control system that can be used to track changes of the files in a repository
and thus to facilitate collaborative software development.
The Git repository of Naproche is hosted on [GitHub][github], a platform to
manage and store code, at <https://github.com/naproche/naproche>.

The following sections explain how to obtain a copy of the Naproche repository
where you can edit the source files and how to contriubte changes on them to
the repository hosted on GitHub.

For a list of more in-depth introductions to Git, see e.g.
<https://git-scm.com/doc/ext>.


## Installing Git

First, you have to install Git on your system. See
<https://git-scm.com/downloads> for installation instructions for Git on Linux,
macOs and Windows.


## Cloning the Naproche Repository

To get a copy of the Naproche repository on your local system, *clone* the
repository by executing either of the following command in a terminal (from
within any directory of your choice).

  * If you have an GitHub account with an SSH key accociated with it (see
    <https://docs.github.com/en/authentication/connecting-to-github-with-ssh>
    for details), you can clone the repository via SSH:

    ```
    git clone git@github.com:naproche/naproche.git
    ```

  * Otherwise you can clone it via HTTPS:

    ```
    git clone https://github.com/naproche/naproche.git
    ```

After that there should be a direcory named `naproche`, in the following refered
to as `$NAPROCHE_HOME`, within the directory in which you executed the above
command. This directory is an exact copy of the Naproche repository on GitHub
and can freely be edited by you.


## Committing Changes to Your Local Git History

...


## Committing Changes to the GitHub Repository

...


[git]: <https://git-scm.com/>
[github]: <https://github.com/>
