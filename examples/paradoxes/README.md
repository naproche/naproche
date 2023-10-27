# Paradoxes

A collection of well-known mathematical and logical paradoxes.


## Contents

  * [The Barber Paradox](source/barber.ftl.tex)

  * [Burali-Forti's Paradox](source/burali-forti.ftl.tex)

  * [Cantor's First Paradox](source/cantor_1.ftl.tex)

  * [Cantor's Second Paradox](source/cantor_2.ftl.tex)

  * [Curry's Paradox][source/curry.ftl.tex]

  * [The Drinker Paradox](source/drinker.ftl.tex)

  * [Hilbert's Paradox](source/hilbert.ftl.tex)

  * [The Russell-Myhill Paradox](source/russell-myhill.ftl.tex)

  * [Russell's Paradox](source/russell.ftl.tex)


## Usage

This directory forms an sTeX archive.
To be able to convert the `.tex` files in the `source` directory to PDF or HTML,
follow the below instructions.

1.  Set up sTeX and a local `MathHub` directory as described in section *1
    Introduction & Setup* of [The sTeX3 Package Collection][sTeX-doc].

2.  Mount your `naproche` directory to your `MathHub` directory (a simple
    symlink might not suffice), e.g. via

    ```
    mount <path-to-naproche> <path-to-MathHub>/naproche
    ```

    where `<path-to-naproche>` and `<path-to-MathHub>` have to be replaced with
    the (absolute) paths to your `naproche` and `MathHub` directory,
    respectively.

    **Optional:** To automatically mount your `naproche` directory to your
    `MathHub` directory at boot you can add the following line to your
    `/etc/fstab` (again with the appropriate replacements for
    `<path-to-naproche>` and `<path-to-MathHub>`):

    ```
    <path-to-naproche> <path-to-MathHub>/naproche none bind
    ```

To be able to successfully compile the `.tex` files in the `source` directory
to, e.g., PDF or HTML make sure to run the respective compiler (e.g.
[pdfTeX][pdfTeX] or [RusTeX][RusTeX]) from within the
`<path-to-MathHub>/naproche` directory and not from within the
`<path-to-naproche>` directory.


## Copyright

All formalizations in this directory (and its subdirectories) are licensed under
a [Creative Commons “CC0 1.0 Universal”][CC0] license.


[sTeX-doc]: <https://github.com/slatex/sTeX/blob/main/doc/stex-doc.pdf>
[CC0]: <https://creativecommons.org/publicdomain/zero/1.0/deed.en>
[pdfTeX]: <https://tug.org/applications/pdftex/index.html>
[RusTeX]: <https://github.com/slatex/RusTeX>
