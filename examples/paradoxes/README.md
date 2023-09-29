# Mathematical Paradoxes

A collection of well-known mathematical and logical paradoxes.


## Contents

  * [The Barber Paradox](source/barber.ftl.tex)

  * [Burali-Forti's Paradox](source/burali-forti.ftl.tex)

  * [Cantor's First Paradox](source/cantor_1.ftl.tex)

  * [Cantor's Second Paradox](source/cantor_2.ftl.tex)

  * [The Drinker Paradox](source/drinker.ftl.tex)

  * [Hilbert's Paradox](source/hilbert.ftl.tex)

  * [The Russell-Myhill Paradox](source/russell-myhill.ftl.tex)

  * [Russell's Paradox](source/russell.ftl.tex)


## Usage

...

Mount your `naproche` directory to your `MathHub` directory (a simple symlink
might not suffice), e.g. via

```
mount <path-to-naproche> <path-to-MathHub>/naproche
```

where `<path-to-naproche` and `<path-to-MathHub` have to be replaced with the
(absolute) paths to your `naproche` and `MathHub` directory, respectively.

**Optional:** To automatically your `naproche` directory to your `MathHub`
directory at boot you can add the following line to your `/etc/fstab`:

```
<path-to-naproche> <path-to-MathHub>/naproche none bind
```


## Copyright

All formalizations in this directory (and its subdirectories) are licensed under
a [Creative Commons “CC0 1.0 Universal”][CC0] license.


[CC0]: <https://creativecommons.org/publicdomain/zero/1.0/deed.en>
