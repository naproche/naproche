# Set Theory

A formalization of a ZF-like set theory


## Contents

1.  Sets  

    1.1 Sets  
    1.2 The powerset  
    1.3 Regularity  
    1.4 The symmetric difference  
    1.5 Ordered pairs  
    1.6 The Cartesian product

2.  Functions  

    2.1 Functions
    2.2 Image and preimage  
    2.3 Invertible functions  
    2.4 Functions and the symmetric difference  
    2.5 Functions and set-systems  
    2.6 Equipollency


## Dependency graph

![dependency graph](dependency-graph/graph.svg)


## Technical note

The file `set-theory.ftl.aux` must be kept in this directory in order to allow
for references to labels defined in `set-theory.ftl.tex` (and its subfiles) via
the LaTeX package `xr`. Such a "cross-document" reference is for instance used
in `$NAPROCHE/examples/cantor-schroeder-bernstein.ftl.tex`.
