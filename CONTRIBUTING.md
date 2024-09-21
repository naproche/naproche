# Contributing to Naproche

## Resources

 - **[An argument for controlled natural languages in Mathematics](https://jiggerwit.files.wordpress.com/2019/06/header.pdf)**:
   Motivation for and future direction of CNLs in general.
 - **[Automatic Proof-Checking of Ordinary Mathematical Texts](http://ceur-ws.org/Vol-2307/paper13.pdf)**:
   A short introduction to this project.
 - **[The syntax and semantics of the ForTheL language, 2007](http://nevidal.org/download/forthel.pdf)**:
   In-depth paper on the ForTheL language.
 - **[Méthodes de formalisation des connaissances et des raisonnements mathématiques: aspects appliqués et théoriques](http://tertium.org/papers/thesis-07.fr.pdf)**:
   Andrei Paskevich's PhD thesis on this topic (in French)
 - **[Handbook of Practical Logic and Automated Reasoning](https://www.cl.cam.ac.uk/~jrh13/atp/)**:
   Textbook on logic and automated theorem proving. Some functions in the code base are literal translations of the OCaml code presented in the book.


## Haskell

Naproche is written in the functional programming language [Haskell][haskell].
If you are not familiar with Haskell (yet), have a look at
[`doc/haskell.md`](doc/haskell.md).


## Changelog

It is highly encouraged to document all changes on Naproche in the file
[CHANGELOG.md](CHAMGELOG.md).


## Abbreviations

Using these abbreviations is encouraged when writing/rewriting code, especially
for local variables.

Abbrev | Meaning
------ | -----------------------------
adj    | adjective
aff    | affirm/affirmation
asm    | assume/assumption
cont   | continuation
dec    | decrement
decl   | declaration
def    | definition
eps    | epsilon
eq     | equal/equality
err    | error
expr   | expression
fun    | function
hypo   | hypothesis
inc    | increment
instr  | instruction
pat    | pattern
predi  | predicate
prim   | primitive
sig    | signature
st     | state
sub    | substitution/substitute
symb   | symbol/symbolic
var    | variable


## To-Dos

The file [TODO.md](TODO.md) contains a list of pending to-dos. When an item has
been processed, plesase delete it from that list.


[haskell]: <https://en.wikipedia.org/wiki/Haskell>
