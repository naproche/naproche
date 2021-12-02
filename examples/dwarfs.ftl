\documentclass{article}

\usepackage[utf8]{inputenc}
\usepackage[english]{babel}
\usepackage{amssymb}
\usepackage{../lib/tex/naproche01}

\title{Murder at Dreadsbury Mansion (Pelletier Problem 55)}
\author{\Naproche{} Formalization: Steffen Frerix and Peter Koepke}
\date{2018 and 2021}

\begin{document}
  \pagenumbering{gobble}

  \maketitle
\section{Introduction}

\begin{forthel}
Signature.
A dwarf is a notion.

Signature.
Sigbert is a dwarf.

Signature.
Tormund is a dwarf.

Let aDwarf denote a dwarf.

Signature. A hat is a notion.

Let aHat denote a hat.

Signature.
The hat of aDwarf is a hat.

Signature. A color is a notion.

Signature.
white is a color.

Signature.
black is a color.

Let aColor denote a color.

Signature. The color of aHat is a color.

Axiom.
The color of the hat of aDwarf is white or 
the color of the hat of aDwarf is black.


Signature.
aDwarf names aColor is an atom.

Signature.
The opposite color of aColor is a color.

Axiom.
The opposite color of white is black.

Axiom.
The opposite color of black is white.

Definition. Both dwarfs get released iff some Dwarf D names the color
of the hat of D.


Axiom.
Sigbert names the opposite color of the color of the hat of Tormund.

Axiom.
Tormund names the color of the hat of Sigbert.


Proposition.
Both dwarfs get released.

\end{forthel}
\end{document}


