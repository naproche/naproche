# Set Theory in ForTheL

These are formalizations of basic axiomatic set theory. The content is inspired by the [script](http://www.math.uni-bonn.de/ag/logik/teaching/2018WS/set_theory/current_scriptum.pdf) of the lecture *Set Theory* held by Prof. Peter Koepke at the University of Bonn in the winter term 18/19.  
The formalization finishs with the proof of Silver's Theorem about the continuum function at singular cardinals of uncountable cofinality (page 52 in the script).

These ForThel files can be checked by Naproche-SAD, either with the [source code](https://github.com/Naproche/Naproche-SAD) or the [Isabelle/jEdit integration](https://files.sketis.net/Isabelle_Naproche-20190611/).  
All folder `Formalizations` has to be copied in the example-folder of Naproche-SAD. In the application it is the folder  
```
Isabelle_Naproche-20190611.app/Contents/Resources/Isabelle_Naproche-20190611/contrib/naproche-20190418/examples.
```

The total checking time of all files is about 4 hours (depending on the computer).

The first times were checked on a computer with a 3.2 GHz Quad-Core Intel Core i5 and 16 GB 1333 MHz DDR3 RAM.  
The second times were checked on a computer with a 2.3 GHz 8-Core Intel Core i9 and 16 GB 2400 MHz DDR4 RAM.

The times vary depending on background activity.

| file name                         | checking time 1       | checking time 2       |
| --------------------------------- | --------------------- | --------------------- |
| P01-ZF-Sets                       | 01:40.00              | 01:31.24              |
| P02-Cardinals_Part_1              | 09:39.97              | 08:48.37              |
| P03-Von_Neumann_Hierarchy         | 03:46.15              | 03:29.25              |
| P04-Ordinal_Arithmetic            | 06:53.26              | 06:17.09              |
| P05-Mostowski_Collapse            | 11:30.23              | 10:27.10              |
| P06-Transitive_Closure            | 04:13.38              | 03:29.88              |
| P07-Cardinals_Part_2              | 18:58.94              | 17:38.09              |
| P08-Cardinal_Arithmetic           | 25:21.26              | 23:37.73              |
| P09-Cofinality                    | 13:24.79              | 12:29.44              |
| P10-Koenigs_Lemma                 | 19:49.29              | 18:39.89              |
| P11-Gimel_Function                | 14:37.54              | 13:27.62              |
| P12-Cardinal_Exponentiation       | 10:56.07              | 09:58.31              |
| P13_GCH                           | 03:35.76              | 03:14.86              |
| P14-Clubs                         | 08:42.63              | 08:03.66              |
| P15-Stationary_Sets               | 11:09.74              | 10:00.70              |
| P16-Fodors_Lemma                  | 10:55.87              | 09:56.65              |
| P17-Disjoint_Stationary_Functions | 09:36.64              | 08:21.55              |
| P18-Almost_Disjoint_Functions     | 21:43.33              | 20:16.52              |
| P19-The_Last_Lemma                | 19:26.14              | 17:42.16              |
| P20-Silvers_Theorem               | 03:23.56              | 03:10.30              |
|                                   |                       |                       |
| Example_from_1.1.1                | 00:00.30              | 00:00.18              |
| Formalizing_Pairs_and_Functions   | 00:23.52              | 00:22.03              |
