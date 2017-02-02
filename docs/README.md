# ALIGATOR Mathematica Package

Aligator is a Mathematica software package for generating loop invariants.

## Installation

To install Aligator download `Aligator.m` from the repository and put it somewhere Mathematica can
find it.

### Dependencies

Aligator requires the Mathematica packages [Hyper](http://www.fmf.uni-lj.si/~petkovsek/software.html), FastZeil and Dependencies, where the latter two are part of the compilation package [ErgoSum](https://www.risc.jku.at/research/combinat/software/ergosum/). Thus, before you can use Aligator you have to install those packages first.

## Examples

We provide an introductory example for computing all polynomial invariants among
the program variables `a`, `b`, `c` and `d`.

```
<< Aligator` (* Load Aligator *)

Aligator[
  WHILE[y > 0,
    t1 := t2;
    t2 := a;
    a := 5 (n + 2) t2 + 6 (n^2 + 3n + 2) t1;
    b := 2 b;
    c := 3 (n + 2) c;
    d := (n + 2) d
  ],
  LoopCounter -> n,
  IniVal -> {
    t1:=1;
    t2:=1;
    a:=1;
    b:=1;
    c:=1;
    d:=1
  }
]
```

The output of Aligator is a conjuction of the elements of the Gröbner basis of
the ideal of algebraic relations among `a`, `b`, `c` and `d` providing a finite
representation of all polynomial invariants among those.

```
25 d^2 == (7 a - 12 b c)^2
```

If no starting values (`IniVal`) are given, then the invariants contain the
starting values in the form of `a[n]` corresponding to the n-th value of the
sequence represented by `a`.

```
d^2 (-6 a[0] + a[1])^2 b[0]^2 c[0]^2 == (6 b c (a[0] + a[1]) - 7 a b[0] c[0])^2 d[0]^2
```

More examples are provided in the repository.

## Publications

1. Laura Kovács. A Complete Invariant Generation Approach for P-solvable Loops. In *Proceedings of the
International Conference on Perspectives of System Informatics (PSI)*, volume 5947 of *LNCS*, pages 242–256,
2009.

2. Laura Kovács. Reasoning Algebraically About P-solvable Loops. In *Proceedings of the International Conference
on Tools and Algorithms for the Construction and Analysis of Systems (TACAS)*, volume 4963 of *LNCS*,
pages 249–264, 2008.

3. Laura Kovács. Aligator: A Mathematica Package for Invariant Generation (System Description). In *Proceedings
of the International Joint Conference on Automated Reasoning (IJCAR)*, volume 5195 of *LNCS*, pages
275–282, 2008.

4. Laura Kovács. Invariant Generation with Aligator. In *Proceedings of Austrian-Japanese Workshop on
Symbolic Computation in Software Science (SCCS)*, number 08-08 in *RISC-Linz Report Series*, pages 123–
136, 2008.

4. Laura Kovács. Aligator: a Package for Reasoning about Loops. In *Proceedings of the International Conference
on Logic for Programming, Artificial Intelligence and Reasoning – Short Papers (LPAR-14)*, pages 5–8, 2007.

