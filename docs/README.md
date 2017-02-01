# ALIGATOR Mathematica Package

Aligator is a Mathematica software package for generating loop invariants.

## Installation

### Dependencies

Aligator requires the Mathematica packages [Hyper](http://www.fmf.uni-lj.si/~petkovsek/software.html), FastZeil and Dependencies, where the latter two are part of the compilation package [ErgoSum](https://www.risc.jku.at/research/combinat/software/ergosum/).

## Examples

```
Aligator[
  WHILE[y > 0,
    t1 := t2;
    t2 := a;
    a := 5 (n + 2)*t2 + 6 ((n)^2 + 3 (n) + 2) t1;
    b := 2 b;
    c := 3 (n + 1) c;
    d := (n + 1) d
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

## Publications

[Download](/README.md)
