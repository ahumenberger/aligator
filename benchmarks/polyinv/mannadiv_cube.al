WHILE[( y > 0),
  IF[(t == x^2),
    y := y - 3*x - 1;
    t := 0;
    x := x + 1,
    y := y - 3;
    t := t + 1
  ]
]