WHILE[(y*(y-1) != 0),
  IF[(t == x),
    y := y - 1;
    t := 0;
    x := x + 1,
    y := y - 2;
    t := t + 1
  ]
]