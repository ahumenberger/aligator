WHILE[(y3 != 0),
  IF[(y2 + 1 == x2),
    y1 := y1 + 1;
    y2 := 0;
    y3 := y3 - 1,
    y2 := y2 + 1;
    y3 := y3 - 1
  ]
]