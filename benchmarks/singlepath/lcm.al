WHILE[(x!=y),
  IF[(x>y),
    x := x-y;
    v := v+u,
    y := y-x;
    u := u+v
  ]
]