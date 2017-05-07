WHILE[ (a!=b),
  IF[ (a>b),
    a := a-b;
    p := p-q;
    r := r-s,
    b := b-a;
    q := q-p;
    s := s-r
  ]
]