WHILE[ ((s>=d)&&(r!=0)),
  IF[ (2*r-rp+q<0),
    t:=r;
    r:=2*r-rp+q+d+2;
    rp:=t;
    q:=q+4;
    d:=d+2,
    IF[ ((2*r-rp+q>=0)&&(2*r-rp+q<d+2)),
      t:=r;
      r:=2*r-rp+q;
      rp:=t;
      d:=d+2,
      IF[ ((2*r-rp+q>=0)&&(2*r-rp+q>=d+2)&&(2*r-rp+q<2*d+4)),
        t:=r;
        r:=2*r-rp+q-d-2;
        rp:=t;
        q:=q-4;
        d:=d+2,
        t:=r;
        r:=2*r-rp+q-2*d-4;
        rp:=t;
        q:=q-8;
        d:=d+2
      ]
    ]
  ]
]