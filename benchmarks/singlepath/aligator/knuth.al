WHILE[ ((s>=d)&&(r!=0)),
  IF[ (2*r-rp+x<0),
    t:=r;
    r:=2*r-rp+x+d+2;
    rp:=t;
    x:=x+4;
    d:=d+2,
    IF[ ((2*r-rp+x>=0)&&(2*r-rp+x<d+2)),
      t:=r;
      r:=2*r-rp+x;
      rp:=t;
      d:=d+2,
      IF[ ((2*r-rp+x>=0)&&(2*r-rp+x>=d+2)&&(2*r-rp+x<2*d+4)),
        t:=r;
        r:=2*r-rp+x-d-2;
        rp:=t;
        x:=x-4;
        d:=d+2,
        t:=r;
        r:=2*r-rp+x-2*d-4;
        rp:=t;
        x:=x-8;
        d:=d+2
      ]
    ]
  ]
]