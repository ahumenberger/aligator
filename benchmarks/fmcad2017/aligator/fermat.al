WHILE[ (r!=0),
    IF[ (r>0),
        r:=r-v;
        v:=v+2,
        r:=r+u;
        u:=u+2
    ]
]