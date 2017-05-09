WHILE[ (b!=B),
    q:=2*q;
    b:=b/2;
    IF[ (r>=b),
        q:=q+1;
        r:=r-b
    ]
]