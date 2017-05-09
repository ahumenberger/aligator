WHILE[ (b!=B),
    x:=2*x;
    b:=b/2;
    IF[ (r>=b),
        x:=x+1;
        r:=r-b
    ]
]