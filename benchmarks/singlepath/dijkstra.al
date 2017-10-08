WHILE[ (x!=1),
    x:=x/4;
    h:=p+x;
    p:=p/2;
    IF[ (r>=h),
        p:=p+x;
        r:=r-h
    ]
]
