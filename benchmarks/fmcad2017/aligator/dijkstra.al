WHILE[ (q!=1),
    q:=q/4;
    h:=p+q;
    p:=p/2;
    IF[ (r>=h),
        p:=p+q;
        r:=r-h
    ]
]
