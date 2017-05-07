restart;
new_lib_dir := "/Users/ajobin/Desktop/maple_exemples/mapleLib";
libname := new_lib_dir, libname;
with(InvPol);
with(DivInductif);
with(SolveTools);

#################################################
# Calcul simultane de GCD et LCM de (a,b) (ind) #
#################################################
# /* algorithm for computing simultaneously the GCD and the LCM, by Sankaranarayanan */
#
# int lcm (int a, int b)
# pre( a>0 && b>0 );
#     {
#     int x,y,u,v;
#
#     x=a;
#     y=b;
#     u=b;
#     v=0;
#
#     inv( GCD(x,y) == GCD(a,b) && x*u + y*v == a*b );
#     while(x!=y)
#         {
#
#         inv( GCD(x,y) == GCD(a,b) && x*u + y*v == a*b );
#         while (x>y)
#             {
#             x=x-y;
#             v=v+u;
#             }
#
#         inv( GCD(x,y) == GCD(a,b) && x*u + y*v == a*b );
#         while (x<y)
#             {
#             y=y-x;
#             u=u+v;
#             }
#         }
#     return u+v;
#     }
# post( result == LCM(a,b) );


st:=time();

# variables du programme
listVar := [x, y, u, v, a, b];
# invariant parametre
deg := 2;
paramg := t;
g :=generePol(listVar, deg, paramg);
listParam :=genereListParamDeg(listVar, deg, paramg);

# cont1 = contraintes "inductives" generees par le 1er while
cont1:=contAffect(g, [x=x-y, v=v+u], listVar);
# cont2 = contraintes "inductives" generees par le 2eme while
cont2:=contAffect(g, [y=y-x, u=u+v], listVar);

# contraintes generees par l inductivite
cont:=[op(cont1),op(cont2)];

# contraintes generees par les affectations initiales (non ind)
contInit:= listEqtCoeff(listVar ,[subs(op(miroir([x=a, y=b, u=b, v=0])), g)]);

# contraintes du systeme
contSys := [op(cont),op(contInit)];
ss := Linear(contSys, listParam);

# invariant genere
subs(ss, g);
# OK
# (memes invariant que celui de Carbonell)


expanded_time := time()-st;
