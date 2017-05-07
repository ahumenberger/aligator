restart;
new_lib_dir := "/Users/ajobin/Desktop/maple_exemples/mapleLib";
libname := new_lib_dir, libname;
with(InvPol);
with(DivInductif);
with(SolveTools);

################
# fermat (ind) #
################
# /* program computing a divisor for factorisation, by Bressoud */
#
# int fermat(int N, int R)
# pre(  N >= 1  &&   (R-1) ^2 < N   &&   N <= R^2  &&  N%2 == 1  );
#     {
#     int u,v,r;
#
#
#     u=2*R+1;
#     v=1;
#     r=R*R-N;
#
#     inv(   4*(N + r) == u^2 - v^2 - 2*u + 2*v   &&   v%2 == 1   &&   u%2 == 1   &&   N >= 1  );
#     while ( r!=0 )
#         {
#
#         inv( 4*(N+r)==u*u-v*v-2*u+2*v && v%2==1 && u%2==1 && N>=1 );
#         while ( r>0 )
#             {
#             r=r-v;
#             v=v+2;
#             }
#
#         inv( 4*(N+r)==u*u-v*v-2*u+2*v && v%2==1 && u%2==1 && N>=1 );
#         while ( r<0 )
#             {
#             r=r+u;
#             u=u+2;
#             }
#         }
#
#     assert(u!=v);
#     return((u-v)/2);
#     }
# post(N % result==0);

st:=time();

# variables du programme
listVar := [u, v, r, R, N];
# invariant parametre
deg := 2;
paramg := a;
g := generePol(listVar, deg, paramg);
listParam := genereListParamDeg(listVar, deg, paramg);

# contraintes generees par les affectations initiales (non ind)
contInit:= listEqtCoeff(listVar, [subs(op(miroir([u=2*R+1, v=1, r=R*R-N])), g)]);

# contraintes generees par le premier while
cont1 := contAffect(g, [r=r-v, v=v+2], listVar);

# contraintes generees par le 2eme while
cont2 := contAffect(g, [r=r+u, u=u+2], listVar);

# merge des contraintes while
cont := [op(cont1),op(cont2)];

# contraintes du systeme
contSys := [op(cont),op(contInit)];
ss := Linear(contSys,listParam);

# invariant genere
gg := subs(ss, g);

expanded_time := time()-st;
