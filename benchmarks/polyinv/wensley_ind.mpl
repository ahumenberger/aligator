restart;
new_lib_dir := "/Users/ajobin/Desktop/maple_exemples/mapleLib";
libname := new_lib_dir, libname;
with(InvPol);
with(DivInductif);
with(SolveTools);

#################################
# Real division algorithm (ind) #
#################################

# /* Wensley's algorithm for real division */
#
# float division (float P, float Q, float E)
# pre(   Q > P  &&  P >= 0  &&  E > 0   );
#     {
#     float a,b,d,y;
#
#     a=0;
#     b=Q/2;
#     d=1;
#     y=0;
#
#     inv(   a == Q*y   &&   b == Q*d/2   &&   P/Q - d < y   &&   y <= P/Q   );
#     while( d>= E)
#         {
#         if (P< a+b)
#             {
#             b=b/2;
#             d=d/2;
#             }
#         else
#             {
#             a=a+b;
#             y=y+d/2;
#             b=b/2;
#             d=d/2;
#             }
#         }
#
# return y;
# }
# post(   P/Q >= result   &&   result > P/Q - E   );


st:=time();
# variables du programme
listVar := [Q, a, b, d, y];
# invariant parametre
deg := 2:
paramg := u:
g := generePol(listVar, deg, paramg):
listParam := genereListParamDeg(listVar, deg, paramg);

# contraintes generees par la branche then (lambda = 1/2)
cont1 := contAffectLambda(g, [b=(1/2)*b, d=(1/2)*d], lam, listVar);

# contraintes generees par la branche else (lambda = 1/2)
cont2 := contAffectLambda(g, [a=a+b, y=y+(1/2)*d, b=(1/2)*b, d=(1/2)*d], lam, listVar);

# la garde du if (x>y) est hors sémantique; la contrainte generee par
# le if est l'union de celles generees dans chaque branche
cont := [op(cont1),op(cont2)];

# contraintes generees par les affectations initiales (non ind)
contInit:= listEqtCoeff(listVar, [subs(op(miroir([a=0, b=(1/2)*Q, d=1, y=0])), g)]);

# contraintes du systeme
contSys := [op(cont),op(contInit)];


################################################
assume(lam<>0);
assume(lam<>1);

lP := [lam,op(genereListParam(u,binomial(2+nops(listVar),nops(listVar))))]:
ss := PolynomialSystem(contSys,lP,{lam-1});

subs(ss,g);


# Les invariants sont donc les suivants :
# (ad = 2*by) && (2*b = Qd)
# ce qui permet de trouver les invariants (si d not= 0):
# (a = Qy) && (b = Qd/2)
# OK

expanded_time:=time()-st;




