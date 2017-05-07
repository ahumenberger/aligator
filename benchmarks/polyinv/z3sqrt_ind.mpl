restart;
new_lib_dir := "/Users/ajobin/Desktop/maple_exemples/mapleLib";
libname := new_lib_dir, libname;
with(InvPol);
with(DivInductif);
with(SolveTools);

################
# z3sqrt (ind) #
################
# /* program for computing square roots, by Zuse */
#
# float z3sqrt (float a, float err)
# pre( a>= 1 && err > 0 );
#     {
#     float r,q,p,e;
#
#     r = a-1;
#     q = 1;
#     p = 1/2;
#
#     inv( q^2 + 2*r*p == a && err > 0 && p >= 0 && r >= 0 );
#     while ( 2*p*r >= e )
#         {
#         if ( 2*r-2*q-p >= 0 )
#             {
#             r = 2*r-2*q-p;
#             q = q+p;
#             p = p/2;
#             }
#         else
#             {
#             r = 2*r;
#             p = p/2;
#             }
#         }
#
#         return q;
#     }
# post( q^2 >= a && q^2+err < a );

st := time();

# variables du programme
listVar := [r, q, p, a];
# invariant parametre
deg := 2;
paramg := u;
g := generePol(listVar, deg, paramg);
listParam := genereListParamDeg(listVar, deg, paramg);

# contraintes generees par la branche 1
cont1 := contAffect(g, [r=2*r-2*q-p, q=q+p, p=(1/2)*p], listVar);

# contraintes generees par la branche 2
cont2 := contAffect(g, [r=2*r, p=(1/2)*p], listVar);

# la contrainte generee par le if est l'union de celles generees
# dans chaque branche
cont := [op(cont1),op(cont2)];

# contraintes generees par les affectations initiales (non ind)
contInit:= listEqtCoeff(listVar, [subs(op(miroir([r=a-1, q=1, p=1/2])), g)]);

# contraintes du systeme
contSys := [op(cont),op(contInit)];
ss := Linear(contSys, listParam);

# invariant genere
gg := subs(ss, g);

expanded_time := time()-st;
