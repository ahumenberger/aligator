restart;
new_lib_dir := "/Users/ajobin/Desktop/maple_exemples/mapleLib";
libname := new_lib_dir, libname;
with(InvPol);
with(DivInductif);
with(SolveTools);

#########################################
# Calcul de la racine carree de n (ind) #
#########################################
# /* algorithm computing the floor of the square root of a natural number */
#
# int sqrt (int n)
# pre( n >= 0 );
#     {
#     int a,su,t;
#
#     a=0;
#     su=1;
#     t=1;
#
#     inv(    a ^2 <= n   &&   t == 2*a + 1   &&   su == ( a + 1 ) ^2    );
#     while ( su <= n )
#         {
#         a=a+1;
#         t=t+2;
#         su=su+t;
#         }
#
#     return a;
#     }
# post(   result ^2 <= n    &&   ( result + 1 ) ^2 > n   );

st:=time();

# variables du programme
listVar := [a, su, t];
# invariant parametre
deg := 2:
paramg := v:
g := generePol(listVar, deg, paramg):
listParam := generelistParam(listVar, deg, paramg):

# invariant genere par la methode inductive (les affectations
# initiales sont prises en compte)
hh := automAffectLin(g, [a=a+1, t=t+2, su=su+t], [a=0, su=1, t=1], listVar, deg, paramg);
# rendre l invariant genere plus lisible en "inversant" les parametres
ll := listEqtCoeff(genereListParam(v,14), [hh[1]]);

# Les invariants generes correspondent a ceux trouves par Carbonell
PolynomialSystem(ll,listVar);


###################################
# Comparaison avec l approche MOS #
###################################

# Avec MOS (cf sqrt_MOS), _ iterations de boucles avant
# stabilite ...

expanded_time:=time()-st;
