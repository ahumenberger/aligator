restart;
new_lib_dir := "/Users/ajobin/Desktop/maple_exemples/mapleLib";
libname := new_lib_dir, libname;
with(InvPol);
with(DivInductif);
with(SolveTools);

##########################################
#### petite erreur sur la page de R-Carbonell?
#### il faut changer l'ordre des affectations dans le dernier if
##########################################

##############################
# Product of 2 numbers (ind) #
##############################
# /* algorithm for computing the product of two natural numbers */
#
# int prod (int x,int y)
# pre( x >= 0 && y >= 0 );
#     {
#     int a,b,p,q;
#
#     a = x;
#     b = y;
#     p = 1;
#     q = 0;
#
#     inv( q+abp==xy );
#     while( a!=0 && b!=0 )
#         {
#         if ( a % 2 ==0 && b% 2 ==0 )
#             {
#             a =a/2;
#             b = b/2;
#             p = 4p;
#             }
#         else if ( a % 2 ==1 && b% 2 ==0 )
#             {
#             a =a-1;
#             q = q+bp;
#             }
#         else if ( a % 2 ==0 && b% 2 ==1 )
#             {
#             b =b-1;
#             q = q+ap;
#             }
#         else
#             {
################ NON ############
#             a =a-1;
#             b =b-1;
#             q = q+(a+b-1)p;
#################################
#             }
#         }
#     return z;
#     }
# post( result==xy );


st := time();

# variables du programme
listVar := [a, b, p, q, x, y]:
# invariant parametre
deg := 3:
paramg := u:
g := generePol(listVar, deg, paramg):
listParam := genereListParamDeg(listVar, deg, paramg):

# contraintes generees par la branche 1
cont1 := contAffect(g, [a=(1/2)*a, b=(1/2)*b, p=4*p], listVar):

# contraintes generees par la branche 2
cont2 := contAffect(g, [a=a-1, q=q+b*p], listVar):

# contraintes generees par la branche 3
cont3 := contAffect(g, [b=b-1, q=q+a*p], listVar):

# contraintes generees par la branche 4
cont4 := contAffect(g, [q=q+a*p+b*p-p, a=a-1, b=b-1], listVar):

# la contrainte generee par le if est l'union de celles generees
# dans chaque branche
cont := [op(cont1),op(cont2),op(cont3),op(cont4)]:

# contraintes generees par les affectations initiales (non ind)
contInit:= listEqtCoeff(listVar, [subs(op(miroir([a=x, b=y, p=1, q=0])), g)]):

# contraintes du systeme
contSys := [op(cont),op(contInit)]:
ss := Linear(contSys,listParam):

# invariant genere
gg := subs(ss, g);

expanded_time := time()-st;
