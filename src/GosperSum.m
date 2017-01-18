(* Mixed Gosper's algorithm for Mma 3.0, by Marko Petkovsek *)
(* Mixed Poly for Mma 3.0, by Marko Petkovsek *)

(* October 6, 1996 *)
(* October 23, 1997: corr. treatment of Product in FactorialSimplify[expr] *)
(* October 30, 1997: impr. treatment of Product in FactorialSimplify[expr] *)
(* May 18, 1998: incl. treatment of qFac in FactorialSimplify[expr] *)
(* May 29, 1998: fixed bugs found by W. Gosper 
                 (added PowerExpand and Together to ToY *)


BeginPackage["GosperSum`"];

Off[General::spell1];


FactorialSimplify::usage = "FactorialSimplify[expr] is a simple-minded
simplification routine for expressions containing rational functions, 
Factorial, Factorial2, Binomial, Gamma, Pochhammer, and Product. 
The result is expressed by means of Binomial and Factorial functions.
FactorialSimplify[expr, n] simplifies linear combinations of terms
which are hypergeometric in n. Alias: FS.";

FS::usage = "FS is alias for FactorialSimplify.";

GetRatio::usage = "GetRatio[h, n] returns the rational consecutive-term
ratio h[n+1]/h[n] for a hypergeometric term h[n].";

GosperFunction::usage = "GosperFunction[r, n, qList:{}] uses 
Gosper's algorithm to find for a given rational function r[n, q1^n, .., qk^n] 
another rational function R[n, q1^n, .., qk^n] such that r NR - R == 1. 
If no such function exists then GosperFunction returns $Failed.";

GosperSum::usage = "GosperSum[term, {var, n0, n1}, qList:{}] finds 
a hypergeometric closed form for Sum[term, {var, n0, n1}] if possible. 
GosperSum[term, var, qList:{}] is the corresponding indefinite sum. 
Term can contain rational functions, Factorial, Factorial2, Binomial, Gamma, 
Pochhammer, Product, and qFac. GosperSum uses the generalization of Gosper's
algorithm to the mixed multibasic case by A.Bauer and M.Petkovsek.";

MixedNormalForm::usage = "MixedNormalForm[r, n, y] returns the normal form
{a, b, c} for the rational function r[n, y[q1], .., y[qk]].";

MixedPoly::usage = "MixedPoly[eqn, x[n], qList, paramList:{}] finds 
polynomial solutions of an inhomogeneous mixed recurrence with parameters.";

Zeil::usage = "Zeil[F, s[n], {k, lo, hi}] returns a recurrence rec of the form
Ls[n] == rhs[n] satisfied by the sum s[n] = Sum[F[n,k], {k, lo, hi}]. Here s,
n and k must be symbols.   Options of Zeil:
Rhs -> False suppresses the right hand side of the recurrence.
Certificate -> True returns {R, rec} where R is a rational function
such that G = RF satisfies LF[n,k] == G[n,k+1] - G[n,k].
Bases -> {q, ... } specifies the bases in case of a (multi)basic summand.
Start -> d starts the search for L at order d rather than 0."

Start::usage = "An option for Zeil specifying the starting value for the order 
of the sought recurrence. Default value: 0.";

Bases::usage = "An option for Zeil specifying the list of bases in the 
(multi)basic case. Default value: {}.";

Rhs::usage = "An option for Zeil specifying whether or not the right-hand side
of the recurrence is required. Default value: True.";

Certificate::usage = " An option of Zeil specifying whether or not a 
certificate of the recurrence is required. Default value: False.";

qFac::usage = "The q-factorial function: 
qFac[a,q,n] = Product[1 - a q^i, {i,0,n-1}].";

WZ::usage = "WZ[F, n, k, qList:{}] returns a rational function R(n,k) 
such that F(n,k) and G(n,k) := R(n,k) F(n,k) are a WZ pair: 
F(n+1,k) - F(n,k) = G(n,k+1) - G(n,k)." ;

ToY::usage = "ToY[expr, n, qList, y] replaces all appearances of q^n in expr
with y[q], for all q in qList." ;


Begin["Private`"];

Share[];

Unprotect[Power];
0^0 = 1;
Protect[Power];



(* WZ METHOD *)

WZ[F_, n_, k_, qList_:{}] :=
  Module[{rn, rk, rr},
    rn = GetRatio[F, n];
    rk = GetRatio[F, k];
    rr = Together[rn - 1];
    out = GosperFunction[
        Factor[rk (rr /. k->k+1) / rr], k, qList];
    If[out === $Failed, Return[$Failed],
                        Return[Together[rr out]] ]
  ];



(* FACTORIAL SIMPLIFY *)

rf[a_, 0] = 1;

rf[a_, n_Integer?Positive] := Product[a+i, {i,0,n-1}];

rf[a_, n_Integer?Negative] := 1 / Product[a-i, {i,1,-n}];


FS = FactorialSimplify;

FactorialSimplify[expr_] := 
  Module[{k, ex = expr /. 
               {Product[f_, {j_, n_}] :> Product[Factor[f], {j,1,n}],
                Product[f_, {n_}] :> f^n,
                Product[f_, {j_, a_, b_, s_}] :> 
                   Product[Factor[f] /. j -> a + k s, {k, 0, (b-a)/s}]},
          x},
     ex = ex //. 
       {Binomial[n_,k_] /; n-k =!= 0 -> rf[n-k,k]/rf[1,k] n/(n-k),
        Binomial[n_,k_] -> rf[n-k+1,k]/rf[1,k],
        Factorial[n_] -> rf[1,n],
        Gamma[x_] -> rf[1,x-1],
        Pochhammer[a_, x_] -> rf[a,x],
        Factorial2[a_?EvenQ n_ + b_.] /; EvenQ[b] -> 
           2^(a/2 n + b/2) (a/2 n + b/2)!,
        Factorial2[a_?EvenQ n_ + b_] /; OddQ[b] -> 
           2^(a/2 n + (b+1)/2) rf[1/2, a/2 n + (b+1)/2],
        Product[f_ g_, {j_, a_, b_}] ->
           Product[f, {j,a,b}] Product[g, {j,a,b}],
        Product[f_^k_, {j_, a_, b_}] /; FreeQ[k, j] ->
           Product[f, {j,a,b}]^k,
        Product[f_^k_, {j_, a_, b_}] /; FreeQ[f, j] :>
           f^GosperSum[k, {j,a,b}],
        Product[u_, {j_, a_, b_}] /; FreeQ[u, j] -> u^(b-a+1),
        Product[u_. j_ + v_., {j_, a_, b_}] /; FreeQ[u, j] && FreeQ[v, j] ->
           u^(b-a+1) rf[v/u + a, b-a+1],
        Product[(u_. j_ + v_.)^(-1), {j_, a_, b_}] /; 
             FreeQ[u, j] && FreeQ[v, j] ->
           1/(u^(b-a+1) rf[v/u + a, b-a+1])};
     ex = ex /. rf[a_, b_] :> rf[Expand[a], Expand[b]];
     ex = ex //. 
       {rf[a_, b_ + n_Integer?Positive] ->
          rf[a, b] rf[a+b, n],
        rf[a_, b_ + n_Integer?Negative] ->
          rf[a, b] / rf[a+b+n, -n],
        rf[a_ + n_Integer?Positive, b_] -> 
          rf[a, b]rf[a+b,n]/rf[a,n],
        rf[a_ + n_Integer?Negative, b_] -> 
          rf[a,b]rf[a+n,-n]/rf[a+b+n,-n],
        rf[a_, b_. + r_Rational?(# > 1 &)] ->
          rf[a, b+r-Floor[r]] rf[a+b+r-Floor[r], Floor[r]],
        rf[a_, b_. + r_Rational?Negative] ->
          rf[a, b+r-Ceiling[r]+1] / rf[a+b+r, 1-Ceiling[r]], 
        rf[a_. + r_Rational?(# > 1 &), b_] -> 
          rf[a+r-Floor[r], b]rf[a+r-Floor[r]+b,Floor[r]]/
            rf[a+r-Floor[r],Floor[r]],
        rf[a_. + r_Rational?Negative, b_] -> 
          rf[a+r, 1-Ceiling[r]]rf[a+r-Ceiling[r]+1,b]/
            rf[a+r+b,1-Ceiling[r]],
        qFac[a_, q_, b_ + n_Integer?Positive] -> 
            qFac[a, q, b] qFac[a q^b, q, n],
        qFac[a_, q_, b_ + n_Integer?Negative] -> 
            qFac[a, q, b] / qFac[a q^(b+n), q, -n]};
      ex = ex /. rf[a_, b_] /; a+b =!= 0 -> Binomial[a+b,b] b! a/(a+b);
      ex = ex /. rf[a_, b_] -> Binomial[a+b-1,b] b!;
      ex = ex /. Power[a_, b_] :> Power[a, Expand[b]];
      ex = ex /. (-1)^(b_+Optional[u_Integer]) Binomial[a_Integer?Negative, 
                       b_] c___ :> 
                         (-1)^u Binomial[b-a-1,-a-1] c;
      ex = ex /. Binomial[a_Integer?Negative, b_] :> 
                         (-1)^b Binomial[b-a-1,-a-1];
      ex = ex /. Binomial[a_ + b_, b_] :> 
                         (-1)^b Binomial[-a-1,b];
      ex = ex /. Binomial[Rational[m_?Positive,2], n_] :>
         (-1)^((m+1)/2) m!! Binomial[2n,n] / ((-1)^n 4^n Product[2n-k, 
              {k,1,m,2}]);
      ex = ex /. Binomial[Rational[m_?Negative,2], n_] :>
         Product[2n+k, {k,1,-m-2,2}] Binomial[2n,n] / ((-1)^n 4^n (-m-2)!!);
      Return[PostSimplify[MyFactor[ex, 
        {Factorial, Binomial, Factorial2, Gamma,
         Pochhammer, Product, qFac}]]] ];

(* FactorialSimplify[expr_] := 
  Module[{ex = expr, x},
     ex = ex //. 
       {Binomial[n_,k_] -> rf[n-k+1,k]/rf[1,k],
        Factorial[n_] -> rf[1,n],
        Gamma[x_] -> rf[1,x-1],
        Pochhammer[a_, x_] -> rf[a,x],
        Factorial2[a_?EvenQ n_ c_.+ b_] -> (a c)^n Product[
                     rf[(b+k)/(a c),n], {k,2,a c,2}],
        Product[f_ g_, {j_, a_, b_}] ->
           Product[f, {j,a,b}] Product[g, {j,a,b}],
        Product[f_^k_, {j_, a_, b_}] /; FreeQ[k, j] ->
           Product[f, {j,a,b}]^k,
        Product[u_, {j_, a_, b_}] /; FreeQ[u, j] -> u^(b-a+1),
        Product[u_. j_ + v_., {j_, a_, b_}] /; FreeQ[u, j] && FreeQ[v, j] ->
           u^(b-a+1) rf[v/u + a, b-a+1],
        Product[(u_. j_ + v_.)^(-1), {j_, a_, b_}] /; 
             FreeQ[u, j] && FreeQ[v, j] ->
           1/(u^(b-a+1) rf[v/u + a, b-a+1])};
     ex = ex /. rf[a_, b_] :> rf[Expand[a], Expand[b]];
     ex = ex //. 
       {rf[a_, b_ + n_Integer?Positive] ->
          rf[a, b] rf[a+b, n],
        rf[a_, b_ + n_Integer?Negative] ->
          rf[a, b] / rf[a+b+n, -n],
        rf[a_ + n_Integer?Positive, b_] -> 
          rf[a, b]rf[a+b,n]/rf[a,n],
        rf[a_ + n_Integer?Negative, b_] -> 
          rf[a,b]rf[a+n,-n]/rf[a+b+n,-n],
        rf[a_, b_. + r_Rational?(# > 1 &)] ->
          rf[a, b+r-Floor[r]] rf[a+b+r-Floor[r], Floor[r]],
        rf[a_, b_. + r_Rational?Negative] ->
          rf[a, b+r-Ceiling[r]+1] / rf[a+b+r, 1-Ceiling[r]], 
        rf[a_. + r_Rational?(# > 1 &), b_] -> 
          rf[a+r-Floor[r], b]rf[a+r-Floor[r]+b,Floor[r]]/
            rf[a+r-Floor[r],Floor[r]],
        rf[a_. + r_Rational?Negative, b_] -> 
          rf[a+r, 1-Ceiling[r]]rf[a+r-Ceiling[r]+1,b]/
            rf[a+r+b,1-Ceiling[r]]};
      ex = ex /. rf[a_, b_] -> Binomial[a+b-1,b] b!;
      ex = ex /. Power[a_, b_] :> Power[a, Expand[b]];
      Return[MyFactor[ex, 
        {Factorial, Binomial, Factorial2, Gamma,
         Pochhammer, Product, qFac}]] ];
*)      

MyFactor[ex_, heads_] := 
  Module[{flist, vars, exp},
    flist = Union[
      Cases[ex, _?(MemberQ[heads, Head[#]]&), Infinity]];
    vars = Table[Unique[f], {Length[flist]}];
    exp = ex /. Thread[flist -> vars];
    Return[Factor[exp] /. Thread[vars -> flist]] ];


Similar[r1_, r2_, n_] :=
  Module[{r, a, b, c, a1, b1, c1, y, num, den, k},
    r = Cancel[r2/r1];
    {num, den} = {Numerator[r], Denominator[r]};
    If[Coefficient[num, n, Exponent[num, n]] /
       Coefficient[den, n, Exponent[den, n]] =!= 1, Return[False]];
    {a,b,c} = MixedNormalForm[num/den, n, y];
    {a1,b1,c1} = MixedNormalForm[b/a, n, y];
    If[Together[a1/b1] =!= 1, Return[False]]; 
    Return[Together[c/c1]] ];
    
FindSimilar[diss_List, term_, n_] :=
  Module[{r, i, out, rat1, h1, rat2, h2,
          val, newrat, k, mult},
    out = 
      Scan[(
       {{rat1, h1}, i} = #;
        {rat2, h2} = term;
        r = Similar[rat1, rat2, n];
        If[r =!= False,
          k = 1;
          Off[Power::infy, Infinity::indet];
          val = h2/(h1 r) /. n -> k;
          While[!FreeQ[val, Indeterminate] || !FreeQ[val, DirectedInfinity],
            k++; val = h2/(h1 r) /. n -> k];
          On[Power::infy, Infinity::indet];
          mult = Together[1 + FS[val] r]; 
          If[mult === 0, Return[Delete[diss, i]]];
          newrat = Factor[rat1 (mult /. n->n+1) / mult];
          Return[ReplacePart[diss, {{newrat, h1 mult}, i}, i]] ]
       )&, diss];
    If[out === Null,
       Return[Append[diss, {term, Length[diss] + 1}]],
       Return[Thread[{First /@ out, Range[Length[out]]}]]]
  ];
  
FactorialSimplify[expr_, n_] /; RationalQ[expr, n] :=
    Together[expr];

FactorialSimplify[expr_, n_] :=
  Module[{den, ex, rat, ratios, diss},
    den = Denominator[expr];
    If[den =!= 1, 
       FS[Numerator[expr], n] / FS[den, n]];
    ex = Together /@ MakeList[expr, Plus];
    rat = Select[ex, RationalQ[#, n]&];
    ex = Complement[ex, rat];
    rat = Together[Plus @@ rat];
    ratios = GetRatio[#, n]& /@ ex;    
    ratios = Factor /@ ratios;
    diss = Fold[FindSimilar[#1, #2, n]&, {}, Thread[{ratios, ex}]];
    diss = First /@ diss;
    Return[rat + PostSimplify[Plus @@ (FormHg[#, n]& /@ diss)]]];
    
MaxRoot[p_, x_] := (* max nonnegative integer root, or -1 *)
  Module[{all},
      all = x /. Select[Solve[p == 0, x], FreeQ[#, Roots]&];
      If[all === x, all = {}];
      all = Select[all, IntegerQ[#] && # >= 0&];
      If[all === {}, all = {-1}];
  Return[Max[all]] ];


Transform[(n_ + a_Integer?Negative)^k_., n_] /; 
    FreeQ[k, n] := (n+a-1)!^k;

Transform[n_^k_., n_] /; FreeQ[k,n] := (n-1)!^k;

Transform[(n_ + a_)^k_., n_] /; FreeQ[{a,k}, n] := 
    Binomial[n+a-1,n]^k n!^k; 
(*    (-1)^n Binomial[-a,n]^k n!^k; *)

Transform[a_, n_] := Product[a /. n->j, {j, n-1}];
 

ToHg[{r_, h_}, n_] :=
  (* constructs a canonical hg. term for h from its c.t.r. r *)
  Module[{rr, lc, k, val},
    rr = Factor[r] /. {a_?(FreeQ[#,n]&) n + b_?(FreeQ[#,n]&) :> (n + b/a) a};
    rr = MakeList[rr, Times];
    lc = Select[rr, FreeQ[#, n]&];
    rr = Complement[rr, lc];
    lc = Times @@ lc;
    Scan[If[MatchQ[#, a_?(FreeQ[#,n]&) - n], lc = -lc]&, rr];
    rr = rr /. {a_?(FreeQ[#,n]&) - n -> n - a};
    rr = Transform[#, n]& /@ rr;
    rr = rr /. Binomial[m_, k_] -> Binomial[k-m-1,k]/(-1)^k;
    rr = lc^n (Times @@ rr);
    k = 1;
    Off[Power::infy, Infinity::indet];
    val = (h/rr) /. n -> k;
    While[!FreeQ[val, Indeterminate] || !FreeQ[val, DirectedInfinity],
      k++; val = (h/rr) /. n -> k];
    On[Power::infy, Infinity::indet];
    Return[rr val]
  ];
  
FormHg[{rat_, h_}, n_] :=
  Module[{a, b, c, a1, b1, c1, y},
    {a,b,c} = MixedNormalForm[rat, n, y];
    {a1,b1,c1} = MixedNormalForm[b/a, n, y];
    Return[Together[c/c1] ToHg[{b1/a1, h c1/c}, n]]
  ];
    

PostSimplify[expr_] :=
    Module[{ex = expr /. n_! :> (Expand[n])!, i},
        ex //.
            {n_!^k_. m_!^l_. :> Product[m + i, {i, n - m}]^k /;
                                 IntegerQ[Expand[n - m]] &&
                                 Expand[n - m] > 0 && Expand[k + l] == 0,
             n_!^k_. m_^l_. :> Expand[n + 1]!^k Expand[n + 1]^(l - k) /;
                                Expand[m - n] == 1 && Sign[k] == Sign[l],
             n_!^k_. m_^l_. :> (-1)^k Expand[n + 1]!^k Expand[m]^(l - k) /;
                               Expand[m + n] == -1 && Sign[k] == Sign[l],
             n_!^k_. n_^l_. :> Expand[n - 1]!^k /; Expand[k + l] == 0,
             n_!^k_. m_^l_. :> (-1)^k Expand[n - 1]!^k /;
                                  Expand[k + l] == 0 == Expand[n + m] } ];
                                  


(* MIXED NORMAL FORM *)

FindShift[a_, b_, x_] :=
  Module[{d = Exponent[a, x], a0, a1, b0, b1, h}, 
    If[Exponent[b, x] =!= d, Return[{}]];
    If[d === 0, Return[{0, {a, b}, a/b}]];
    a0 = Coefficient[a, x, d];
    a1 = Coefficient[a, x, d-1];
    b0 = Coefficient[b, x, d];
    b1 = Coefficient[b, x, d-1];
    h = Together[Det[{{a1,b1},{a0,b0}}]/(d a0 b0)];
    If[!IntegerQ[h] || h < 0 || Expand[b0 a - a0 (b /. x -> x+h)] =!= 0,
       {}, {h, {a, b}, a0/b0}]
  ];        
  
FindExponent[flist_, af_] := 
  Scan[If[#[[1]] === af, Return[#[[2]]]]&, flist] /. Null -> 0;
  
FactorOut[{alist_, blist_, a_, b_, c_}, {h_, {af_, bf_}, const_}, x_] :=
  Module[{d = Min[FindExponent[alist, af], FindExponent[blist, bf]]},
    {alist/.{af,n_}->{af,n-d}, blist/.{bf,n_}->{bf,n-d}, 
     a const^d / af^d, b / bf^d, c Product[bf /. x -> x+s, {s,0,h-1}]^d}
  ];
    
NormalForm[r_, x_] :=
  Module[{fr = Factor[r], a, b, alist, blist, shifts},
    a = Numerator[fr]; b = Denominator[fr];
    alist = Select[FactorList[a], !FreeQ[#, x]&];
    blist = Select[FactorList[b], !FreeQ[#, x]&];
    shifts = Select[Union @@ Outer[FindShift[#1, #2, x]&, 
                                   First /@ alist, First /@ blist],
                    # =!= {}&];
    Drop[Fold[FactorOut[#1,#2,x]&, {alist, blist, a, b, 1}, shifts], 2]
  ];
  
  
ToY[expr_, n_, qList_, y_] := 
  Together[PowerExpand[expr] /. 
           q_?(MemberQ[qList,#]&)^(a_. n + b_.) :> q^b y[q]^a];
  

GetMonomial[term_, y_] :=
  Which[term === 0,           0,
        FreeQ[term, y],       1,
        Head[term] =!= Times, term,
        True,                 Select[term, Not[FreeQ[#, y]]&] ];

GetCoefficient[expr_, mon_, y_] :=
  If[mon === 1, 
       Plus @@ Select[MakeList[expr, Plus], FreeQ[#, y]&], 
       GetCoefficient[Coefficient[expr, mon], 1, y] ];
       

MixedFindShift[a_, b_, n_, y_] := 

(* returns {h, {a, b}, const}  where h >= 0 and a(n) = const b(n+h),
   or      {}                  if no such h and const exist;
   it is assumed that gcd(a,b) = 1  *)

  Module[{aa = MakeList[a, Plus], bb = MakeList[b, Plus], e,
          max, min, amax, amin, bmax, bmin, q, qn, qp, h, exp, quot}, 

(* compare lists of y-monomials *)

    aa = Union[GetMonomial[#, y]& /@ aa];
    bb = Union[GetMonomial[#, y]& /@ bb];
    If[aa =!= bb, Return[{}]];
    
(* if there are no y's use FindShift *)

    If[aa === {1}, Return[FindShift[a, b, n]]];

(* use max and min monomials to determine h and const
   (since gcd(a,b) = 1, there are at least 
   two distinct monomials in a and b) *)

    max = Last[aa];
    min = First[aa];
    
(* get the exponent of the first base appearing in max/min *)

    qn = First[MakeList[max/min, Times]];
    {q, exp} = Replace[qn, y[q_]^exp_. -> {q, exp}];
    
(* compare leading coeffs w.r.t. n of the coeffs of max and min *)

    amax = GetCoefficient[a, max, y];
    bmax = GetCoefficient[b, max, y];
    amax = Coefficient[amax, n, Exponent[amax, n]]; 
    bmax = Coefficient[bmax, n, Exponent[bmax, n]]; 
    amin = GetCoefficient[a, min, y];
    bmin = GetCoefficient[b, min, y];
    amin = Coefficient[amin, n, Exponent[amin, n]]; 
    bmin = Coefficient[bmin, n, Exponent[bmin, n]]; 
    quot = MakeList[Cancel[(amax/bmax)/(amin/bmin)], Times];
    qp = Select[quot, !FreeQ[#, q]&];

(* there is no shift unless qp = {q^e} and h = e/exp is a nonnegative integer *)
      
    h = Together[Replace[qp, {q^e_.} -> e] / exp];
    If[!IntegerQ[h] || h < 0, Return[{}]];
    
(* compute overall constant factor *)

    const = (amin/bmin) / (min /. y[q_] -> q)^h;
    
(* check shift and const *)

    If[Together[a - (const b /. {n -> n+h, y[q_] -> q^h y[q]})] =!= 0,
         {}, 
         {h, {a, b}, const}]
]; 
   
MixedFactorOut[{alist_, blist_, a_, b_, c_}, {h_, {af_, bf_}, const_}, n_, y_] :=
  Module[{d = Min[FindExponent[alist, af], FindExponent[blist, bf]]},
    {alist /.{af, k_} -> {af, k - d}, 
     blist /.{bf, k_} -> {bf, k - d}, 
     Cancel[a const^d / af^d], 
     Cancel[b / bf^d], 
     c Product[bf /. {n -> n+s, y[q_] -> q^s y[q]}, {s,0,h-1}]^d }
  ];
    
MixedNormalForm[r_, n_, y_] :=
  Module[{fr = Cancel[r], a, b, alist, blist, shifts},
    a = Numerator[fr]; b = Denominator[fr];
    alist = Select[MyFactorList[a], !FreeL[#, {n, y}]&];
    blist = Select[MyFactorList[b], !FreeL[#, {n, y}]&];
    shifts = Select[Union @@ Outer[MixedFindShift[#1, #2, n, y]&, 
                                   First /@ alist, First /@ blist],
                    # =!= {}&];
    Drop[Fold[MixedFactorOut[#1,#2,n,y]&, {alist, blist, a, b, 1}, shifts], 2]
  ];
  

MyFactorList[x__Times] := Join @@ (MyFactorList /@ (List @@ x));

MyFactorList[x_^n_] := {{x, n}};

MyFactorList[x_] := {{x, 1}};



(* MIXED POLY *)

MixedPoly[eqn_, f_[n_], qList_, cList_:{}] :=
  Module[{y, eq, lhs, rhs, args, min, max, ord, terms, mons, maxd,
          ltcoeffs, chp, nmax, roots, coeffs, qmon, nt, sol, sub,
          newc, genh, part, cc, x, constants},

(* put everything to the left *)

    If[Head[eqn] === Equal, 
      eq = eqn[[1]] - eqn[[2]],
      eq = eqn];

(* shift if necessary *)

    args = First /@ Cases[eq, _f, Infinity] /. n -> 0;
    {min, max} = {Min[args], Max[args]};
    eq = eq /. n -> n - min;
    ord = max - min;

(* separate left-hand side from right-hand side *)

    rhs = - Select[eq, FreeQ[#, f]&];
    lhs = eq + rhs;

(* get polynomial coefficients of L *)

    coeffs = Coefficient[lhs, f[n+#]]& /@ Range[0, ord];

(* replace q^n by y[q] *)

    {coeffs, rhs} = Expand[{coeffs, rhs}] /. 
               q_?(MemberQ[qList,#]&)^(a_. n + b_.) :> q^b y[q]^a;

(* get q-monomials in L *)

    terms = MakeList[#, Plus]& /@ coeffs;
    terms = Join @@ terms;
    mons = Function[x, If[FreeQ[x, y], 1,
                           If[Head[x] =!= Times, x,
                               Select[x, Not[FreeQ[#, y]]&] ]]] /@ terms;
    mons = Union[mons];
    maxd = Last[mons];
    
(* characteristic polynomial and its roots *)
   
    ltcoeffs = If[maxd === 1,
                  coeffs,
                  Expand[Coefficient[#, maxd]& /@ coeffs]];
    nmax = Max[Exponent[#, n]& /@ ltcoeffs];
    chp = (Coefficient[#, n, nmax]& /@ ltcoeffs).(x^Range[0, ord]);
    roots = x /. Select[Solve[chp == 0, x], FreeQ[#, Roots]&];
    If[roots === x, roots = {}];
    qmon[a_ b_] := qmon[a] && qmon[b];
    qmon[a_^b_] := MemberQ[qList, a] && IntegerQ[b] && b >= 0;
    qmon[a_] := MemberQ[Append[qList, 1], a];
    roots = Select[Union[roots], qmon] /. q_?(MemberQ[qList,#]&)^a_. :> y[q]^a;
    roots = Prepend[roots, 0];
    
(* call the main routine *)
  
    nt = NextTerm[coeffs, ltcoeffs, maxd, rhs, n, roots, qList, cList, y];
    If[nt === $Failed, Return[{}]];
    {sol, sub, newc} = nt;

(* spruce up the solution *)

    sol = MakeList[sol /. sub, Plus];
    sol = sol /. y[q_] -> q^n;
    constants = Join[cList, newc];
    part = Select[sol, FreeL[#, constants]&];
    genh = Complement[sol, part];
    genh = Collect[Plus @@ genh, constants];
    genh = MakeList[genh, Plus];
    genh = Plus @@ (Together /@ genh);

(* absorb constant factors into arbitrary constants *)

    genh = genh /. {a_?(FreeQ[#, n]&) b_?(MemberQ[newc,#]&) c_. -> b c};
    sol = Factor[Plus @@ part] + genh;
    
(* rename and renumber arbitrary constants *)

    cc = Cases[{sol}, _?(MemberQ[newc,#]&), Infinity];
    Return[{sol, Select[Thread[cList -> (cList //. sub)], #[[1]] =!= #[[2]]&]} /. 
                        Thread[cc->Array[C, Length[cc]]] ] ];
    
   
   
NextTerm[coeffs_, ltcoeffs_, maxd_, rhs_, n_, roots_, qList_, cList_, y_] :=

(* finds polynomial solutions of Lf == rhs *)

  Module[{maxroot, terms, mons, maxr, bound, lt, a, q, pl, sol, x,
          range = Range[0, Length[coeffs]-1], newroots, newc, nt},
  
    maxroot = Last[roots];
    If[maxroot === 0 && rhs === 0, Return[{0,{},{}}]];

(* rhs degree *)

    terms = MakeList[Expand[rhs], Plus];
    mons = Function[x, Which[x === 0,           0,
                             FreeQ[x, y],       1,
                             Head[x] =!= Times, x,
                             True,              Select[x, Not[FreeQ[#, y]]&] ]] /@ terms;
    mons = Union[mons];
    maxr = Last[mons];
    
(* main switch *)

    If[OrderedQ[{maxr, maxd maxroot}],
        bound = maxroot;
        newroots = Drop[roots, -1],
      If[Denominator[maxr/maxd] === 1,
          bound = maxr/maxd;
          newroots = roots,
        bound = None;
        If[cList === {}, 
             sol = {},
             Off[Solve::svars];
             sol = Solve[CoefficientList[Expand[
                         If[maxr === 1, 
                            rhs,
                            Coefficient[rhs, maxr]]], n] == 0, cList] ];
        If[sol === {} || sol === {{}}, 
             Return[$Failed],
             sol = sol[[1]];
             nt = NextTerm[coeffs, ltcoeffs, maxd, 
                             Expand[Together[rhs /. sol]], n, roots, qList, cList, y];
             If[nt === $Failed, Return[$Failed]];
             Return[{nt[[1]], Join[sol /. nt[[2]], nt[[2]]], nt[[3]]}]
    ]]];
             
(* leading term: call Poly to get the (q^n)-free part *)

    If[bound =!= None,
      pl = Poly[ltcoeffs . (a[n+#](bound /. y[q_] -> q)^# & /@ range)
                == If[maxd bound === 1, rhs, Coefficient[rhs, maxd bound]], a[n], cList];
      If[pl === {}, 
          Return[$Failed], 
        {lt, sol, newc} = pl];
      lt = lt bound;

(* recursive call *)

      nt = NextTerm[coeffs, ltcoeffs, maxd, 
                    Expand[Together[(rhs - coeffs . ((lt /. {n -> n+#, y[q_] -> q^# y[q]})& 
                           /@ range)) /. sol]],
                    n, newroots, qList, Join[cList, newc], y];
      If[nt === $Failed, Return[$Failed]];
      Return[{lt + nt[[1]], Join[sol /. nt[[2]], nt[[2]]], Join[newc, nt[[3]]]}]
]];



MakeList[expr_, head_: List] :=
   If[Head[expr] === head, List @@ expr, List @ expr];


FreeL[eq_, un_] := FreeQ[eq, _?(MemberQ[un, #]&)];


Coef[_,_,_,_?Negative] = 0;

Coef[p_,i_,n_,j_] := Coefficient[p[[i]], n, j];


TriSolve[eqns_, unknowns_] := 
  Module[{sub = {}, sub1, x, eq, eqn, term, un},
     sub1 = Scan[(eq = Collect[Numerator[Together[# /. sub]], unknowns]; 
        If[eq == 0,  Null,          (* this equation is satisfied *)
                     Return[Fail],  (* lhs != 0 over Q *)
          If[FreeL[eq, unknowns],  Return[Fail],  (* lhs != 0 over Q(params) *)
              eqn = Reverse[MakeList[eq, Plus]];
                 (* find a term containing an unknown *)
              term = Scan[If[Or @@ (Function[x, !FreeQ[#, x]] /@ unknowns), 
                    Return[#]]&, eqn];
                 (* extract the unknown *)
              un = First[Select[MakeList[term, Times], 
                                MemberQ[unknowns, #]&]];
              sub1 = {un -> (term - eq)/(term/un)}; 
              sub = Join[sub /. sub1, sub1]
           ]
         ]) & , eqns]; 
    Return[If[sub1 === Fail, Fail, sub]]];


Poly[eqn_, a_[n_], cList_, verbose_: False] :=
   Module[{min, max, dd, polyCoeffs, i, eq, lhs, rhs},
   eq = Numerator[Together[ If[Head[eqn] === Equal, eqn[[1]]-eqn[[2]], eqn] ]];
   {min, max} = {Min[#], Max[#]}& @ (First /@ Cases[{eq}, a[_], Infinity]/.n->0);
   dd = max - min;                                      
   eq = Collect[Expand[eq /. n -> n - min], Table[a[n+i], {i,0,dd}]];
   rhs = - Select[eq, FreeQ[#, a]&];
   lhs = eq + rhs;                    
   polyCoeffs = Module[{i},
      Coefficient[lhs, #]& /@ Table[a[n+i], {i,0,dd}]];        
   Return[PolyK[polyCoeffs, rhs, a[n], cList, verbose]] ];
   

PolyK[polyCoeffs_, rhs_, a_[n_], cList_, verbose_: False] :=
   Module[{dd = Length[polyCoeffs] - 1, m, degreePoly, s = 0, d, degrees, deg, 
           unknowns, lhs, i, sol, poly, sub, k, cc, genh, part,
           verb = MemberQ[{True, Automatic}, verbose], C},            

   m = Max[Exponent[#, n]& /@ polyCoeffs];
   For[degreePoly = 0, degreePoly === 0, s++,
      degreePoly = Module[{i,j},
         Factor[Sum[Binomial[d,j] Sum[i^j Coef[polyCoeffs, i+1, n, m-s+j],
         {i,0,dd}], {j,0,s}]]]];
   s--;
   If[verb, Print[""]; Print["Degree polynomial: ", degreePoly/.d->n]];
   degrees = Flatten[Union[Factor /@ (d/.Solve[degreePoly==0, d]) /. d -> {}]];
   If[verb, Print["Roots found: ", degrees]];
   degrees = Append[degrees, Exponent[rhs, n] - m + s];
   degrees = Select[degrees, (IntegerQ[#] && NonNegative[#])&];
   If[verb, Print["Possible degrees: ", degrees]]; 
   deg = Max[degrees];
   If[deg === -Infinity, 
     If[rhs === 0,
        Return[{0,{},{}}],
        Return[{}] ]];
   unknowns = Array[C, deg+1, 0];
   poly = unknowns.Table[n^k, {k,0,deg}];
   lhs = polyCoeffs . Table[a[n+i], {i,0,dd}];
   sub = lhs /. a[x_] :> (poly /. n -> x);
   sub = Reverse[CoefficientList[Expand[sub - rhs], n]];
   If[verbose, Print["Triangular system: "];
               Print[""]; Print[MatrixForm[Thread[sub == 0]]]]; 
   sub = TriSolve[sub, Join[unknowns, cList]];
   If[sub === Fail, Return[{}],
      sol = Collect[poly /. sub, unknowns]];                            
   If[sol === 0, Return[{0,{},{}}]];
   sol = MakeList[sol, Plus];
   part = Select[sol, FreeQ[#, C]&];
   genh = Complement[sol, part];
   sol = Factor[Plus @@ part] + 
      Plus @@ (Factor[Numerator[Together[#]]]& /@ genh);
   cc = Cases[{sol}, C[_], Infinity];
   sub = Simplify[sub];
   Return[{sol, Select[sub, !FreeL[First[#], cList]&], cc} /. Thread[cc->Array[C, Length[cc]]] ]];



(* GET RATIO *)

(* q-factorials *)


qFac[a_, q_, n_Integer] := 
  Which[
    n  >  0,   Product[1 - a q^i, {i,0,n-1}],
    n === 0,   1,
    n  <  0,   1 / Product[1 - a/q^i, {i,-n}] ];


(** GetRatio **)

(* distribute over factors *)


GetRatio[a_Times, n_] := GetRatio[#, n]& /@ a;

GetRatio[a_^b_, n_] := GetRatio[a, n]^b /; FreeQ[b, n];


(* built-in hypergeometrics *)


GetRatio[Gamma[x_], n_] := GetRatio[Pochhammer[1, x-1], n];

GetRatio[a_!, n_] := GetRatio[Pochhammer[1, a], n];

GetRatio[(a_. n_ + b_.)!!, n_] := 
      Product[a n + b + 2 i, {i, a/2}] /; IntegerQ[a/2] && a > 0;

GetRatio[(a_. n_ + b_.)!!, n_] := 
  1 / Product[a n + b + 2 i, {i, 0, a/2 + 1, -1}] /;
                                          IntegerQ[a/2] && a < 0;

GetRatio[Binomial[a_,b_], n_] := GetRatio[Pochhammer[a-b+1,b]/b!, n];

GetRatio[Pochhammer[a_. n_ + b_., c_. n_ + d_.], n_] := 
  (If[a < 0, Product[a n + b + i, {i, a, -1}],
           1/Product[a n + b + i, {i, 0, a-1}]] *
   If[a+c > 0, Product[(a+c) n + b + d + i, {i, 0, a+c-1}],
             1/Product[(a+c) n + b + d + i, {i, a+c, -1}]]) /;
      IntegerQ[a] && IntegerQ[c] && FreeQ[b, n] && FreeQ[d, n];

GetRatio[Pochhammer[a_. n_ + b_., d_], n_] := 
  (If[a < 0, Product[a n + b + i, {i, a, -1}],
           1/Product[a n + b + i, {i, 0, a-1}]] *
   If[a > 0, Product[a n + b + d + i, {i, 0, a-1}],
           1/Product[a n + b + d + i, {i, a, -1}]]) /;
      IntegerQ[a] && FreeQ[d, n] && FreeQ[b, n];

GetRatio[Pochhammer[b_, c_. n_ + d_.], n_] := 
  (If[c > 0, Product[c n + b + d + i, {i, 0, c-1}],
           1/Product[c n + b + d + i, {i, c, -1}]]) /;
      IntegerQ[c] && FreeQ[b, n] && FreeQ[d, n];


(* products *)


GetRatio[Product[a_, {i_, b_, c_. n_ + d_.}], n_] :=
  (Product[a, {i, c n + d + 1, c n + d + c}]) /;
    IntegerQ[c] && c >= 0 && FreeQ[b, n] && RationalQ[a, i];

GetRatio[Product[a_, {i_, b_}], n_] :=
   GetRatio[Product[a, {i,1,b}], n];
   
RationalQ[p_, x_] := PolynomialQ[Numerator[p], x] &&
                     PolynomialQ[Denominator[p], x];
   
(* q-hypergeometrics *)

GetRatio[qFac[a_, q_, b_. n_ + c_.], n_] := 
  qFac[a q^(b n + c), q, b]  /;
    IntegerQ[b] && FreeQ[a, n] && FreeQ[q, n] && FreeQ[c, n];

GetRatio[qFac[A_. q_^(a_. n_ + b_.), q_^i_., c_. n_ + d_.], n_] := 
  qFac[A q^((a + i c) n + b + i d), q^i, a/i + c] /
  qFac[A q^(a n + b), q^i, a/i]  /;
    IntegerQ[a/i] && FreeQ[b, n] && FreeQ[q, n] && FreeQ[c, n] && FreeQ[d, n];

GetRatio[qFac[A_. q_^(a_. n_ + b_.), q_^i_., d_], n_] := 
  qFac[A q^(a n + b + i d), q^i, a/i] /
  qFac[A q^(a n + b), q^i, a/i]  /;
    IntegerQ[a/i] && FreeQ[b, n] && FreeQ[q, n] && FreeQ[d, n];



(* the rest *)
   
GetRatio[a_, n_] := FS[(a /. n->n+1) / a];



(* MIXED GOSPER *)

MyCancel[f_Times] :=
  Module[{f1, f2},
    f1 = Select[f, FreeL[#, {Binomial, Factorial, Factorial2,
                             Pochhammer, Gamma, qFac}]&];
    f2 = f/f1;
    Return[Cancel[f1] f2] ];
    
MyCancel[f_] := f;
                        

GosperSum[t_, k_Symbol, qList_:{}] :=  (* indefinite sum *)
  Module[{r, f},
     r = Together /@ GetRatio[t, k];
     f = GosperFunction[r, k, qList];
     If[f === $Failed, Return[$Failed],
        Return[MyCancel[f t] // PostSimplify]]];
                     

GosperSum[t_, {k_, a_, b_}, qList_:{}] :=  (* definite sum *)
  Module[{r, f},
     r = Together /@ GetRatio[t, k];
     f = GosperFunction[r, k, qList];
     If[f === $Failed, 
          Return[Sum[t, {k, a, b}]],
          Return[(MyCancel[(t /. k -> b) Factor[1 + (f /. k -> b)]] - 
                      ((f t) /. k -> a)) // PostSimplify] ]];
        

GosperFunction[r_, k_Symbol, qList_:{}] :=  (* Gosper's algoritem *)
  Module[{y, num, den, a, b, c, b1, z, x, T, qmon, f,
          w, out, a0, b0, g, aa, bb, cc, wList, rr, vars,
          a2, b2, c2},
     rr = ToY[r, k, qList, y];
     vars = Prepend[y /@ qList, k];
     num = Numerator[rr];
     den = Denominator[rr];
     If[!PolynomialQ[num, vars] || !PolynomialQ[den, vars],
        Return[$Failed]];
     {a,b,c} = MixedNormalForm[num/den, k, y];
     b1 = b /. {k -> k-1, y[q_] -> y[q]/q};

(* try with g = 1 first *)

     {a2,b2,c2} = {a,b1,c} /. {y[q_]^m_. -> q^(m k)};
     z = MixedPoly[a2 f[k+1] - b2 f[k] == c2, f[k], qList] /.
                  _C -> 0;
     If[z =!= {},
       Return[Together[(b1 z[[1]] / c) /. y[q_]^n_. -> q^(n k)]] ];

(* find g != 1 *)

     T = Select[y /@ qList, FreeQ[{a, b} /. # -> 0, 0]&];     
     qmon[a_ b_] := qmon[a] && qmon[b];
     qmon[a_^b_] := MemberQ[qList, a] && IntegerQ[b];
     qmon[a_] := MemberQ[Append[qList, 1], a];
     exponents = 
       Map[Function[yi,
         a0 = a /. yi -> 0;
         b0 = b1 /. yi -> 0;
         {aa,bb,cc} = MixedNormalForm[b0/a0, k, y];
         If[!qmon[aa/bb],
            0,
            Exponent[Denominator[aa/bb], yi[[1]] ] ]], T];
     w = Times @@ ((First /@ T) ^ exponents);
     g = Times @@ (T ^ exponents);
     {w2, g2} = {w, g} /. {y[q_]^m_. -> q^(m k)};
     If[g === 1, Return[$Failed]];
     z = MixedPoly[a2 f[k+1] - b2 w2 f[k] == c2 w2 g2, f[k], qList] /.
                  _C -> 0;
     If[z === {}, 
       Return[$Failed],
       Return[Together[(b1 z[[1]] / (g c)) /. y[q_]^n_. -> q^(n k)]]
     ]
];


Options[Zeil] = {Bases -> {}, Rhs -> True, Certificate -> False,
                 Start -> 0};

Zeil[F_, s_[n_], k_Symbol, opts___] :=
  Zeil[F, s[n], {k, -Infinity, Infinity}, opts];

Zeil[F_, s_[n_], {k_, lo_, hi_}, opts___] :=
  Module[{d, f, g, u, uu, v, vv, vp, out, alpha, pars, p, x,
          a, b, c, b1, y, z, vars, qList, rhsQ, certQ, rec, cert,
          dens, den, lclo, lchi, lolim, hilim, rhs, i, FF},
    d     = Start       /. {opts} /. Options[Zeil];
    qList = Bases       /. {opts} /. Options[Zeil];
    rhsQ  = Rhs         /. {opts} /. Options[Zeil];
    certQ = Certificate /. {opts} /. Options[Zeil];
    If[!PolynomialQ[lo, n] || !PolynomialQ[hi, n],
          Print[""]; Print["Non-polynomial limits."]; Return[]];
    lclo = Coefficient[lo, n, Exponent[lo, n]];
    lchi = Coefficient[hi, n, Exponent[hi, n]];
    lolim = Expand[If[lclo > 0, lo /. n->n+d, lo]];
    hilim = Expand[If[lchi < 0, hi /. n->n+d, hi] - 1];
    alpha[0] = 1;
    f = Together /@ GetRatio[F, n];       
    g = Together /@ GetRatio[F, k]; 
    f = ToY[ToY[f, k, qList, z], n, qList, y];
    g = ToY[ToY[g, k, qList, z], n, qList, y];
    u = Numerator[f];
    v = Denominator[f];
    vars = Join[{k, n}, y /@ qList, z /@ qList];
    If[!PolynomialQ[u, vars] || !PolynomialQ[v, vars] ||
       !PolynomialQ[Numerator[g], vars] || 
       !PolynomialQ[Denominator[g], vars],
          Print[""]; Print["Non-hypergeometric input."]; Return[]];
    out = While[True,
      Print[""];
      Print["trying d = ", d, " ..."];
      uu = FoldList[Times, 1, Table[u /. {n -> n+i, y[q_] -> q^i y[q]}, {i,0,d-1}]];
      vv = FoldList[Times, 1, Table[v /. {n -> n+i, y[q_] -> q^i y[q]}, {i,d-1,0,-1}]];
      vp = Last[vv]; 
      {a,b,c} = MixedNormalForm[g vp / 
                                (vp /. {k -> k+1, z[q_] -> q z[q]}), k, z];
      b1 = b /. {k -> k-1, z[q_] -> z[q]/q};                          
      pars = alpha /@ Range[0, d];
      p = Plus @@ (pars uu Reverse[vv]);
      {a,b1,c,p} = {a,b1,c,p} /. {y[q_] -> q^n, z[q_] -> q^k};
      sol = MixedPoly[a x[k+1] - b1 x[k] == c p, x[k], qList, Rest[pars]];
      If[sol === {}, 
       d++, 
         Print["Solution found."];
         rec = Together[Reverse[Expand[(pars /. sol[[2]]) /. _alpha -> 0]]];
         dens = Denominator /@ rec;
         den = PolynomialLCM @@ dens;
         rec = Together[den rec].(s /@ Range[n+d,n,-1]);
         If[Not[certQ || rhsQ], Return[rec]];
         cert = (den sol[[1]]b1/c/vp) /. 
          {y[q_] -> q^n, z[q_] -> q^k, _alpha -> 0};
         If[Not[rhsQ], Return[{cert, rec}]];
         FF = FS[cert F, k];
         rhs = (rec /. 
           s[n+i_.] :> Sum[Evaluate[F /. n->n+i], 
                                   {k, Expand[lo /. n->n+i], lolim - 1}] 
                     + Sum[Evaluate[F /. n->n+i], 
                                   {k, hilim + 1, Expand[hi /. n->n+i]}])
           + FS[FF /. k -> hilim + 1, n]
           - FS[FF /. k -> lolim, n];
         If[FreeQ[rhs, Sum], rhs = FS[rhs, n]];
         If[Not[certQ], Return[rec == rhs],
                        Return[{cert, rec == rhs}]];
       (*  Return[{sol[[1]]b1/c/vp /. {y[q_] -> q^n, z[q_] -> q^k}, 
                 Reverse[Expand[(pars /. sol[[2]]) /. _alpha -> 0]]}] *) ]
    ]
  ];    


Print["N.B.: Besides GosperSum and GosperFunction, this
package also contains FactorialSimplify (alias FS), and WZ."];

End[];

EndPackage[];


On[General::spell1];
  

