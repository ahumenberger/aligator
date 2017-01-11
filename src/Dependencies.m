(* ::Package:: *)

(* written by Manuel Kauers and Burkhard Zimmermann *)

(* Research Institute for Symbolic Computation (RISC) *)
(* J. Kepler University Linz, Austria *)

(* http://www.risc.uni-linz.ac.at/research/combinat/risc/software/ *)
(* email: manuel@kauers.de *)

(* ************************************************************************* *)
(*                              Dependencies.m                               *)
(*         Computing Algebraic Dependencies of C-finite Sequences            *)
(* ************************************************************************* *)

(* INSTALLATION:                                                             *)
(*                                                                           *)
(*  Put this file into some directory where Mathematica is able to           *)
(*  find it.                                                                 *)
(*                                                                           *)
(*                                                                           *)
(* BUGS:                                                                     *)
(*                                                                           *)
(*  Please report bugs concerning this package Manuel Kauers                 *)
(*  (manuel@kauers.de)                                                       *)
(*  This package was developped for Mathematica 5. We do not expect          *)
(*  that it works with earlier versions.                                     *)
(*                                                                           *)
(*                                                                           *)
(* LICENCE:                                                                  *)
(*                                                                           *)
(*  This software package is free; you can redistribute it and/or modify it  *)
(*  under the terms of the GNU General Public License as published by the    *)
(*  Free Software Foundation; either version 2 of the License, or (at your   *)
(*  option) any later version. The package is distributed in the hope that   *)
(*  it will be useful, but without any warranty; without even the implied    *)
(*  warranty of merchantability or fitness for a particular purpose. See the *)
(*  GNU General Public License for more details.                             *)

(* ------------------------------------------------------------------------- *)

Dependencies`Private`Version = "0.30 (2010-03-18)";
(* for MMA 7 from 0.28 on *)

(**
 * TODO:
 * -- Definite sums
 * BUGS:
 * -- Parameters in arguments of sequences, e.g., 
 *    Dependencies[{Fibonacci[n+m],Fibonacci[n],Fibonacci[n+1],Fibonacci[m],Fibonacci[m+1]},x,Variables->{n}] // Short
 **)

BeginPackage["RISCComb`"];

 (* declare symbols of special sequences and options *)
 Unprotect[`Pell, `PellLucas, `Lucas, `Perrin, `Where, `SUM];

 Pell::usage = "Pell[n] gives the nth Pell number.";
 PellLucas::usage = "PellLucas[n] gives the nth Pell-Lucas number.";
 Lucas::usage = "Lucas[n] gives the nth Lucas number.";
 Perrin::usage = "Perrin[n] gives the nth Perrin number.";

 Where::usage = "Option to Dependencies"; 

 dep::warn = "`1`";

 Protect[Pell, PellLucas, Lucas, Perrin, Variable, SUM]; 

 EliminationTime = 0;
 PrimitiveElementTime = 0;

EndPackage[];

BeginPackage["Dependencies`", {"RISCComb`", "Combinatorica`"}];

Unprotect[`Dependencies, Where];

Dependencies::usage = "Dependencies[{f1,f2,...}, x, " <>
  "Where -> {definitions}] computes the ideal of algebraic " <>
  "dependencies of f1,f2,...";
Express::usage = "Express[f, {f1,f2,...}, x, " <>
  "Where -> {definitions}] computes representations of f in " <>
  "terms of f1,f2,...";
CheckResult::usage = "Option to Dependencies";

{`FindRelations}; 

Begin["`Private`"];

DebugPrint[a___] := Null; (* Print[a]; *)

(** define special sequences **)

Unprotect[Pell, PellLucas, Lucas, Perrin, SUM];

SUM[expr_, {i_, a_Integer, b_Integer}] := Plus@@Table[expr, {i, a, b}];

Pell[n_Integer] := xPell[n]; PellLucas[n_Integer] := xPellLucas[n];
Lucas[n_Integer] := xLucas[n]; Perrin[n_Integer] := xPerrin[n];

Protect[Pell, PellLucas, Lucas, Perrin, SUM];

xPell[0] = 0; xPell[1] = 1;
xPell[n_Integer] /; n > 0 := (xPell[n] = 2*xPell[n-1] + xPell[n-2]);
xPell[n_Integer] /; n < 0 := (xPell[n] = -2*xPell[n+1] + xPell[n+2]);

xPellLucas[0] = 2; xPellLucas[1] = 2;
xPellLucas[n_Integer] /; n > 0 := (xPellLucas[n] = 2*xPellLucas[n-1] + xPellLucas[n-2]);
xPellLucas[n_Integer] /; n < 0 := (xPellLucas[n] = -2*xPellLucas[n+1] + xPellLucas[n+2]);

xLucas[0] = 2; xLucas[1] = 1;
xLucas[n_Integer] /; n > 0 := (xLucas[n] = xLucas[n-1] + xLucas[n-2]);
xLucas[n_Integer] /; n < 0 := (xLucas[n] = -xLucas[n+1] + xLucas[n+2]);

xPerrin[0] = 3; xPerrin[1] = 0; xPerrin[2] = 2; xPerrin[3] = 3; xPerrin[4] = 2; xPerrin[5] = 5;
xPerrin[n_Integer] /; n < 0 := (xPerrin[n] = -xPerrin[n+1] + xPerrin[n+3]);
xPerrin[n_Integer] /; n > 0 && EvenQ[n] := Module[{m}, m=n/2; xPerrin[n] = 
  (5*xPerrin[m]^2 - 12*xPerrin[m]*xPerrin[1 + m] - 2*xPerrin[1 + m]^2 + 
   8*xPerrin[m]*xPerrin[2 + m] + 18*xPerrin[1 + m]*xPerrin[2 + m] - 6*xPerrin[2 + m]^2)/23];
xPerrin[n_Integer] /; n > 0 && OddQ[n] := Module[{m}, m=(n-1)/2; xPerrin[n] = 
  (4*xPerrin[m]^2 + 18*xPerrin[m]*xPerrin[1 + m] + 3*xPerrin[1 + m]^2 - 
   12*xPerrin[m]*xPerrin[2 + m] - 4*xPerrin[1 + m]*xPerrin[2 + m] + 9*xPerrin[2 + m]^2)/23];

(******************************************************)
(* Part 0: Expression manipulation tools              *)
(******************************************************)

(**
 * Given a system of linear recurrences, extract the dependent variable in which it is given.
 * If the dependent variable cannot be determined (e.g. if the system is empty), then a new 
 * symbol will be returned. If more than one dependent variable is found, an exception is thrown.
 *
 * It is assumed that the system is given in the form as required by SolveRecurrence; see
 * the spec of that function for details. 
 **)
ExtractDependentVariable[system_List] :=
  Module[ {n, i},

  If[ system === {}, Return[n] ];

  n = Union[Cases[system, _[n_ + Optional[_Integer]] == _ -> n, Infinity]];
  n = DeleteCases[n, _Integer];

  Which[ 
    Length[n] === 1, Return[First[n]],
    Length[n] < 1, Return[Unique[]],
    Length[n] > 1, Throw["Definitions must be given using one and the same variable symbol in each equation."]
  ];
];

(**
 * Brings a system of linear recurrences into a standardized form.
 * This form has the following properties
 * 1. recurrences and initial values are separated. 
 * 2. all recurrence equations are of the form f[n]==.. (i.e. not f[n+i]==.. with i>0)
 * 3. Recurrence A is listed before recurrence B if the inhomog. part of A involves the
 *    sequence defined by B.
 * 4. Recurrences for builtin-functions are made explicit.
 * If a system cannot be brought to this form, an exception is thrown.
 * 
 * Return value has the form {listofrecs, listofinitvalspecs}.
 **)
NormalizeSystem[sys_] := 
  Module[ {recs, inits, args, i, n, eq, fib, luc, pell, pellluc, perrin, chebu, chebt, g, 
           iFreeOfJ, jFreeOfI},

    recs = {}; inits = {};
    n = ExtractDependentVariable[sys];

    (* split *)
    Do[
      eq = sys[[i]];
      Which[ 
        FreeQ[eq, n] && MatchQ[eq, _[_Integer]==_],
          AppendTo[inits, eq],
        MatchQ[eq, _[n + Optional[_Integer]]==_],
          AppendTo[recs, eq],
        True,
          Throw["Illegal equation encountered: " <> ToString[eq]];
      ];
    , {i, 1, Length[sys]}];

    (* add builtin stuff *)
    {recs, inits} = {recs, inits} /. {Fibonacci -> fib, Lucas -> luc, Pell -> pell, 
                                      PellLucas -> pellluc, Perrin -> perrin}
                                  /. ChebyshevT[n_, x_] -> chebt[x][n]
                                  /. ChebyshevU[n_, x_] -> chebu[x][n];

    args = Cases[recs, chebu[x_] -> x, Infinity, Heads -> True];
    recs = Join[recs, (chebu[#][n+2]==-chebu[#][n]+2# chebu[#][n+1])& /@ args];
    inits = Join[inits, Flatten[{chebu[#][0]==1, chebu[#][1]==2#}& /@ args]];

    args = Cases[recs, chebt[x_] -> x, Infinity, Heads -> True];
    recs = Join[recs, (chebt[#][n+2]==-chebt[#][n]+2# chebt[#][n+1])& /@ args];
    inits = Join[inits, Flatten[{chebt[#][0]==1, chebt[#][1]==#}& /@ args]];

    recs = Join[recs, {fib[n+2]==fib[n]+fib[n+1],luc[n+2]==luc[n]+luc[n+1],
                       pell[n+2]==pell[n]+2pell[n+1],pellluc[n+2]==pellluc[n]+2pellluc[n+1],
                       perrin[n+3]==perrin[n]+perrin[n+1]}];
    inits = Join[inits, {fib[0]==0,fib[1]==1,luc[0]==2,luc[1]==1,pell[0]==0,pell[1]==1,
                         pellluc[0]==2,pellluc[1]==2,perrin[0]==3,perrin[1]==0,perrin[2]==2}];

    (* align shifts *)
    recs = recs /. f_[n+i_]==rhs_ :> (f[n+i]==rhs/.n->n-i);

    (* topological sort *)
    g = EmptyGraph[Length[recs], Type -> Directed];
    Do[
      iFreeOfJ = FreeQ[recs[[i]], recs[[j, 1, 0]]]; (* rec i does not depend on seq j *)
      jFreeOfI = FreeQ[recs[[j]], recs[[i, 1, 0]]]; (* rec j does not depend on seq i *)
      Which[
        !jFreeOfI && iFreeOfJ, g = AddEdge[g, {j, i}], (* i-th must be before j-th *)
        !iFreeOfJ && jFreeOfI, g = AddEdge[g, {i, j}], (* j-th must be before i-th *)
        jFreeOfI && iFreeOfJ, Null, (* order irrelevant *)
        True, Throw["defining equations illegally coupled"] (* illegal coupling *)
      ]
    , {i, 1, Length[recs]}, {j, 1, i - 1}];
    g = TopologicalSort[g];
    If[ Head[g] =!= List, Throw["defining equations illegally coupled"] ];
    recs = Table[recs[[g[[i]]]], {i, 1, Length[recs]}];

    (* done *)
    Return[{recs, inits}];
  ];

(**
 * From a normalized recurrence system, create a list of rules that allows the evaluation of 
 * the sequences.
 * For each recurrence f[n]==..., two rules are created: (f[n]/;n>a)->.. and (f[n]/;n<b)->..
 * where a and b are the smallest resp. larges point for which an initial value is specified. 
 * If b - a exceeds the order of the recurrence, and exception is thrown.
 * Also rules corresponding to the initial value specs are included.
 * If, for some sequence, no initial values are specified at all, then f[0],...,f[order-1] are
 * taken as symbolic initial values.
 *
 * Example: f[17] //. System2Rules[sys] should either generate an exception or yield the 
 * value of f at n=17, provided that sys defines f.
 **)
System2Rules[recs_, inits_] :=
  Module[ {rules, n, a, b, c, d, r, f, eq, i, j},

  n = ExtractDependentVariable[recs];

  rules = inits /. a_ == b_ -> (a -> b);

  Do[
    eq = recs[[i]]; f = eq[[1,0]];

    a = Min[Cases[inits, f[j_Integer]==_ -> j]];
    b = Max[Cases[inits, f[j_Integer]==_ -> j]];
    r = RecurrenceOrder[eq, n, f];

    If[ a == Infinity || b == -Infinity, {a, b} = {0, r - 1} ];
    If[ b - a < r - 1, b = a + r - 1 ]; (* padd with symbolic initvals *)

    AppendTo[rules, (c[f[d[n, Blank[Integer]]], n > b] /. {c -> Condition, d -> Pattern}) -> Last[eq]];

    eq = (f[n] /. First[Solve[eq /. n -> n + r, f[n]]]);
    AppendTo[rules, (c[f[d[n, Blank[Integer]]], n < a] /. {c -> Condition, d -> Pattern}) -> eq];

  , {i, 1, Length[recs]}];  

  Return[rules];  
];

RecurrenceOrder[rec_, n_, f_] := 
  Max[Cases[rec, f[n+j_.] -> j, Infinity]] - Min[Cases[rec, f[n+j_.] -> j, Infinity]];

ClearAll[ExpectedOrder];
ExpectedOrder[expr_, recs_, n_] /; FreeQ[expr, n] := If[ Expand[expr]===0, 0, 1];
ExpectedOrder[expr_, recs_, n_] /; PolynomialQ[expr, n] := 1 + Exponent[expr, n];
ExpectedOrder[SUM[expr_, {k_, _Integer, _}], recs_, n_] /; FreeQ[expr, n] := 
  1 + ExpectedOrder[expr /. k -> n, recs, n];
ExpectedOrder[a_*b__, recs_, n_] := Max[1, ExpectedOrder[a, recs, n]] * ExpectedOrder[Times[b], recs, n];
ExpectedOrder[a_+b__, recs_, n_] := ExpectedOrder[a, recs, n] + ExpectedOrder[Plus[b], recs, n];
ExpectedOrder[a_^b_, recs_, n_] /; FreeQ[a, n] = 1;
ExpectedOrder[a_^k_Integer, recs_, n_] := 
  If[ !FreeQ[a, n] && k < 0, 
    Throw["Unable to verify c-finitenes of " <> ToString[a^k]],
    Binomial[ExpectedOrder[a, recs, n]+k-1,k]
  ];
ExpectedOrder[f_[a_], recs_, n_] /; Exponent[a, n] == 1 :=
  Module[ {rec},
    rec = Cases[recs, f[_]==_];
    If[ Length[rec] =!= 1, Throw["no recurrence for " <> ToString[f] <> " found."] ];
    Return[RecurrenceOrder[First[rec], n, f] + 
           ExpectedOrder[rec[[1, 2]] /. f[_] -> 0, DeleteCases[recs, rec], n]];
  ];
ExpectedOrder[a_, __] := 
  Throw["illegal expression encountered in inhomogenoues part of recurrence: " <> ToString[a]];

(* Given a normalizeable system, construct an individual recurrences
   for each sequence, resp. for the given sequences *)
Off[Solve::svars];
UnCouple[sys_] := UnCouple[sys, Union[Cases[sys, f_[_]==_ -> f, Infinity]]];
UnCouple[sys_, funs_] :=
  Module[
    {recs, inits, newRecs, newInits, n, eval, eq, r, c, f, i, j,
     a, rec0, sys0, sol0, values, k, rightHandSideDependency, method},

    n = ExtractDependentVariable[sys];
    {recs, inits} = NormalizeSystem[sys];
    eval = System2Rules[recs, inits];

    newRecs = {}; 

    Do[

      eq = recs[[i]]; f = eq[[1, 0]]; 

      If[ !MemberQ[funs, f], Continue[] ];

      a = Max[Min[Cases[rec, f[j_] == _          -> j]],
              Min[Cases[eval, SUM[_, {_, j_, _}] -> j, Infinity]]];

      If[ a == Infinity, a = 0 ];
      rec0[k_] = c[0];

      rightHandSideDependency = Last[eq] /. f[_] -> 0;
      (* The following If is basically a short cut for cases where the
         equation is already uncoupled. *)
      (* Last[eq] is the right hand side of eq. *)
      If[rightHandSideDependency === 0,
        AppendTo[newRecs, Prepend[Cases[sys, f[_Integer]==_], eq]]; 
        Continue[]
      ];

      (* upper bound *)
      r = RecurrenceOrder[eq, n, f] + 
          ExpectedOrder[Collect[rightHandSideDependency, _^n],
                        Drop[recs, i],
                        n];
      values = Table[
          FixedPoint[# /. eval /. b_*c_Plus :> Plus@@(b*List@@c)&, f[j]],
          {j, a, a + 3*r}
      ];
      r = r + 1;

      (* The following While body will be executed at least once, but
         it might need (at most) two iterations in order to solve the
         system. *)
      While[ !FreeQ[rec0[n], c],

        r = r - Length[Union[Cases[{rec0[n]}, c[_], Infinity]]];
        rec0[k_] = f[k + r] - Sum[c[j]f[k + j], {j, 0, r - 1}];
        sys0 = Table[rec0[k]==0, {k, a, a + 2*r}] /. f[j_] :> values[[j-a+1]];

        (* For certain problems like
           Dependencies[{f[n], g[n]}, x, Variables -> {n},
             Where -> {f[n+1] == f[n] + g[n]^2, g[n+1] == g[n] + Fibonacci[n]}]
           the running time was extremely longer in MMA7 than in MMA6.
           The reason is that RowReduce in MMA7 uses another heuristics.
           So we switch back to the MMA6 semantics.
           See http://groups.google.com/group/comp.soft-sys.math.mathematica/browse_thread/thread/a39d99bc1470bb3c
           Since we do not want to rely on the Internal` context,
           we just do it the simple way of locally changing the options of
           RowReduce. *)
        method = Options[RowReduce, Method];
        SetOptions[RowReduce, Method -> OneStepRowReduction];
        sol0 = Solve[sys0, Array[c, r, 0]];
        SetOptions[RowReduce,method];

        rec0[k_] = f[k + r] == Sum[c[j]f[k + j], {j, 0, r - 1}] /. First[sol0];
      ];

      sol0 = First[sol0];
      AppendTo[newRecs,
        Prepend[Table[f[a + j - 1] == values[[j]], {j, 1, r}], rec0[n]]];

    , {i, 1, Length[recs]}];

    Return[DeleteCases[#, True]& /@ newRecs];
  ];

(**
 * Replace non-polynomial subexpressions in seqs by f[1][n], f[2][n], f[3][n], ...
 * The last f[_][n] is always n.
 * and add the corresponding definitions to defs. Return {newSeqs, newDefs}.
 **)
ExtractExpressions[seqs_, defs_, f_] :=
  Module[ {n, newDefs, rules, ex, a, b, c, d, i},

    n = ExtractDependentVariable[defs];

    ex = Union[Cases[seqs, SUM[a_, {b_, c_, d_}] -> SUM[a, {b, c, n}], Infinity],
               Cases[seqs, a_[b_] /; !NumberQ[b] -> a[n], Infinity],
               Cases[seqs, a_^(b_.*c_+d_.) /; !NumberQ[c] -> a^(b n), Infinity], (* catches Sqrt[2]^n *)
               Cases[seqs, a_^b_ /; !NumberQ[b] -> a^n, Infinity], (* doesn't catch Sqrt[2]^n *)
               Cases[seqs, ChebyshevU[a_, b_] /; !NumberQ[a] -> ChebyshevU[n, b], Infinity],
               Cases[seqs, ChebyshevT[a_, b_] /; !NumberQ[a] -> ChebyshevT[n, b], Infinity]];

    newDefs = Table[f[i][n] == ex[[i]], {i, 1, Length[ex]}];
    rules = ToRules[And@@(Reverse/@newDefs)]
               /. (a_ -> b_) :> ((a /. n -> c[n, Blank[]]) -> b)
               /. c -> Pattern;

    AppendTo[newDefs, f[Length[newDefs] + 1][n] == n];

    Return[{seqs /. rules, Join[defs, newDefs]}];
  ];

(******************************************************)
(* Part I: Recurrence Solving Tools                   *)
(******************************************************)

(**
 * Input: Something of the form {f[n+2]==f[n]+f[n+1],f[0]==0,f[1]==1}
 * Output: Something of the form {f, {a, b}, {{c, d, ..}, {e, ..}}}
 * representing the closed form f[n] == (c + d*n + ..)*a^n + (e + ..)*b^n.
 **)
SolveRecurrence[rec_] := 
  Module[ {p, eq, n, f, a, b, c, i, j, lambda, x, eval, ansatz, sys, sol},

    n = ExtractDependentVariable[rec];
    eq = Select[rec, !FreeQ[#, n]&];
    eval = System2Rules@@NormalizeSystem[rec];

    If[ Length[eq] =!= 1, Throw["Illegal sequence definition: " <> ToString[rec]] ];
    eq = First[eq]; f = eq[[1, 0]];
    
    p = eq /. a_ == b_ -> a - b /. f[n + i_.] -> lambda^i // FactorList;
    p = Rest[p] /. {a_, b_Integer} :> 
                   Table[{Hold[Root[x[a] /. lambda -> # /. x -> Function, i]] // ReleaseHold, b}, 
                         {i, 1, Exponent[a, lambda]}];
    p = Join@@p;

    ansatz[n_] = Sum[c[i, j]n^i p[[j, 1]]^n, {j, 1, Length[p]}, {i, 0, p[[j, 2]] - 1}];
    sys = FixedPoint[Expand[#/.eval]&, Table[f[n] == ansatz[n], {n, 0, RecurrenceOrder[eq, n, f]}]];
    sol = Solve[sys, Union[Cases[sys, c[__], Infinity]]];

    Return[ {f, First /@ p, Table[c[i, j], {j, 1, Length[p]}, {i, 0, p[[j, 2]] - 1}] /. First[sol]} ];
  ];

(**
 * This function converts a given multivariate polynomial 
 * from the standard basis into the falling factorial basis.
 *
 * The result is given as a list of pairs {c, {e1,e2,...}}
 * such that the sum of all c*ff[v1,e1]*ff[v2,e2]*... is equal
 * to poly.
 **)
FallingFactorialRepresentation[poly_, vars_] :=
   Module[ {p, i, j, d, t, v},

   p = Expand[poly];

   Do[
     p = p /. vars[[i]]^Optional[d_Integer] :> Sum[StirlingS2[d, j]*v[i]^j, {j, 0, d}];
   , {i, 1, Length[vars]}];

   p = Expand[p];

   If[ Head[p] === Plus, p = List@@p, p = {p} ];

   Do[
     t = p[[i]]; (* current monomial *)
     p[[i]] = {t /. v[_] -> 1, Table[Exponent[t, v[j]], {j, 1, Length[vars]}]};
   , {i, 1, Length[p]}];

   Return[p];
];

FallingFactorial[n_, d_Integer] := Pochhammer[n - d + 1, d];

(**
 * converts a descriptor as delivered by the solver into a closed form expression.
 * example: {f, {a, b}, {{1,2},{3,4}}} ==> (1+2*n)*a^n + (3+4*n)*b^n
 **)
Descriptor2Expression[{f_, phi_List, coeffs_List}, n_] :=   
  Module[ {i, j},

  Sum[phi[[i]]^n * Sum[coeffs[[i,j]] * If[j==1, 1, n^(j-1)], {j, 1, Length[coeffs[[i]]]}],
     {i, 1, Length[phi]}]  
];

(*******************************************************)
(* Part II: lattice computation routines               *)
(*******************************************************)

(* FindRelations and ZModuleIntersect are defined in the second part of this file *)

(**
 * Given a basis of a lattice L and an integer d,
 * compute a basis of the lattice L' containing all
 * points v such that v*d belongs to L.
 **)
LatticeDivide[lattice_?MatrixQ, d_Integer] :=
  Module[ {n},

  n = Length[First[lattice]];
  ZModuleIntersect[lattice, d*IdentityMatrix[n]] / d

];
LatticeDivide[{}, _] = {};

(**
 * Converts a lattice to an ideal.
 * The variable corresponding to the i-th component is x[i].
 **)
Lattice2Ideal[{}, _] = {};

Lattice2Ideal[b_, x_] := Module[ {e, y},

  base = Table[ 
    Product[
      e = b[[i,j]]; If[e > 0, x, y][j]^Abs[e]
      , {j, 1, Length[b[[i]]]}] - 1,
    {i, 1, Length[b]}
  ];
  base = Join[base, Table[x[j]*y[j] - 1, {j, 1, Length[First[b]]}]];
  base = EliminationIdeal[base, Table[y[i], {i, 1, Length[First[b]]}], Table[x[i], {i, 1, Length[First[b]]}]];

  Return[base];
];

(*******************************************************)
(* Part III: User interface                            *)
(*******************************************************)

(**
 * Given multivariate sequences f and f1,f2,... and a variable x (opt),
 * compute a representation of f in terms of f1, f2, ... if possible.
 **)
Options[Express] := {Where -> {}, Variables -> Automatic};
Express[f_, terms_List, opts:((_Rule|_RuleDelayed)...)] :=
  Module[ {x, i},

  Express[f, terms, x, opts] /. x[i_] :> terms[[i]]
];
Express[f_, terms_List, x_, opts:((_Rule|_RuleDelayed)...)] :=
  Module[ {id, i},

  id = Dependencies[Prepend[terms, f], x, opts, Cleanup -> False] /. x[i_] -> x[i-1];
  id = EliminationIdeal[id, {x[0]}, Table[x[i], {i, 1, Length[terms]}], Keep -> True, Cleanup -> False];
  id = Select[id, !FreeQ[#, x[0]]&];
  id = Flatten[(x[0] /. Solve[#==0, x[0]])& /@ id];

  Return[id];  
];

(**
 * Given multivariate sequences f1,f2,..., and a symbol x,
 * compute an ideal basis of kernel (Phi), where 
 * Phi maps x[1] to f1, x[2] to f2, etc.
 **)
Options[Dependencies] = {Where -> {}, Variables :> Automatic, CheckResult -> True};
Dependencies[seqs_List, opts:((_Rule|_RuleDelayed)...)] :=
   Module[ {x, i},

   Dependencies[seqs, x, opts] /. x[i_] :> seqs[[i]]
];
Dependencies[seqs_List, x_, opts:((_Rule|_RuleDelayed)...)] := 
   Module[ {myseqs, C, V, id, p, exp, a, b, c, d, e, f, i, j, n, L, defs, 
            used, vars, basis, u, check, eval},

   If[ Length[Complement[First /@ {opts}, {Where, Variables, Cleanup, CheckResult}]] > 0,
     Throw["Illegal option(s) encountered."];
   ];

   (* I. Preprocessing *)
   check = CheckResult /. {opts} /. Options[Dependencies];
   defs = Where /. {opts} /. Options[Dependencies];
   {myseqs, defs} = ExtractExpressions[seqs, defs, f];
   eval = System2Rules@@NormalizeSystem[defs];
   defs = SolveRecurrence /@ UnCouple[defs, Union[Cases[defs, f[a_][_]==_ -> f[a]]]];

   V = Variables /. {opts} /. Options[Dependencies];
   If[ Head[V] =!= List,
     V = Union[Flatten[Cases[myseqs, f[_][i_] :> Variables[i], Infinity]]];
     Message[dep::warn, "No variables specified. Choosing " <> ToString[V]];
   ];

   myseqs = myseqs /. Thread[V -> Thread[f[Length[defs]][V]]] /. f[i_][j_] :> f[i][j /. f[_][a_] -> a];

   (* 2. extract the exponentials that actually occur *)
   phi = Union@@Table[defs[[i, 2]], {i, 1, Length[defs]}];

   (* 3. extract the parameters appearing in the recurrences *)
   vars = Union[
            Cases[Flatten[(#[[2]]& /@ defs)], 
            i_ /; !MemberQ[{Root,AlgebraicNumber,Plus,Times,Power,Integer,Rational,Function,Slot},Head[i]],
            Infinity]
          ];
   vars = DeleteCases[vars, _?NumericQ];

   (* 4. replace the corresponding entries in defs by pointers to phi *)
   DebugPrint["I.4"];
   
   Do[
      defs[[i, 2, j]] = Position[phi, defs[[i, 2, j]]][[1,1]];
   , {i, 1, Length[defs]}, {j, 1, Length[defs[[i, 2]]]}];

   (* 5. compute the first lattice now and the others on demand *)
   DebugPrint["I.5"];

   L[0] = {};
   L[1] = FindRelations[phi, vars];
   L[d_Integer] := (L[d] = LatticeDivide[L[1], d!]);   

   (* II. Build up the ideal basis *)
   DebugPrint["II."];

   basis = {};

   (* we use c[i][x,y,z,...] as variable for 
      phi[[i]] ^ (ff[V[[1]], x] * ff[V[[2]], y] * ff[V[[3]], z] * ...)

      and c[i] as variable for C[[i]]
      and the elements of V for themselves
      and c[-i] for the denominator of myseqs[[i]] (if nontrivial)
    *)

   (* 1. collect the closed forms of the involved c-finite functions *)
   DebugPrint["II.1"];

   C = Union[Cases[myseqs, f[a_][_], Infinity]];

   Do[ 

      p = C[[i, 1]]; (* argument polynomial *)

      ffp = FallingFactorialRepresentation[p, V]; 

      (* get the position of the closed form *)
      d = First[Cases[defs, {C[[i, 0]], _, _}]];
      AppendTo[basis, -c[i] + def2poly[c, d, p, ffp]];

   , {i, 1, Length[C]}];

   basis = basis /. c[i_][0..] :> phi[[i]]; (* a^(n^0)= a^1 = a *)   

   (* 2. add the algebraic dependencies of the exponentials *)
   DebugPrint["II.2"];

   (* which exponent vectors do actually occur in the argument polynomials? *)
   e = Union[Flatten[Cases[basis, c[_][i___] -> a[i], Infinity]]] /. a -> List;

   Do[

     b = Union@@Table[L[e[[i,j]]], {j, 1, Length[e[[i]]]}]; 
     basis = Join[basis, Lattice2Ideal[b, u] /. u[j_] -> c[j]@@e[[i]]];

   , {i, 1, Length[e]}]; 

   (* 3. add the generators of the given expression *)
   DebugPrint["II.3"];

   basis = Union[basis, 
     Table[Numerator[Together[x[i] - (myseqs[[i]] /. Table[C[[j]] -> c[j], {j, 1, Length[C]}])]],
        {i, 1, Length[myseqs]}]
   ];

   basis = Numerator /@ Together /@ basis; (* clear denominators *)

   (* 4. add Rabinovitz variables for nontrivial denominators in myseqs *)
   DebugPrint["II.4"];

   Do[
     d = Denominator[Together[myseqs[[i]]]];
     If[ !NumberQ[d], AppendTo[basis, c[-i]*d - 1 /. Table[C[[j]] -> c[j], {j, 1, Length[C]}]] ];
   , {i, 1, Length[myseqs]}];   

   (* 5. Eliminate all dummy variables *)
   DebugPrint["II.5"];

   basis = EliminationIdeal[basis, 
         Union[Flatten[Cases[basis, c[_][___], Infinity]],
               Flatten[Cases[basis, c[_], Infinity]],
               V],
         Table[x[i], {i, 1, Length[myseqs]}],
         opts
      ];

   basis = RootReduce /@ basis;

   (* 6. check result *)
   DebugPrint["II.6"];
   If[ CheckResult /. {opts} /. Options[Dependencies],

     myseqs = basis /. x[i_] :> myseqs[[i]] /. Thread[V -> 2+Range[Length[V]]];
     myseqs = FixedPoint[# /. eval /. a_*b_Plus :> Plus@@(a*List@@b)&, myseqs];

     If[ !MatchQ[Chop[N[Together[myseqs]]], {0...}],
       Throw["Consistency check reports failure: Algorithm delivered an incorrect relation. " <>
             "Please report this bug (including the package version and the input that lead " <>
             "to this message) to Manuel Kauers (manuel@kauers.de). Thank you."]];
   ];

   Return[basis];
];

polypower[c_, fpp_] := Module[ {i}, 

  Product[ c@@fpp[[i, 2]]^fpp[[i, 1]], {i, 1, Length[fpp]} ]
];

def2poly[c_, d_, p_, fpp_] := Module[ {i,j,k},

  Sum[
    Sum[ d[[3, i, j]]*p^(j-1), {j, 1, Length[d[[3, i]]]}]
      * polypower[c[d[[2, i]]], fpp], 
  {i, 1, Length[d[[2]]]}]
];

(**
 * Compute an Elimination ideal.
 *
 * {p1,p2,...}... a list of multivariate polynomials in x1,x2,...,y1,y2,...
 * {x1,x2,...}... variables to be eliminated
 * {y1,y2,...}... variables to be kept.
 **)
Options[EliminationIdeal] = {`Keep -> False, `Cleanup -> True};
EliminationIdeal[basis_List, {}, stay_List, opts___] := basis;
EliminationIdeal[basis_List, away_List, stay_List, opts___] :=
   Module[ {M, G, mystay, alg, algNum, algFun, t, i, a, minpoly, keep, cleanup, time},

   {keep, cleanup} = {Keep, Cleanup} /. {opts} /. Options[EliminationIdeal];

   (* use a fast elimination ordering instead of Lex *)

   (* matrix orders do not work over function fields *)
   mystay = Join[stay, Complement[Variables[basis], away, stay]];

   (* we make algebraic numbers explicit in hope for better performance *)
   alg = Union[Cases[basis, (AlgebraicNumber[_,_]|Root[_,__]|Complex[_,_]|Power[_,_Rational]|Sqrt[_]), Infinity]];

   algNum = Select[alg, NumericQ];
   algFun = Complement[alg, algNum];

   {time, algNum} = Timing[Apply[Rule, Transpose[{algNum, ToNumberField[algNum]}], {1}]];
   PrimitiveElementTime += time;
   G = basis /. algNum /. AlgebraicNumber[_, a_List] :> Sum[a[[i]]*t^(i-1),{i,1,Length[a]}];

   If[ Length[algNum] > 0, 
     AppendTo[G, MinimalPolynomial[algNum[[1,2,1]], t]];
     AppendTo[mystay, t];
   ];

   For[ i = 1, i <= Length[algFun], i++,
     a = algFun[[i]];
     G = G /. a -> t[i];
     AppendTo[G, 
        Which[ (* defining equation for t[i] *)
          Head[a] === Power, 
            t[i]^Denominator[a[[2]]] - a[[1]]^Numerator[a[[2]]],
          Head[a] === Root,
            a[[1]][t[i]]
        ]];
     AppendTo[mystay, t[i]];
   ];

   EliminationTime += First[AbsoluteTiming[
   Which[
     NameQ["Singular`SingularVersion"],

      (* use Singular if it is available *)
      If[ keep, 
        G = Singular`SingularStd[G, away, mystay, MonomialOrder -> "dp"],
        G = Singular`SingularEliminate[G, away, mystay]
      ];

    , NameQ["Gb`GbVersion"],

      (* use Faugere if it is available *)
      G = Gb`GBasis[G, away, mystay, 
             MonomialOrder -> DegreeReverseLexicographic,
             Eliminate -> !keep];
    , True,

      (* otherwise, try Mathematica's builtin *)
      If[ keep,
        G = GroebnerBasis[G, Join[away, mystay]],
        G = GroebnerBasis[G, mystay, away]
      ];
      (*
      M = -IdentityMatrix[Length[away] + Length[mystay]];

      M[[1]] = Join[Table[1, {Length[away]}], Table[0, {Length[mystay]}]];
      M[[2]] = 1 - M[[1]];

      If[ Length[away] > 1, M[[2,2]] = -1 ];

      G = GroebnerBasis[G, Join[away, mystay], MonomialOrder -> M];
      G = Select[G, (Intersection[Variables[#], away] == {}) &];
      *)
   ]]];

   (* undo algebraic numbers *)
   G = G /. t[i_Integer] :> algFun[[i]];

   If[ Length[algNum] > 0, 
      G = G /. t -> AlgebraicNumber[algNum[[1,2,1]],{0,1}] // RootReduce;
   ]; 

   If[ cleanup,
     G = GroebnerBasis[G, stay, MonomialOrder -> DegreeReverseLexicographic]; (* cleanup *)
   ,
     G = DeleteCases[G, 0];
   ];

   (* discard the content. a nontrivial content might be present due to the encoding
      of algebraic numbers/functions as ring variables. *)
   For[ i = 1, i <= Length[G], i++,

     a = PolynomialGCD@@Complement[Flatten[CoefficientList[G[[i]], Join[away, stay]]], {0}];
     G[[i]] = Cancel[G[[i]]/a];
   ];
   G = Union[G]; (* remove doublets *)

   Return[G];
];

Protect[Dependencies];

End[];

(* ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## *)
(* ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## *)
(* ## Code below provides implementation of Ge's algorithm ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## *)
(* ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## *)
(* ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## ## *)

(* This code should be kept independent from the rest so that it can be pasted into an independent 
   package, if desired *)

(* needs: NumberTheory`AlgebraicNumberFields`, NumberTheory`ContinuedFractions` *)

Unprotect[FindRelations];

FindRelations::usage = 
  StringJoin["FindRelations[{a[1],a[2],...}] computes a basis of the lattice ",
             "of all integer vectors {v[1],v[2]...} such that a[1]^v[1]*a[2]^v[2]*...=1. ",
             "The numbers a[i] have to be algebraic over the rationals, given as Root or ",
             "Algebraic objects. If they are not given as Algebraic objects of the same ",
             "field, then the splitting field has to be computed and this computation may ",
             "dominate all other steps in runtime."];

Begin["`Private`"];

(**
 * ZModuleIntersect[base1, base2];
 *
 * Given two Z-modules, compute a basis for their intersection. 
 **)
ZModuleIntersect[base1_List, base2_List] := 
  Module[ {d, b, a, sol},

  (* like in linear algebra, but with ZNullSpace instead of NullSpace *)
  If[ base1 == {} || base2 == {}, Return[ {} ]];

  sol = ZNullSpace[Join[base1, base2]];

  If[sol == {}, Return[ {} ]];

  LatticeReduce[Transpose[Transpose[base1] . Transpose[Take[sol, Length[sol], Length[base1]]]]]
];

(**
 * Computes the integer kernel of an integer matrix.
 **)
ZNullSpace[mat_] := 
  Module[ {U, A},    

  {U, A} = HermiteDecomposition[mat]; 

  (* kernel is generated by the rows of U that correspond to zero rows in A *)
  (* cf. H. Cohen, prop. 2.4.9. *)

  Extract[U, Position[A, {0..}]] 
];

(**
 * Given a list of algebraic numbers, a[1], ..., a[k], this method returns a number B
 * such that the lattice of all vectors {v[1],...,v[k]} with 
 *
 *  a[1]^v[1]*...*a[k]^v[k] == 1
 *
 * has a basis whose basis vectors have norm at most B.
 **)
MasserBound[roots_] := 
  Module[ {k, D, h, h0, p, i, eta, x},

  (* k = number of roots *)
  k = Length[roots]; (* number of roots *)

  (* D = degree of the field extension *)
  p = Union[Cases[roots, AlgebraicNumber[i_, __] -> i]];

  Which[ 
    Length[p] == 0 && FreeQ[roots, Sqrt] && FreeQ[roots, Root],
      D = 1,
    Length[p] == 1, 
      D = Exponent[MinimalPolynomial[First[p], x], x],
    True,           
      Throw["Input should be specified as Algebraic objects of one single algebraic extension of Q"]
  ];

  (* h = maximum height of the a[i]. The height of an algebraic number is the sum of the degree and 
     the binary length of all coefficients in the defining equation over Q *)
  h = 0;
  For[i = 1, i <= Length[roots], i++,

     p = MinimalPolynomial[ roots[[i]], x];
     h0 = Ceiling[Exponent[p, x] + Plus@@Log[2, Abs[DeleteCases[CoefficientList[p, x], 0, 1]]]];

     If[ h0 > h, h = h0 ];
  ];

  (* Masser's bound *)
  Ceiling[ D^2*(4*h*k*D*(Log[2+D]/Log[Log[2+D]])^3)^(k-1) + 1 ]

];

(**
 * Decision procedure for zero equivalence of algebraic functions. 
 **)
AlgebraicFunctionZeroQ[alg_, vars_] := 
  Module[ {myalg, funs, f, y, myvars, ideal, ord, x, s, i, j},

  If[ alg === 0, Return[True] ];
  If[ vars === {}, Return[FullSimplify[alg]===0] ];

  funs = Union[Cases[alg, Root[_,__]|Power[_,_Rational], Infinity]];
  funs = Transpose[{Array[f, Length[funs]], funs}];
  algnum = alg /. Apply[Rule, Reverse /@ funs, {1}] // Together // Numerator;

  (* defining relations of equation *)
  ideal = Table[funs[[i, 2]] /. 
            {Root[j_, _] -> j[f[i]], a_^j_ :> f[i]^Denominator[j]-a^Numerator[j]},
            {i, 1, Length[funs]}];
  (* saturation *)
  ideal = Join[ideal, Table[f[i]*y[i] - 1, {i, 1, Length[funs]}]];

  (* definition of function *)
  ideal = Append[ideal, f[0] - algnum];

  (* compute defining equation for function *)
  ideal = GroebnerBasis[
             ideal,
             {f[0]},
             Join[Array[f, Length[funs]], Array[y, Length[funs]]]
          ];

  (* detect order of recurrence *)
  ord = Exponent[First[ideal], f[0]];

  (* consider the first ord items of the series expansion of algnum along the first variable *)
  x = First[vars];
  s = Series[algnum /. Apply[Rule, funs, {1}], {x, 0, ord}];

  If[ Head[s] === SeriesData, s = s[[3]], Return[ AlgebraicFunctionZeroQ[s, Rest[vars]]] ];

  (* compare all the coefficients to zero *)
  For[ i = 1, i <= Length[s], i++,
    If[ !AlgebraicFunctionZeroQ[s[[i]], Rest[vars]], Return[False] ];
  ];

  (* the whole thing is zero *)
  Return[True];
];

(**
 * FindRelations[roots, vars]
 *
 * roots... a list of algebraic functions, given as Root objects involving vars
 * vars...  list of indeterminates.
 *
 * returns a list of integer vectors {b[1],...,b[d]} generating the lattice of
 * all vectors v with
 *
 *   Product[roots[i]^v[i], {i}] == 1.
 *
 * The procedure does not necessarily terminate. It should terminate with probability 1.
 * (We have no proof for this, however.)
 **)
FindRelations[roots_, vars_] :=
  Module[ {L, n, hom, done, rhs, check},

    L = IdentityMatrix[Length[roots]];

    For[ n = 1, !And@@(AlgebraicFunctionZeroQ[Times@@(roots^#)-1, vars]& /@ L), n++,

      If[ n > 1, Print["more than one iteration necessary"] ];

      hom = Thread[vars -> rhs] /. rhs :> Rationalize[Random[], 10^(-n-1)];
      L = ZModuleIntersect[L, FindRelations[roots /. hom]];
    ];

    Return[L];
  ];

(**
 * FindRelations[roots]
 *
 * roots... a list of algebraic numbers, given as Algebraic or as Root objects
 * 
 * returns a list of integer vectors {b[1],...,b[d]} generating the lattice of 
 * all vectors v with
 *
 *   Product[roots[i]^v[i], {i}] == 1 .
 * 
 * If the roots are given as members of the same algebraic extension of Q, then 
 * the procedure has polynomial runtime. Otherwise, a common algebraic extension
 * field of the given roots is computed, and this may take long.
 **)
FindRelations[roots_List] := 
   Module[ {i, z, a, bound, reLog, imLog, m, m1, m2, time}, 

   (* first treat zeros in the root list. Assume 0^0 = 1 *)

   If[ MatchQ[ roots, {0...} ], Return[ {} ] ];

   If[ !FreeQ[ roots, 0, 1], 

       ex = Position[roots, 0, 1]; (* positions of the zeroes *)
       B = FindRelations[ DeleteCases[roots, 0] ]; (* basis for the nonzero numbers *)
       Do[ B = Insert[#, 0, ex[[i, 1]] ]& /@ B, {i, 1, Length[ex]}]; (* insert new dimensions *)

       Return[ B ];
   ];

   DebugPrint["FR 1"];

   {time, a} = Timing[ToNumberField[roots]]; (* does nothing if the roots all belong to the same field *)
   PrimitiveElementTime += time;

   DebugPrint["FR 2"];

   reLog = Re[Log[a]];
   imLog = Append[Im[Log[a]], 2*Pi];

   DebugPrint["FR 3"];

   (* replace implicit zeros by explicit ones. *)
   For[i = 1, i <= Length[a], i++,

      z = a[[i]];

      (* Abs[z] == 1 *)
      If[ Abs[N[Abs[z]]-1]<.1 && FullSimplify[Abs[z]] === 1, reLog[[i]] = 0 ];

      (* z is real and z >= 0 *)
      If[ Element[z, Reals] && Element[Sqrt[z], Reals], 
        imLog[[i]] = 0, 
        Null,
         (* try harder if no decision was found *)
         If[ Element[RootReduce[z], Reals] && Element[Sqrt[RootReduce[z]], Reals], imLog[[i]] = 0 ];
      ];

   ];

   DebugPrint["FR 4"];

   (* compute a bound for the coefficients of the generators *)
   bound = MasserBound[a]; 

   DebugPrint["FR 5"];

   m = IdentityMatrix[Length[a]];

   (* successively refine the approximation until only valid generators are returned *)
   For[ level = Ceiling[N[Log[2, bound]] + 1], !(And@@(CheckRelation[a,#]&/@m)), level++, 

      DebugPrint["FR 6"];

      m1 = GetBasis[reLog, level, bound];
      m2 = Drop[#, -1]& /@ GetBasis[imLog, level, bound];
      m = ZModuleIntersect[m1, m2];
   ];

   DebugPrint["FR 7"];

   m
];

(** 
 * Computes the integer relations with coefficients bounded by bound of the real numbers in l based on
 * continued fraction approximations of at least the specified level. Arbitrary expressions are allowed
 * as elements of l, as long as N is able to map them to a float. However, it is assumed that an 
 * expression that is different from 0 corresponds to a number that is different from zero. 
 *
 * The returned basis is guaranteed to contain all integer relations for l with coefficients bounded by
 * bound, but it may contain additional, wrong, "relations", if the approximation level is chosen too 
 * small. For sufficiently large level, only true relations will be returned.
 **)
GetBasis[l_List, level_Integer, bound_Integer] :=
   Module[ {B, i, j, c1, c2, d, e, ex, n, lev},

    n = Length[l];

    (* first treat zero elements in l as special cases *)

    If[ MatchQ[l, {0..}], (* l has zeroes only *)

       Return[IdentityMatrix[n]] 
    ]; 

    If[ !FreeQ[l, 0, 1], (* l contains at least one zero *)

       ex = Position[l, 0, 1]; (* positions of the zeroes *)
       B = GetBasis[ DeleteCases[l, 0], level, bound]; (* basis for the nonzero numbers *)
       Do[ B = Insert[#, 0, ex[[i, 1]] ]& /@ B, {i, 1, Length[ex]}]; (* insert new dimensions *)
       B = Join[B, IdentityMatrix[n][[Flatten[ex]]] ]; (* add unit vectors at the zero positions *)

       Return[ B ];
    ];

    (* now we assume that l is a list of nonzero real numbers *)

    c1 = Last[Convergents[#, level]]& /@ l;
    c2 = Last[Convergents[#, level + 1]]& /@ l;

    e = Table[ 1/Denominator[c1[[i]]*c2[[i]]] , {i, 1, n}];
    (* cfrac theorem says: | log[i] - c1[i] | <= e[i] *)

    (* refine the approximation such that all errors are smaller than the smallest
       element of l in absolute value *)

    lev = level + 1;
    While[ (* exists i, j st e[i] >= c1[j], replace c1[j] by better approximation. *)
      Select[c1, (Max@@e >= Abs[#])&] =!= {} && lev < level + 5,

      ex = Flatten[Position[e, Max@@e]]; (* indices with greatest errors *)

      lev++;
      For[ i=1, i <= Length[ex], i++,
         j = ex[[i]];
         c1[[j]] = c2[[j]];
         c2[[j]] = Last[Convergents[ l[[j]], lev]];
         e[[j]] = If[ c1[[j]] == l[[j]], 0, 1/Denominator[c1[[j]] * c2[[j]]] ];
      ];
    ];

    (* now: max e[i] < min |c1[i]| *)

    (* this bound guarantees that generators whose norm is at most bound will
       appear in the LLL-reduced basis *)
    d = Ceiling[N[2^((Length[c1]-1)/2)*bound/(Min@@(Abs/@c1) - Max@@(Abs/@e))]];

    B = Transpose[Append[IdentityMatrix[n], c1*d]];
    B = LatticeReduce[B];

    (* Vectors whose right hand side is greater than the errors permit can be 
       discarded; they cannot correspond to integer relations. *)
    B = Select[B, (Abs[Last[#]] <= d*Sum[Abs[#[[j]]*e[[j]]], {j, 1, n}])&];

    (* the following old version was sufficient for some time but once became
       incomplete for some strange reason:
    B = Select[B, (Abs[Last[#]] <= d*Abs[Sum[#[[j]]*e[[j]], {j, 1, n}]])&];
    *)

    (* all remaining vectors are returned as candidates *)
    Drop[#, -1]& /@ B
];

(**
 * given a list of algebraic numbers {a[1],a[2],...}, all belonging to the same algebraic 
 * extension of Q, and an integer vector {e[1],e[2],...} this function returns
 * True if a[1]^e[1] * a[2]^e[2] * ... = 1, and False otherwise.
 **)
CheckRelation[a_List, e_List] := (Times@@(a^e) == 1);

Protect[FindRelations];

End[];

(* RISC header *)
If[$Notebooks,
   CellPrint[Cell[#, "Print", FontColor -> RGBColor[0, 0, 0], 
                              CellFrame -> 0.5, 
                              Background -> RGBColor[0.796887, 0.789075, 0.871107]]]&,
   Print
  ]["Dependencies.m by Manuel Kauers and Burkhard Zimmermann. \nChanged by Laura Kovacs for Invariant Generation. " <> 
    "\[LongDash] \[Copyright] RISC Linz \[LongDash] V " <> Dependencies`Private`Version];

EndPackage[];
