(* ::Package:: *)

(* ALIGATOR = 
Automated polynomial Loop Invariant Generation by Algebraic Techniques Over the Rationals *)

(* written by Laura Kovacs *)

(* work started at Research Institute for Symbolic Computation (RISC), *)
(* J.Kepler University Linz, Austria, http://www.risc.uni-linz.ac.at *)

(* work continued at Ecole Politechnique Federale de Lausanne (EPFL), Switzerland, http://mtc.epfl.ch *)
(* work maintained currently at Vienna University of Technology (TU Wien), Austria, http://www.complang.tuwien.ac.at/ *)

(* email: lkovacs@complang.tuwien.ac.at *)

(* ************************************************************************************** *)
(*                                   Aligator.m                                           *)
(* Automated Polynomial Invariant Generation by Algebraic Techniques for P-solvable Loops *)
(* Usage of Symbolic Summation and Polynomial Algebra for Invariant Generation ********** *)
(* ************************************************************************************** *)

(* INSTALLATION:                                                                          *)
(*   Put this file into some directory where Mathematica is able to find it.              *)
(*                                                                                        *)
(* BUGS:                                                                                  *)
(*   Please report bugs concerning this package to                                        *)
(*   Laura Kovacs (lkovacs@complang.tuwien.ac.at).                                        *)
(*   This package was updated and developed for Mathematica 11.                           *)
(*   We do not expect that it works with earlier/later versions.                          *)
(*                                                                                        *)
(* LICENCE:                                                                               *)
(*   This software package is licensed under the MIT License.                             *)
(*   However, please send an email to ahumenbe@forsyte.at and cite this work              *)
(*   appropiately, whenever you redistribute it and/or modify it.                         *)

(* -------------------------------------------------------------------------------------- *)

(* *************************************************** *)
(* ************ Package Initialization *************** *)
(* ** Function Attributes, Options, Error Messages *** *)
(* *************************************************** *)


Aligator`Private`Version = "0.5 (2010-09-14)";


BeginPackage["Aligator`",{"RISC`fastZeil`","RISC`Dependencies`","Hyper`"}];

aligator::InputError1 = "Not appropiate Aligator-input. `1` must be of the form WHILE[loop-condition, loop-body].\n
Given loop condition is not appropiate - it has to be a NON-EMPTY BOOLEAN CONDITION (without :=)!";

aligator::InputError2 = "Not appropiate Aligator-input.`1` must be of the form WHILE[loop-condition, loop-body].
Given loop-body has to be a sequence of the form: s0; IF[test, s1, s2]; s3, \n 
where s0, s1, s3 are SEQUENCES OF ASSIGNMENTS, s2 is a SEQUNECE OF ASSIGNMENTS or IF-STATEMENT, and all conditions are NON-EMPTY BOOLEAN CONDITIONS (without :=)! \n
Hint: check also for spellings (e.g. := instead of =, IF instead of If, ; instead of ,)!";

aligator::InputError3 = "Not appropiate Aligator-input.`1` must be of the form WHILE[loop-condition, loop-body].\n
WHILE has 2 arguments only!";

aligator::InputError4 = "Not appropiate Aligator-input.`1` must be of the form WHILE[loop-condition, loop-body].\n
Given input must be a WHILE loop!";

aligator::InputCorrect = "Appropiate Aligator-input.";


Unprotect[`Aligator, WHILE, IF,Body,
        InputCheck,AssgnCheck,IniVal,LoopCounter,
        LoopTransform,IfWhileTransform,LoopCondCheck,LoopBodyCheck,CheckIfSeq,FromLoopToRecs,
        RecSystem, RecEqs, RecSolve, RecRelations, FlattenRecurrences, FlattenBody,AssgnToChange,NormedVarList,
                   SimplifySeq, SimplifyVarList,ShiftRec,ProperRecVars,VarShiftChange,
        RecSolve,CFRulesList,PSolvableCheck,SeqToVars,EqRecSolve,ShiftBackClosedForm,ShiftBackSolSet,
        RecDependencyCheck,RecurrenceOrder,RecOrderCheck,
        LinRecCSolve, CFiniteCheck, CheckTerm, InhomCCheck, ShiftOrder, 
        InhomRecTransform, SolveCFinRecurrence,SolCFinConstruct,
        HypergeometricQ, GosperCheckAndSolve,
        IniValuesAndVarRules,InitialSubstitutions,
        InvLoopCond,CfIfLoopSeq,UniformInnerLoopVars,CFMerge,InvIdealLoopSeq,InnerLoopRewwriteRules,
        WP,WPInnerLoops,WPPolySet,InvariantFilter,CheckInvariant,PolyDependencyCheck,
        InvLoopAssg,
        CompletenessCheck,UnsortedComplement
];

SetAttributes[Aligator, HoldAll];
SetAttributes[AssgnCheck, HoldAll];
SetAttributes[InputCheck, HoldAll];
SetAttributes[LoopCondCheck, HoldAll];
SetAttributes[LoopBodyCheck, HoldAll];
SetAttributes[WHILE, HoldAll];
SetAttributes[IF, HoldAll];
SetAttributes[Body, HoldAll];
SetAttributes[LoopTransform, HoldAll];
SetAttributes[IfWhileTransform, HoldAll];
SetAttributes[CheckIfSeq, HoldAll];
(* SetAttributes[FromLoopToRecs, HoldAll]; *)
SetAttributes[RecSystem, HoldAll];
SetAttributes[RecEqs, HoldAll];


Aligator::usage = "Aligator[WHILE[c1, s1; IF[c2,s2,s3]; s2], LoopCounter->i, IniVal -> {assignments}] " <>
    "generates the polynomial invariant of the given loop if the loop is P-solvable.\n" <>
    "The loop counter variable is optionally specified by LoopCounter.\n" <>
    "The initial values of the variables are optionally specified by IniVal.";

IniVal::usage = "Option to Aligator for specifying initial values of variables.";
LoopCounter::usage = "Option to Aligator for specifying the loop counter variable";


Begin["`Private`"];


(*******************************************************)
(* ***************** RISC/EPFL Header **************** *)
(*******************************************************)


If[ $Notebooks,
    CellPrint[Cell[#,
    "Print",FontColor->RGBColor[0,0,0],CellFrame->0.5,Background->RGBColor[0.796887,0.789075,0.871107]]]&,
    Print
]["Aligator.m \n"<>"Automated Loop Invariant Generation by Algebraic Techniques Over the Rationals.\n"<>
"Package written by Laura Kovacs"
<>" \[LongDash] \[Copyright] TU Wien \[LongDash] V "<>Aligator`Private`Version];


(* *************************************************** *)
(* ************ Aligator User Interface  ************* *)
(* *************************************************** *)


Options[Aligator] = {IniVal->{},LoopCounter->i};

RecEqs[{seq_:CompoundExpression[]}] := RecEqs[seq,{}]

Aligator[c_, opts__ : OptionPattern[]] :=
    Module[ {invariants = {},givenIniRecs,givenIniRules},
        (* Specific option handling to avoid evaluation of initial values. *)
        SetOptions[Aligator,LoopCounter->OptionValue[Aligator,Unevaluated[{opts}],LoopCounter]];
        invariants    = Aligator[c];
        givenIniRecs  = OptionValue[Aligator,Unevaluated[{opts}],IniVal,RecEqs];
        givenIniRules = Association @ InitialSubstitutions[givenIniRecs,{}];
        keys = Keys[$InitValues];
        vals = Values[$InitValues];
        vals = vals /. givenIniRules;
        $InitValues = Thread[keys -> vals];
        $InitValues = AssociateTo[givenIniRules, $InitValues] // PrintDebug["Final initial values"];
        Simplify[invariants /. $InitValues]
    ]


Aligator[c_] :=
    Module[ {sw,ifCheck,loops,invariants = {}},
        sw = InputCheck[c];
        If[ sw == 0,
            Abort[]
        ];
        (* correct input - proceed! *)
        ifCheck = CheckIfSeq[c];
        (* Print["If-statements: ",ifCheck]; *)
        loops = IfWhileTransform[c,Body[],Body[]];
        (* Print["Number of inner loops:", Length[loops]]; *)
        (* Print["Loops:",loops]; *)
        If[ !ifCheck, 
            (* no conditional branches - invariant generation for loops with assignments only*)
            (* Print["No If-statements!"]; *)
            invariants = InvLoopAssg[loops],
            (* with conditional branches - invariant generation for loops with assignments only*)
            (*Print["With If-statements!"];*)
            invariants = InvLoopCond[loops]
        ];
        (* transform polys into poly equalities *)
        If[invariants == {},
            Print["No invariants found!"]; {},
            Simplify[And@@(Equal[#,0]&/@invariants)]
        ]
    ]


InitialSubstitutions[{x_==rhs_,seq___},iniValList_] = Module[ {newIniList},
                                                          newIniList = Join[iniValList,{Rule[x[0],rhs]}];
                                                          InitialSubstitutions[{seq},newIniList]
                                                      ]


InitialSubstitutions[{},iniValList_] = iniValList


IniValuesAndVarRules[finVars_,iniVars_] :=
    Module[ {i,rules = {}},
        Do[
        rules = Append[rules,iniVars[[i]]->finVars[[i]][0]]
        ,{i,1,Length[finVars]}
        ];
        rules
    ]


(* *************************************************** *)
(* ********** Part 0: Input Format Check  ************ *)
(* *************************************************** *)


(* Check if the Aligator input is in appropiate loop format *)


AssgnCheck[CompoundExpression[],assgnlist_] :=
    assgnlist


AssgnCheck[CompoundExpression[lhs_ := rhs_, cmds__],assgnlist_]/;lhs==rhs :=
    0


AssgnCheck[CompoundExpression[lhs_ := rhs_],assgnlist_]/;lhs==rhs :=
    0


AssgnCheck[lhs_ := rhs_,assgnlist_]/;lhs==rhs :=
    0


AssgnCheck[CompoundExpression[lhs_ := rhs_, cmds__],assgnlist_] :=
    AssgnCheck[CompoundExpression[cmds],assgnlist]


AssgnCheck[CompoundExpression[lhs_ := rhs_],assgnlist_] :=
    AssgnCheck[CompoundExpression[],assgnlist]


AssgnCheck[lhs_ := rhs_,assgnlist_] :=
    AssgnCheck[CompoundExpression[],assgnlist]


AssgnCheck[seq___,assgnlist_] :=
    0


LoopCondCheck[cond_,condcheck_]/;(ToString[Hold[cond]]==ToString[Hold[Null]]) :=
    0


LoopCondCheck[CompoundExpression[b1_, b2__],condcheck_] :=
    0


(*put check for :=-free conditions *)


LoopCondCheck[cond_,condcheck_] :=
    condcheck


(* ********************* The given loop body is of the following form **************************** *)
(* ** Assignments_List0; IF[..., Assignments_List _Then, Else_branch]; Assgnments_List1], where: ** *)
(* (1) Assignments_List0, Assignments_List _Then and Assignments_List1 are sequences of assignments *)
(* (2) Else_Branch is either a sequence of assignments or an IF statement. ************************ *)
(* ************************************************************************************************ *)


(* ********************* The test below is more general. ***************************************** *)
(* It allows Assignments_List _Then to be also either a list of assignments, or an IF statement.*** *)
(* ************************************************************************************************ *)


LoopBodyCheck[body_,bodycheck_]/;(AssgnCheck[body,1]==1) :=
    bodycheck


LoopBodyCheck[IF[bif_,s1_],bodycheck_]/; (LoopCondCheck[bif,1]==1) :=
    LoopBodyCheck[s1,bodycheck]


LoopBodyCheck[IF[bif_,s1_,s2_],bodycheck_]/; (LoopCondCheck[bif,1]==1) :=
    Module[ {thencheck},
        thencheck := LoopBodyCheck[s1,bodycheck];
        LoopBodyCheck[s2,thencheck]
    ]


LoopBodyCheck[CompoundExpression[s0__,
              IF[bif_,s1_]],bodycheck_]/;(AssgnCheck[CompoundExpression[s0],1]==1) :=
    LoopBodyCheck[IF[bif,s1],bodycheck]


LoopBodyCheck[CompoundExpression[s0__,
              IF[bif_,s1_,s2_]],bodycheck_]/;(AssgnCheck[CompoundExpression[s0],1]==1) :=
    LoopBodyCheck[IF[bif,s1,s2],bodycheck]


LoopBodyCheck[CompoundExpression[IF[bif_,s1_],
              s3__],bodycheck_]/;(AssgnCheck[CompoundExpression[s3],1]==1) :=
    LoopBodyCheck[IF[bif,s1],bodycheck]


LoopBodyCheck[CompoundExpression[IF[bif_,s1_,s2_],
              s3__],bodycheck_]/;(AssgnCheck[CompoundExpression[s3],1]==1) :=
    LoopBodyCheck[IF[bif,s1,s2],bodycheck]


LoopBodyCheck[CompoundExpression[s0__,
              IF[bif_,s1_],
              s3__],bodycheck_]/;((AssgnCheck[CompoundExpression[s0],1]==1) && (AssgnCheck[CompoundExpression[s3],1]==1) ) :=
    LoopBodyCheck[IF[bif,s1],bodycheck]


LoopBodyCheck[CompoundExpression[s0__,
              IF[bif_,s1_,s2_],
              s3__],bodycheck_]/;((AssgnCheck[CompoundExpression[s0],1]==1) && (AssgnCheck[CompoundExpression[s3],1]==1) ) :=
    LoopBodyCheck[IF[bif,s1,s2],bodycheck]


LoopBodyCheck[seq__,condcheck_] :=
    0


InputCheck[WHILE[b_,c___]]/;(LoopCondCheck[b,1]==0) :=
    Module[ {},
        Message[aligator::InputError1,"Input"];
        0
    ]


InputCheck[WHILE[b_,c_]]/;(LoopBodyCheck[c,1]==0) :=
    Module[ {},
        Message[aligator::InputError2,"Input"];
        0
    ]


InputCheck[WHILE[b_,c_]]/;((LoopBodyCheck[c,1]==1) && (LoopCondCheck[b,1]==1)) :=
    Module[ {},
    (* Message[aligator::InputCorrect,msg]; *)
        1
    ]


InputCheck[WHILE[b_,c1_,c2__]] :=
    Module[ {},
        Message[aligator::InputError3,"Input"];
        0
    ]


InputCheck[c___] :=
    Module[ {},
        Message[aligator::InputError4, "Input"];
        0
    ]


(* ******************************************************************************* *)
(* ********************** Part I: Loop Transformation Tools ********************** *)
(* Input: WHILE loop with k>=1 conditional branches. 
     Smth of the form: WHILE[\[Ellipsis],s_ 0;IF[\[Ellipsis],s_ 1,IF[\[Ellipsis],s_ 2,...]...],s_k+1 ******* *)
(* Output: k inner loops. Smth of the form {{s_ 0;s_ 1;s_k+1},\[Ellipsis],{s_ 0;s_k;s_k+1}}.  *)
(* ******************************************************************************* *)


Body[seq1___,Body[]] :=
    Module[ {},
        Body[seq1]
    ]


Body[Body[],seq2___] :=
    Module[ {},
        Body[seq2]
    ]


Body[Body[CompoundExpression[seq1___,
          seq2___]],Body[CompoundExpression[seq3___,
                         seq4___]]] :=
    Module[ {},
        Body[CompoundExpression[seq1,
             seq2,
             seq3,
             seq4]]
    ]


Body[Body[seq1___],Body[CompoundExpression[seq2___,
                        seq3___]]] :=
    Module[ {},
        Body[CompoundExpression[seq1,
             seq2,
             seq3]]
    ]


Body[Body[CompoundExpression[seq1___,
          seq2___]],Body[seq3___]] :=
    Module[ {},
        Body[CompoundExpression[seq1,
             seq2,
             seq3]]
    ]


Body[Body[seq1___],Body[seq2___]] :=
    Module[ {},
        Body[CompoundExpression[seq1,
             seq2]]
    ]


Body[Body[seq___]] :=
    Module[ {},
        Body[seq]
    ]


Body[CompoundExpression[s_]] :=
    Module[ {},
        Body[s]
    ]


CheckIfSeq[loop_] :=
    Not[FreeQ[Body[loop],IF]]


IfWhileTransform[WHILE[b_,c__],beforeSt_,afterSt_] :=
    Module[ {innerLoops},
        innerLoops = Flatten[LoopTransform[c,beforeSt,afterSt]];
        (* in case an inner loop is empty body, Body[], remove it *)
        DeleteCases[innerLoops,Body[],Infinity]
    ]


LoopTransform[body_,beforeSt_,afterSt_]/;(FreeQ[Body[body],IF]) :=
    Body[ Evaluate[Body[beforeSt,Evaluate[Body[body]]]], afterSt]


LoopTransform[IF[bif_,s1_],beforeSt_,afterSt_] :=
    {LoopTransform[s1,beforeSt,afterSt],LoopTransform[Body[],beforeSt,afterSt]}


LoopTransform[IF[bif_,s1_,s2_],beforeSt_,afterSt_] :=
    {LoopTransform[s1,beforeSt,afterSt],LoopTransform[s2,beforeSt,afterSt]}


LoopTransform[CompoundExpression[s0__,
              IF[bif_,s1_]],beforeSt_,afterSt_] :=
    {LoopTransform[s1,Evaluate[Body[beforeSt,Body[CompoundExpression[s0]]]],afterSt],LoopTransform[Body[],Evaluate[Body[beforeSt,Body[CompoundExpression[s0]]]],afterSt]}


LoopTransform[CompoundExpression[s0__,
              IF[bif_,s1_,s2_]],beforeSt_,afterSt_] :=
    {LoopTransform[s1,Evaluate[Body[beforeSt,Body[CompoundExpression[s0]]]],afterSt],LoopTransform[s2,Evaluate[Body[beforeSt,Body[CompoundExpression[s0]]]],afterSt]}


LoopTransform[CompoundExpression[IF[bif_,s1_],
              s3__],beforeSt_,afterSt_] :=
    {LoopTransform[s1,beforeSt,Evaluate[Body[Body[CompoundExpression[s3]],afterSt]]],LoopTransform[Body[],beforeSt,Evaluate[Body[Body[CompoundExpression[s3]],afterSt]]]}


LoopTransform[CompoundExpression[IF[bif_,s1_,s2_],
              s3__],beforeSt_,afterSt_] :=
    {LoopTransform[s1,beforeSt,Evaluate[Body[Body[CompoundExpression[s3]],afterSt]]],LoopTransform[s2,beforeSt,Evaluate[Body[Body[CompoundExpression[s3]],afterSt]]]}


LoopTransform[CompoundExpression[s0__,
              IF[bif_,s1_],
              s3__],beforeSt_,afterSt_] :=
    {LoopTransform[s1,Evaluate[Body[beforeSt,Body[CompoundExpression[s0]]]],Evaluate[Body[Body[CompoundExpression[s3]],afterSt]]],LoopTransform[Body[],Evaluate[Body[beforeSt,Body[CompoundExpression[s0]]]],Evaluate[Body[Body[CompoundExpression[s3]],afterSt]]]}


LoopTransform[CompoundExpression[s0__,
              IF[bif_,s1_,s2_],
              s3__],beforeSt_,afterSt_] :=
    {LoopTransform[s1,Evaluate[Body[beforeSt,Body[CompoundExpression[s0]]]],Evaluate[Body[Body[CompoundExpression[s3]],afterSt]]],
LoopTransform[s2,Evaluate[Body[beforeSt,Body[CompoundExpression[s0]]]],Evaluate[Body[Body[CompoundExpression[s3]],afterSt]]]}



(* ****************************************************************** *)
(* Input: Something of the form Body[{x:=x+1; y:=y+2}]*************** *)
(* Output: Something of the form ************************************ *)
(*        {{x[n+1]==x[n]+1, y[n+1]==y[n]+2}, {{x[n],x},{y[n],y}}, {n}} *)
(* ****************************************************************** *)


FromLoopToRecs[Body[seq__]] :=
    Module[ {},
        RecSystem[seq]
    ]


(* *********************************************************** *)
(* ***** Part II: Recurrence System Construction Tools ******* *)
(* *********************************************************** *)


(* *********************************************************** *)
(* ******* Recurrence System of the Loop Body **************** *)
(* Input:Something of the form {x:=x+1; y:=y+2} ************** *)
(* Output: Something of the form 
{{x[n+1]==x[n]+1, y[n+1]==y[n]+2}, {{x[n],x},{y[n],y}}, {n}} *)
(* representing the recurrence system of the (simplified) loop. *)
(* *********************************************************** *)


RecSystem[List[assgn__]] :=
    RecSystem[assgn]


RecSystem[assgn__] :=
    Module[ {assgAll,recAssg,n = Unique[],recVars,recEqSystem, recVarList,finalRecEqSystem,finalRecVarList,flattenRecEqSystem,flattenRecVarList,allVars,recChangedVarList,notRecVar,notRecChangedVars,removeVar,normVal,normalizedRecEqSystem,normalizedRecVarList,normedVars,shiftVarsNormed,i},
        assgAll                  = RecEqs[assgn,{}];
        {recAssg,recVars}        = FlattenBody[assgAll,{},{}];
        {recRel,recVarList}      = RecRelations[recAssg,n,{},{},recVars];
        {recEqSystem,recVarList} = FlattenRecurrences[recRel,n,recRel,recVarList];
        recEqSystem              = ShiftRec[#,n]&/@recEqSystem;

        (* Create replacement rules for starting values; needed if recurrences of order > 1 are involved *)
        assignRules = Cases[recRel, x_[y_] == rhs_ /; FreeQ[rhs,x] && FreeQ[recEqSystem,x] -> (x[y] -> rhs)];
        recOrders   = Association @ Flatten @ (MaximalBy[Value] @ Cases[#,x_[n+b_.] -> (x->b),Infinity]& /@ recEqSystem);
        $InitValues = DeleteCases[recVarList, {x_[_],x_}];
        $InitValues = ($InitValues /. x_[n + b_.] :> x[n + b + recOrders[x]]);
        $InitValues = ($InitValues /. {x_,y_} -> (x -> y[n+1]));
        $InitValues = $InitValues /. assignRules;
        $InitValues = $InitValues /. n -> 0;

        recEqSystem    = recEqSystem/.OptionValue[Aligator,LoopCounter]->n;
        recChangedVars = ProperRecVars[recEqSystem,n,{}];
        If[ recChangedVars == {},
            Print["No recursively changed variables! Not P-solvable Loop!"];
            Abort[]
        ];
        (* make shifts, if index contains minus operations, i.e. n-1 should be shifted to n *)
        {finalRecEqSystem,finalRecVarList} = ShiftRec[{recEqSystem,recVarList},n];
        (* {finalRecEqSystem,finalRecVarList} = ShiftRec[recEqSystem,n,recVarList,{}]; *)
        allVars           = Union[Table[finalRecVarList[[i,2]],{i,1,Length[recVarList]}]];
        notRecChangedVars = Complement[allVars,recChangedVars];
        recChangedVarList = finalRecVarList;
        Do[
            removeVar         = notRecChangedVars[[i]];
            recChangedVarList = DeleteCases[recChangedVarList,{_,removeVar},Infinity],
            {i,1,Length[notRecChangedVars]}
        ];
        normVal = Min[Cases[finalRecEqSystem,_[n+i_.]->i,Infinity]];
        {normalizedRecEqSystem,normedVars} = {finalRecEqSystem,recChangedVarList};
        If[ normVal > 0, (* there is an extra shift in the recSystem. It is not needed! *)
            {normalizedRecEqSystem,normedVars} = {finalRecEqSystem,normedVars}/.n->n-normVal;
            shiftVarsNormed = Min[Cases[normedVars,_[n+i_.]->i,Infinity]];
            If[ shiftVarsNormed < 0,
                normedVars = NormedVarList[normedVars,n,{}]
            ]
        ];
        {normalizedRecEqSystem,normedVars,{n}}
    ]


(* if there are not used variables, due to auxiliary vars in loop body, remove them from the varList *)
(* unused if they refer to positions that are lower than the order of recSystem *)


NormedVarList[{},n_,VarList_] :=
    VarList


NormedVarList[{vars1_,seq___},n_,VarList_] :=
    Module[ {i,minVal},
        minVal = Min[Cases[vars1,_[n+i_]->i,Infinity]];
        If[ minVal<0,
            NormedVarList[{seq},n,VarList],
            NormedVarList[{seq},n,Join[VarList,{vars1}]]
        ]
    ]


(* ************************************************************* *)
(* ************ Removing multiple variable changes ************* *)
(* Input: smth like {x==x+1; y==y+x; x==x+2},{},{} **************  *)
(* Output: smth like {y==y+x+1; x==x+3},{x,y} ******************** *)
(* ************************************************************* *)


AssgnToChange[{seq1___,x_==rhs_,seq2___},x_,ruleX_] :=
    Module[ {seq2Changed},
        seq2Changed = {seq2}/.ruleX;
        Join[{seq1},seq2Changed]
    ]


FlattenBody[{x_==rhs_,seq__},Vars_,assgnList_] :=
    Module[ {ruleX,rhsMod,assgnListMod,VarsMod,changedSeq},
        If[ MemberQ[Vars,x],
        (* THEN branch: it already appeared -> simplify body *)
            ruleX = Apply[Rule,Cases[assgnList,x==_],{1}];
            rhsMod = rhs/.ruleX;
            (*update AssgnList by rewriting x, and adding the new assgn of x *)
            changedSeq = AssgnToChange[assgnList,x,ruleX];
            assgnListMod = Append[changedSeq,x==rhsMod];
            VarsMod = Vars,
            (* ELSE branch: it has not yet *)
            VarsMod = Append[Vars,x];
            assgnListMod = Append[assgnList,x==rhs]
        ];
        FlattenBody[{seq},VarsMod,assgnListMod]
    ]


FlattenBody[{x_==rhs_},Vars_,assgnList_] :=
    Module[ {ruleX,rhsMod,assgnListMod,VarsMod,changedSeq},
        If[ MemberQ[Vars,x],
        (* THEN branch: it already appeared -> simplify body *)
            ruleX = Apply[Rule,Cases[assgnList,x==_],{1}];
            rhsMod = rhs/.ruleX;
            (*update AssgnList by rewriting x, and adding the new assgn of x *)
            changedSeq = AssgnToChange[assgnList,x,ruleX];
            assgnListMod = Append[changedSeq,x==rhsMod];
            VarsMod = Vars,
            (* ELSE branch: it has not yet *)
            VarsMod = Append[Vars,x];
            assgnListMod = Append[assgnList,x==rhs]
        ];
        {assgnListMod,VarsMod}
    ]


(* **************************************************************** *)
(* *******  Constructing the Recurrence System ******************** *)
(* Input:Something of the form {x==x+1; y==y+x},n,{},{},{x,y} ***** *)
(* Output: Something of the form 
{{x[n+1]==x[n]+1, y[n+1]==y[n]+x[n+1]}, {{x[n],x},{y[n],y}}, {n}} *)
(* representing the recurrence system of the (simplified) loop. *** *)
(* Dependencies of variables are handled. ************************* *)
(* **************************************************************** *)


RecRelations[{x_==rhs_,seq__},n_,LLhs_,RecRels_,Vars_] :=
    Module[ {rhsVarsX,rules = {},changedSoFarX,remainingRulesX,xInd = n,LLhsMod,RecRelsMod,rulesSoFarX},
        rhsVarsX = Complement[Vars,{x}];
        (*RHSVars[rhs,{}],*)
        changedSoFarX = Complement[Cases[LLhs,z_[_]->z,{2}],{x}];
        (* shift by one., i.e. y+1 will be written as  y[n+1]+1 and not y[n]+1 if assignment on y was computed already *)
        rulesSoFarX = Map[Plus[#,1]&,
                          Apply[Rule,DeleteCases[Map[Reverse,LLhs,{1}],{x,x[_]}],{1}],
                                         {3}];
        (* unmodified variables are as x[n]*)
        remainingRulesX = Rule[#,#[n]]&/@Complement[rhsVarsX,changedSoFarX];
        rules = Union[rules,rulesSoFarX,remainingRulesX];
        If[ MemberQ[Cases[LLhs,z_[_]->z,{2}],x],
            (* x was already modified *)
            xInd = Cases[LLhs,x[z_]->z,{2}][[1]];
            rules = Join[rules,{x->x[xInd+1]}];
            LLhsMod = Join[DeleteCases[LLhs,{x[xInd],x}],{{x[xInd+1],x}}];
            xInd = xInd+1,
    (*ELSE*)
            rules = Join[rules,{x->x[xInd]}];
            LLhsMod = Join[LLhs,{{x[xInd],x}}]
        ];
        RecRelsMod = Join[RecRels,{x[xInd+1]==(rhs/.rules)}];
        RecRelations[{seq},n,LLhsMod,RecRelsMod,Vars]
    ]


RecRelations[{x_==rhs_},n_,LLhs_,RecRels_,Vars_] :=
    Module[ {rhsVarsX,rules = {},changedSoFarX,remainingRulesX,xInd = n,LLhsMod,RecRelsMod,rulesSoFarX},
        rhsVarsX = Complement[Vars,{x}];
        changedSoFarX = Complement[Cases[LLhs,z_[_]->z,{2}],{x}];
        rulesSoFarX = Map[Plus[#,1]&,
                          Apply[Rule,DeleteCases[Map[Reverse,LLhs,{1}],{x,x[_]}],{1}],
                                         {3}];
        remainingRulesX = Rule[#,#[n]]&/@Complement[rhsVarsX,changedSoFarX];
        rules = Union[rules,rulesSoFarX,remainingRulesX];
        If[ MemberQ[Cases[LLhs,z_[_]->z,{2}],x],
            (* x was already modified *)
            xInd = Cases[LLhs,x[z_]->z,{2}][[1]];
            rules = Join[rules,{x->x[xInd+1]}];
            LLhsMod = Join[DeleteCases[LLhs,{x[xInd],x}],{{x[xInd+1],x}}];
            xInd = xInd+1,
    (*ELSE*)
            rules = Join[rules,{x->x[xInd]}];
            LLhsMod = Join[LLhs,{{x[xInd],x}}]
        ];
        RecRelsMod = Join[RecRels,{x[xInd+1]==(rhs/.rules)}];
        {RecRelsMod, LLhsMod}
    ]


(* *************************************************************** *)
(* ****  Changing := Assignments into == Recurrence Equality ***** *)
(* Input:Something of the form {x:=x+1; y:=y+x},{} *************** *)
(* Output: Something of the form {x==x+1, y==y+x+x} *************** *)
(* *************************************************************** *)


RecEqs[CompoundExpression[],recSystem_] :=
    recSystem


RecEqs[CompoundExpression[x_ :=
                              rhs_],recSystem_] :=
    RecEqs[CompoundExpression[],Join[recSystem,{x==rhs}]]


RecEqs[x_ :=
           rhs_,recSystem_] :=
    RecEqs[CompoundExpression[],Join[recSystem,{x==rhs}]]


RecEqs[CompoundExpression[x_ :=
                              rhs_,
       seq__],recSystem_] :=
    RecEqs[CompoundExpression[seq],Join[recSystem,{x==rhs}]]


(* ****************************************************************************** *)
(* ****** Removing cycles introduced by auxiliary variables ********************* *)
(* Input: smth like {x[n+1]==t[n];r[n+1]==r[n]+x[n]}, {{x[n],x},{t[n],t},{r[n],r}} *)
(* Output: smth like {r[n+1]==r[n]+t[n-1]}, {{t[n-1],x},{t[n],t},{r[n],r}} ******* *)
(* ****************************************************************************** *)


FlattenRecurrences[{x_[y_]==rhs_,seq__},n_,recSystem_,VarList_] :=
    Module[ {xInRhs,recSystemMod,recList,seqMod,VarListMod},
        xInRhs = Cases[rhs,x[z_]->x[z],Infinity,Heads->True];
        If[ xInRhs=={},
            (* rhs is free of x -> x[y]=rhs is NOT a recurrence equation! *)
            recList = DeleteCases[recSystem,x[y]==rhs];
            VarListMod = SimplifyVarList[VarList,x[y]==rhs,n];
            recSystemMod = SimplifySeq[recList,x[y]==rhs,n,{}];
            seqMod = SimplifySeq[{seq},x[y]==rhs,n,{}],
            (* rhs is NOT free of x -> x[y]=rhs is a recurrence equation! *)
            recSystemMod = recSystem;
            VarListMod = VarList;
            seqMod = {seq}
        ];
        FlattenRecurrences[seqMod,n,recSystemMod,VarListMod]
    ]


FlattenRecurrences[{x_[y_]==rhs_},n_,recSystem_,VarList_] :=
    Module[ {xInRhs,recSystemMod,recList,VarListMod},
        xInRhs = Cases[rhs,x[z_]->x[z],Infinity,Heads->True];
        If[ xInRhs=={},
            (* rhs is free of x -> x[y]=rhs is NOT a recurrence equation! *)
            recList = DeleteCases[recSystem,x[y]==rhs];
            VarListMod = SimplifyVarList[VarList,x[y]==rhs,n];
            recSystemMod = SimplifySeq[recList,x[y]==rhs,n,{}],
            (* rhs is NOT free of x -> x[y]=rhs is a recurrence equation! *)
            recSystemMod = recSystem;
            VarListMod = VarList
        ];
        {recSystemMod,VarListMod}
    ]


(* ******************************************************************** *)
(* ****** Removing variable cycles introduced by auxiliary variables ** *)
(* Input: smth like {{x[n],x},{t[n],t},{r[n],r}}, {x[n+1]==t[n]} ******* *)
(* Output: smth like {{t[n-1],x},{t[n],t},{r[n],r}} ******************** *)
(* ********************************************************************* *)


SimplifyVarList[VarList_,x_[y_]==expr_,n_] :=
    Module[ {ruleX,args,shiftSeq,shiftVals,shiftRules},
        ruleX = x[y]->expr;
        args = Cases[VarList,x[z_]->z,Infinity,Heads->True];
        shiftSeq = (y-#)&/@args;
        shiftVals = (n-#)&/@shiftSeq;
        shiftRules = ruleX/.(n->#)&/@shiftVals;
        VarList/.shiftRules
    ]


(* ************************************************************ *)
(* ***** Removing cycles introduced by auxiliary variables **** *)
(* ***** Auxiliary function of FlattenRecurrences ************* *)
(* ************************************************************ *)


SimplifySeq[{eq1_,seq__},x_[y_]==expr_,n_,eqs_] :=
    Module[ {ruleX = x[y]->expr,args,shiftSeq,shiftVals,eqsMod,shiftRules},
        args = Cases[eq1,x[z_]->z,Infinity,Heads->True];
        shiftSeq = (y-#)&/@args;
        shiftVals = (n-#)&/@shiftSeq;
        shiftRules = ruleX/.(n->#)&/@shiftVals;
        eqsMod = Join[eqs,{eq1/.shiftRules}];
        (*make the variable correspondence change*)
        SimplifySeq[{seq},x[y]==expr,n,eqsMod]
    ]


SimplifySeq[{eq1_},x_[y_]==expr_,n_,eqs_] :=
    Module[ {ruleX = x[y]->expr,args,shiftSeq,shiftVals,eqsMod,shiftRules},
        args = Cases[eq1,x[z_]->z,Infinity,Heads->True];
        shiftSeq = (y-#)&/@args;
        shiftVals = (n-#)&/@shiftSeq;
        shiftRules = ruleX/.(n->#)&/@shiftVals;
        eqsMod = Join[eqs,{eq1/.shiftRules}];
        eqsMod
    ]


SimplifySeq[{},x_[y_]==expr_,n_,eqs_] :=
    eqs


(* ************************************************************ *)
(* ****** Shifting the Recurrence Index *********************** *)
(* Input: smth like {{x[n+1]==x[n-1]+x[n]}, {{x[n],x},{x[n-1],t} *)
(* Output: smth like {{x[n+2]==x[n]+x[n+1]},{{x[n+1],x},{x[n],t} *)
(* ************************************************************* *)


ShiftRec[system_,n_] :=
    Module[ {args,shift},
        args = Cases[Flatten[system],_[z_]->z,Infinity,Heads->True];
        shift = Apply[Min,#-n&/@args];
        If[ shift<0,
            system/.(n->n-shift),
            system
        ]
    ]


(* ShiftRec[{},n_,VarList_,recSystem_]:={recSystem,VarList} *)


(* ShiftRec[{x_[y_]==rhs_,seq___},n_,VarList_,recSystem_]:=
Module[{shiftRule,shift,i,newSystem,newVars},
shift=Min[Cases[{x[y]==rhs},_[n+i_.]->i,Infinity,Heads->True]];
If[shift<0, (*make a shift*)
    shiftRule=n->n-shift;
    newSystem=Append[recSystem,(x[y]==rhs)/.shiftRule];
    newVars=VarShiftChange[VarList,x,shiftRule,{}],
(*no shift needed *)
newSystem=Append[recSystem,x[y]==rhs];
newVars=VarList
];
ShiftRec[{seq},n,newVars,newSystem]
] *)


(* VarShiftChange[{},x_,shiftRule_,shiftedVars_]:=shiftedVars *)


(* VarShiftChange[{varCorresp_,seq___},x_,shiftRule_,shiftedVars_]:=
Module[{f,newCorresp},
f=varCorresp[[1,0]];
newCorresp=varCorresp;
If[f==x, newCorresp=varCorresp/.shiftRule];
VarShiftChange[{seq},x,shiftRule,Append[shiftedVars,newCorresp]]
] *)


ProperRecVars[{},n_,Vars_] :=
    Vars


ProperRecVars[{x_[y_]==rhs_,seq___},n_,Vars_]/;RecurrenceOrder[x[y]==rhs,n,x]<=0 :=
    ProperRecVars[{seq},n,Vars]


ProperRecVars[{x_[y_]==rhs_,seq___},n_,Vars_] :=
    Module[ {depVars,newVars},
        depVars = Union[Cases[{rhs},f_[n+i_.]->f,Infinity]];
        newVars = Union[Vars,depVars];
        ProperRecVars[{seq},n,newVars]
    ]


(* *********************************************************** *)
(* ************ Part III: Recurrence Solving Tools *********** *)
(* *********************************************************** *)


(* ***************************************************** *)
(* Returns the order of recurrence equation rec of f[n]. *)
(* ***************************************************** *)


RecurrenceOrder[rec_,n_,f_] :=
    Max[Cases[rec,f[n+j_.]->j,Infinity]]-Min[Cases[rec,f[n+j_.]->j,Infinity]]


(* ****************************************************************************************** *)
(* The rhs contains only x[n] where n is less then the order of the recurrence. ************* *)
(* Checks that recurrences are of type: x[n+recOrder]= F (x[n+recOrder-1],...,x[n+recOrder-1]) *)
(* Input: {expr}, n, x, recOrder, where x[n+_]==expr **************************************** *)
(* ****************************************************************************************** *)


RecOrderCheck[rhs_,n_,x_,recOrder_]/;Cases[rhs,x[n+recOrder+j_.]->j,Infinity]!= {} :=
    0


RecOrderCheck[rhs_,n_,x_,recOrder_] :=
    1


(* ***************************************************** *)
(* Checks the dependencies. *)
(* ***************************************************** *)


RecDependencyCheck[{x_[y_]==rhs_,seq__},n_,indep_,dep_] :=
    Module[ {depVarsX,indepList,depList,depTerm},
        depVarsX = Complement[Union[Cases[rhs,f_[n+j_.]->f,Infinity]],{x}];
        If[ depVarsX=={},
            (*independent*)
            indepList = Append[indep,x[y]==rhs];
            depList = dep,
            indepList = indep;
            depTerm = {{x[y]==rhs,depVarsX}};
            depList = Join[dep,depTerm]
        ];
        RecDependencyCheck[{seq},n,indepList,depList]
    ]


RecDependencyCheck[{x_[y_]==rhs_},n_,indep_,dep_] :=
    Module[ {depVarsX,indepList,depList,depTerm},
        depVarsX = Complement[Union[Cases[rhs,f_[n+j_.]->f,Infinity]],{x}];
        If[ depVarsX=={},
            (*independent*)
            indepList = Append[indep,x[y]==rhs];
            depList = dep,
            indepList = indep;
            depTerm = {{x[y]==rhs,depVarsX}};
            depList = Join[dep,depTerm]
        ];
        {indepList,depList}
    ]


RecDependencyCheck[{},n_,indep_,dep_] :=
    {indep,dep}


(* ************************************************************************** *)
(* Input: a recurrence equation  x[n+_]=rhs. *)
(* Output: closed form, if it is (equivalent to a) C-finite recurrence
        error message otherwise. ***************************************** *)
(* ************************************************************************** *)


LinRecCSolve[x_[y_]==rhs_,n_]/;FreeQ[rhs,x] :=
    Module[ {},
        Print["Illegal recurrence encountered: " <>ToString[x[y]==rhs]];
        {False,{},{},{}}
    ]


LinRecCSolve[x_[y_]==rhs_,n_] :=
    Module[ {cfinite,inHomPart,shift,newRec,newIniRules,expectedOrder,givenOrder,solSet,sol,solExponent},
        (* 1. Check C-finiteness of rhs. If it is, return its inhom.Par. *)
        newRec      = {};
        newIniRules = {};
        sol         = {};
        solExponent = {};
        solSet      = {};
        {cfinite,inHomPart} = CFiniteCheck[Expand[rhs],n,x];
        If[ Not[cfinite],
            PrintDebug["[LinRecCSolve] Not C-finite", x[y]==rhs],
            (* 2. it is CFinite ->  shift the inhomogenous part *)
            givenOrder    = RecurrenceOrder[x[y] == rhs,n,x];
            shift         = ShiftOrder[inHomPart,n];
            expectedOrder = givenOrder+shift;
            If[ shift == 0, (* inHomPart is 0 -> original rec is CFinite *)
                newRec = x[y]==rhs,
                (* make the recurrence CFinite *)
                {newRec,newIniRules} = InhomRecTransform[x[y]==rhs,n,expectedOrder]
            ];
            (* 3. solve newRec with newIniRules *)
            solSet      = SolveCFinRecurrence[{newRec,newIniRules},n];
            sol         = SolCFinConstruct[solSet,n];
            solExponent = UnsortedComplement[solSet[[2]],{1}];
        ];
        {cfinite,sol,solSet,solExponent}
    ]


UnsortedComplement[x_List,y__List] :=
    Replace[x,Dispatch[(#:>Sequence[])&/@Union[y]],1]


(* ***************************************************************************** *)
(* Check the C-finiteness of the rhs of recurrence of x[n] (i.e. x[n+_)=rhs).    *)
(* Returns {True,inHomPart}, if it is C-finite, and {False,inHomPart} otherwise. *)
(* ***************************************************************************** *)


(* special C-finite recs is geometric recs -> it is treated separetely *)


CFiniteCheck[x_[_],n_,x_] :=
    {True,0}


CFiniteCheck[c_*x_[_],n_,x_] :=
    If[ FreeQ[c,n],
        {True,0},
        {False,0}
    ]


CFiniteCheck[x_[_]*c_,n_,x_] :=
    If[ FreeQ[c,n],
        {True,0},
        {False,0}
    ]


(* not geometric type recs -> it is treated separetely*)


CFiniteCheck[rhs_,n_,x_] :=
    Module[ {xPositions,xTermPositions,xTerm,rhsPos,i,sw = 1,rhsInHom,inHomPart,cFinite,inHomCFinite},
        rhsInHom       = rhs;
        inHomPart      = rhs;
        xPositions     = Position[rhs,x[_]];
        xTermPositions = #[[1]]&/@xPositions;
        Do[
            rhsPos   = xTermPositions[[i]];
            xTerm    = rhs[[rhsPos]];
            rhsInHom = rhsInHom-xTerm;
            sw       = CheckTerm[xTerm,n,x];
            If[ sw==0,
                cFinite = False;
                Continue[]
            ],
            {i,1,Length[xTermPositions]}
        ];
        If[ sw==1,
            (* check C-finiteness of rhsInHom *)
            inHomCFinite = InhomCCheck[rhsInHom,n,1];
            If[ inHomCFinite ==1, 
                (* inHom part is C-finite *)
                cFinite   = True;
                inHomPart = Expand[Simplify[rhsInHom]],
                (* inHom part is not C-finite *)
                cFinite   = False;
                inHomPart = rhs
            ]
        ];
        {cFinite,inHomPart}
    ]


(* ************************************************************************************************* *)
(* Checks that terms over x[_] in the rhs of the recurrence of x are products of constants and x[_]. *)
(* Returns 1, if they are, and 0 otherwise. ******************************************************** *)
(* ************************************************************************************************* *)


CheckTerm[x_[_],n_,x_] :=
    1


CheckTerm[c_*x_[_],n_,x_]/;FreeQ[c,n] :=
    1


CheckTerm[x_[_]*c_,n_,x_]/;FreeQ[c,n] :=
    1


CheckTerm[expr_,n_,x_] :=
    0


(* ************************************************************************************************* *)
(* Checks the C-finiteness of the inhomogeneous part inHomPar of the recurrence 
x[n+r]=Subscript[a, r-1] x[n+r-1]+ ... + Subscript[a, 0] x[n])+ inHomPart *)
(* Returns 1, if it is, and 0 otherwise. ********************************************************** *)
(* ************************************************************************************************* *)


InhomCCheck[expr_,n_,inHom_]/;FreeQ[expr,n] :=
    inHom


InhomCCheck[n_,n_,inHom_] :=
    inHom


InhomCCheck[n_^k_Integer,n_,inHom_]/;k>0 :=
    inHom


InhomCCheck[Sum[expr_,{k_,_Integer,_}],n_,inHom_]/;FreeQ[expr,n] :=
    inHom


InhomCCheck[a_*b__,n_,inHom_] :=
    Module[ {inHomMod},
        inHomMod = InhomCCheck[a,n,inHom];
        InhomCCheck[Times[b],n,inHomMod]
    ]


InhomCCheck[a_+b__,n_,inHom_] :=
    Module[ {inHomMod},
        inHomMod = InhomCCheck[a,n,inHom];
        InhomCCheck[Plus[b],n,inHomMod]
    ]


InhomCCheck[a_^b_,n_,inHom_]/;(FreeQ[a,n]&& Exponent[Expand[b],n]==1) :=
    inHom


InhomCCheck[a_^k_Integer,n_,inHom_] :=
(* if FreeQ[a,n], then FreeQ[a^k,n], since k is integer. Check happens only if !FreeQ[a,n]. *)
    If[ !FreeQ[a,n]&&k<0,
        Print["Unable to verify c-finitenes of "<>ToString[a^k]];
        0,
        InhomCCheck[a,n,inHom]
    ];


InhomCCheck[a_,n_,inHom_] :=
    0


(* ******************************************************************* *)
(* Input: a C-finite expression like  n^d1*Subscript[\[Theta], 1]^n+ \[Ellipsis]+ n^ds*Subscript[\[Theta], s]^n   ************ *)
(* Output: the order of its shift operator, i.e. d1+...+ds+s ********* *)
(* For n^d1*Subscript[\[Theta], 1]^n+ \[Ellipsis]+ n^ds*Subscript[\[Theta], s]^n  the shift operator is:  (S-Subscript[\[Theta], 1])^(d1+1)+ \[Ellipsis]+ (S-Subscript[\[Theta], s])^ds *)
(* ******************************************************************* *)


(* it is not efficient *)


ShiftOrder[expr_,n_]/;FreeQ[expr,n] :=
    If[ Expand[expr]===0,
        0,
        1
    ]


ShiftOrder[n_,n_] :=
    2


ShiftOrder[n_^k_Integer,n_]/;k>0 :=
    1+k


ShiftOrder[expr_,n_]/;FreeQ[Cases[expr,_^e_->e,Infinity],n] :=
    1+Exponent[expr,n] 
(*expr is poly in n, has no exponentials in n*)


ShiftOrder[Sum[expr_,{k_,_Integer,_}],n_]/;FreeQ[expr,n] :=
    1+ShiftOrder[expr/.k->n,n]


ShiftOrder[a_*b__,n_] :=
    Max[1,ShiftOrder[a,n]]*ShiftOrder[Times[b],n]


ShiftOrder[a_+b__,n_] :=
    ShiftOrder[a,n]+ShiftOrder[Plus[b],n]


ShiftOrder[a_^b_,n_]/;FreeQ[a,n] :=
    1


ShiftOrder[a_^k_Integer,n_] :=
    Binomial[ShiftOrder[a,n]-1+k,k]


(* ****************************************************************************************************** *)
(* Input: an inhomogeneous linear recurrence with constant coefficients, with C-finite inhomogeneous part *)
(*        smth like  f[n+r]=Subscript[a, r-1]f[n+r-1]+ \[Ellipsis]+ Subscript[a, 0]f[n] +g (n), with g (n)!= 0 ******************************** *)
(* Output: shifted and equivalent C-finite recurrence, ************************************************** *)
(*        smth like f[n+w]=Subscript[a, w-1]f[n+w-1]+ \[Ellipsis]+ Subscript[a, 0]f[n]  ***************************************************** *)
(* newOrder in the input sequence is originalOrder+shiftOrder ******************************************* *)
(* ****************************************************************************************************** *)


Off[Solve::"svars"];


InhomRecTransform[f_[y_]==rhs_,recIndex_,newOrder_] :=
    Module[ {eval,eq,c,cf,originalOrder,n,val,pat,i,r,FTerm,FreeCoeff,FTermSys,sys = {},sol,newRec,j,iniVal,iniRHS,iniRel,newIniRules,newRecForm,coeffC,FCoefficient},
        r = newOrder;
        n = recIndex;
        eq = f[y]==rhs;
        originalOrder = RecurrenceOrder[eq,n,f];
        eval[j_] = Rule@@eq/.n->j;
        iniRel = Table[eval[j],{j,0,r-originalOrder-1}];
        iniRHS = #[[2]]&/@iniRel;
        iniVal = FixedPoint[#/.iniRel &,iniRHS,r-originalOrder];
        newIniRules = Table[Rule[iniRel[[i,1]],iniVal[[i]]],{i,1,Length[iniVal]}];
        (*NewRecForm*)
        newRecForm[n_] = f[n+r]-Sum[c[j]f[n+j],{j,0,r-1}];
        While[!FreeQ[newRecForm[n],c] ,
        (* in case the shiftOrder (and thus r) was bigger than it should have been, *) 
        (* r will be decreeased until all coefficients can be exactly determined. *)
        (* e.g. By ShiftOrder rules, the shift of -9*2^-n-2^-n*p[0]+2^-n is 2, although it should be 1. *)
        (* WHILE will only take max. 2 iteration. *)
        (*  If the shift order was exact, we get the closed form after 1 iteration.*)
        (*  If the shift order was NOT exact, after the 1st iteration the expected *)
        (*  recurrence order is decremented by the plus amount of the shift. *)
        (* The order gets exact, and closed form is derived. *)
            newRecForm[n_] = f[n+r]-Sum[c[j]f[n+j],{j,0,r-1}];
            coeffC = Table[c[j],{j,0,r-1}];
            sys = {};
            Do[
                (*the rules upto shifted order*)
                val = Table[eval[j],{j,i,i+r-1}];
                (*Apply recursively all rules on newRecForm *)
                          (* we thus get a relation in f[n+i], i=0,...,r-originalOrder+1*)
                cf = FixedPoint[#/.val &,newRecForm[i],r];
                FCoefficient = Table[Coefficient[cf,f[i+j]],{j,0,originalOrder-1}];
                FTerm = Sum[f[i+j-1]*FCoefficient[[j]],{j,1,Length[FCoefficient]}];
                FreeCoeff = Expand[cf-FTerm];
                FTermSys = #==0&/@FCoefficient;
                sys = Union[sys,Union[FTermSys,{FreeCoeff==0}]],
                {i,n,n+r-originalOrder-1}];
            sol = Simplify[Expand[Solve[sys,coeffC]]];
            newRecForm[n_] = f[n+r]-Sum[c[j]f[n+j],{j,0,r-1}]/.sol;
            r = r-Length[Union[Cases[{newRecForm[n]},c[_],Infinity]]]
             ];
        newRec = newRecForm[n][[1]]==0;
        {newRec,newIniRules}
    ]


(* **************************************************************** *)
(* Input:Something of the form {f[n+2]==f[n]+f[n+1]} ************** *)
(* Output: Something of the form {f,{a,b},{{c,d,..},{e,..}} 
representing the closed form f[n]==(c+d*n+..)*a^n+(e+..)*b^n. *)
(* **************************************************************** *)


SolveCFinRecurrence[{rec_,iniRules_},recVar_] :=
    Module[ {eq,charPoly,p,a,b,c,i,j,lambda,x,eval,ansatz,sys,sol,n,f},
        n = recVar;
        eq = rec;
        f = Union[Cases[rec,f_[n+i_.]->f,Infinity]][[1]];
        charPoly = eq/.a_==b_->a-b/.f[n+i_.]->lambda^i;
        p = charPoly//FactorList;(* gets the factors of charPoly with their multiplicity *)
        p = Rest[p]/.{a_,b_Integer}:>Table[{Hold[Root[x[a]/.lambda->#/.x->Function,i]]//ReleaseHold,b},{i,1,Exponent[a,lambda]}];
        p = Join@@p; (* list of factors with their multiplicity *)
        (*closed form shape, j-different factor count, i multiplicity count*)
        (*p[[j,1]] is the root j of the char poly, p[[j,2]] is the multiplicity of root j*)
        ansatz[n_] = Sum[c[i,j]n^i p[[j,1]]^n,{j,1,Length[p]},{i,0,p[[j,2]]-1}]; 
        (*sys=FixedPoint[Expand[#/.eval]&,Table[f[n]==ansatz[n],{n,0,RecurrenceOrder[eq,n,f]-1}]] ;*)
        sys = Table[f[n]==ansatz[n],{n,0,RecurrenceOrder[eq,n,f]-1}]; (* unknowns are the coefficients in the closed forms. They are determined using initial values*)
        sol = Solve[sys,Union[Cases[sys,c[__],Infinity]]];
        Return[ToRadicals[{f,First/@p,Table[c[i,j],{j,1,Length[p]},{i,0,p[[j,2]]-1}]/.First[sol]/.iniRules}]]
    ]


(* Input: Something of the form {f,{a,b},{{c,d,..},{e,..}} (i.e. from SolveCFinRecurrence) *)
(* Output: Closed form f[n]==(c+d*n+..)*a^n+(e+..)*b^n. *)


SolCFinConstruct[L_,n_] :=
    Module[ {f,factors,polyCoeff,eq,newRhs,simpleRhs,coeffFactorJ,j},
        f = L[[1]];
        factors = L[[2]];
        polyCoeff = L[[3]];
        newRhs = 0;
        Do[
        coeffFactorJ = Simplify[Sum[polyCoeff[[j,i]]*n^(i-1),{i,1,Length[polyCoeff[[j]]]}]];
        newRhs = newRhs+factors[[j]]^n *coeffFactorJ,
        {j,1,Length[factors]}];
        eq = f[n]== newRhs
    ]


Off[Zb::"badfac"]


Off[fastZeil`Zb::"badfac"]


Off[fastZeil`Zb::"intlin"]


HypergeometricQ[term_,n_] :=
    Catch[fastZeil`Private`ReleaseHold[Q[term,n]]]=!={};


GosperCheckAndSolve[rhs_,x_,n_] :=
    Module[ {gosperCF,k,gosperSolvable,GosperSum,rhsMod,expVars,gosperTerm,hyperCheck,solSet,expCoeff,i,j,expList,coeffList,freeCoeff},
        solSet    = {};
        GosperSum = {};
        rhsMod    = rhs/.n->k;
        expVars   = {};
        (* Print["Start HypergeometricQ."]; *)
        hyperCheck = HypergeometricQ[Simplify[rhs],n];
        (* Print["hyperCheck: ",hyperCheck]; *)
        If[ !hyperCheck,
            gosperSolvable = False,
            (* Print["Start Gosper."]; *)
            gosperCF = fastZeil`Gosper[rhsMod,{k,0,n-1}]/.$Failed->{};
            (* Print["gosperCF: ",gosperCF]; *)
            If[ (gosperCF=={}),
                gosperSolvable = False,
                gosperSolvable = True;
                gosperTerm     = Simplify[gosperCF[[1,2]]];
                GosperSum      = x[n] == x[0]+gosperTerm;
                expVars        = Union[Cases[{GosperSum},r_^(n+i_.)->r,Infinity],Cases[{GosperSum},r_^(c_*n+i_.)->r^c,Infinity]];
                expCoeff       = Coefficient[{gosperTerm},#^n]&/@expVars;
                freeCoeff      = Simplify[x[0]+gosperTerm-Sum[expCoeff[[i,j]]*expVars[[i]]^n,{i,1,Length[expCoeff]},{j,1,Length[expCoeff[[i]]]}]];
                coeffList      = Append[expCoeff,{freeCoeff}];
                expList        = Append[expVars,1];
                solSet         = {x,expList,coeffList}
            ]
        ];
        {gosperSolvable,GosperSum,solSet,expVars}
    ]

HyperSolve[x_[y_]==rhs_,n_] :=
    Module[ {eqn,hgTerms,solvable,recOrder,matrix,sval,coeff,cf,factorList,polyCoeff,expVars,expCoeff,factCoeff,solSet},
        eqn      = (x[y] == rhs) // PrintDebug["[HS] HyperSolve with"];
        eqn      = HomogeneousTransform[eqn,n] // PrintDebug["[HS] Homogeneous"];
        recOrder = RecurrenceOrder[eqn,n,x];
        hgTerms  = Hyper[eqn,x[n],Solutions->All] // PrintDebug["[HS] Solutions of Hyper"];
        hgTerms  = (ToHg[#,n]& /@ hgTerms) // PrintDebug["[HS] Solutions of ToHg"];
        If [hgTerms == {},
            solvable = False,
            solvable = True;
            matrix   = Table[hgTerms,{n,0,Length[hgTerms]-1}];
            sval     = Table[x[i],{i,0,Length[hgTerms]-1}];
            expCoeff = LinearSolve[matrix,sval];
            hgTerms  = FactorialSimplify[hgTerms] // PrintDebug["[HS] Simplified terms"];

            (* Shift closed form by recOrder-1 s.t. all closed forms correspond to the same loop iteration *)
            hgTerms = hgTerms /. n -> n+recOrder-1;

            cf       = (x[n] == hgTerms.expCoeff) // PrintDebug["[HS] Closed form"];

            expVars = Cases[#, (r_^(c_.*n + i_.)) -> r^c, {0, Infinity}, Heads -> True]& /@ hgTerms;
            expVars = (expVars /. {} -> {1} // Flatten) // PrintDebug["[HS] Exponential sequences"];

            expSeq = Cases[#, (r_^(c_.*n + i_.)) -> r^(c*n+i), {0, Infinity}, Heads -> True]& /@ hgTerms;
            expSeq = expSeq /. {} -> {1} // Flatten;

            factCoeff = hgTerms;
            If[expVars != {},
                expCoeff = expCoeff * expSeq / ((#^n)&/@expVars);
                factCoeff = hgTerms / expSeq;
            ];

            refFactList = FactorList[factCoeff[[1]]];
            refFactList = Cases[refFactList, {FactorialPower[n + b_.,_],k_} -> {b,k},Infinity];
            refFact     = Times @@ (FactorialPower[n+#[[1]],n]^#[[2]]& /@ refFactList);
            fact        = (FactorialSimplify[# / refFact]& /@ factCoeff) // PrintDebug["[HS] Reference factorial"];

            If[!FreeQ[fact,FactorialPower],
                solvable = False;
                PrintDebug["[HS] Recurrence not hypergeometric", hgTerms],
                expCoeff = expCoeff * fact
            ];

            solSet    = {x,expVars,List[#]&/@expCoeff,{{refFact}}} // PrintDebug["[HS] Solution set"]
        ];
        {solvable,cf,solSet,expVars}
    ]

(* Use higher weights for functions which should not appear in simplification. *)
FactorialSimplify[expr_] := 
    FullSimplify[expr,
        ComplexityFunction -> ((LeafCount@# + 1000 Count[#, _Gamma | _Pochhammer, {0, \[Infinity]}]
                                + 50 Count[#, _FactorialPower, {0, \[Infinity]}]) &)
    ];

ToHg[f_, n_] :=
    Module[{ff = Factor[f]},
        m1 = FactorTermsList[ff];
        ff = If[m1[[1]] == -1, ff * (-1), ff];
        ff = FactorList[ff];
        ff = ff /. {(a_. n + b_.),k_} -> {{a,k},{(n + b/a),k}};
        ff = Cases[ff, {c_, b_} /; Head[c] =!= List -> {c, b}, Infinity, Heads -> True];
        (* ff = If[Head[ff] === Times, List @@ ff, ff]; *)
        ff = Replace[ff, {(n + b_.),k_} -> {FactorialPower[n+b-1,n],k}, Infinity, Heads -> True];
        ff = Replace[#, {c_,e_} /; FreeQ[c, n] -> {c,e*n}]& /@ ff;
        ff = If[m1[[1]] == -1, Append[ff,(-1)^n], ff];
        ff = Times @@ (#[[1]]^#[[2]]& /@ ff);
        (* ff = a0 ff / (ff /. n -> n0); *)
        Return[ff]
    ];

HomogeneousTransform[x_[y_]==rhs_,n_] :=
    Module[{newRec,newIniRules,shift,givenOrder,expectedOrder},
        rec = x[y] == rhs;
        eqn = x[y] - rhs;
        recOrder = RecurrenceOrder[rec,n,x] // PrintDebug["[HomTransform] Rec order"];
        startIndex = Max[Cases[eqn,x[n+i_.] -> i]];
        homPart = 0;
        Do[
            coeff = Coefficient[eqn,x[n+i]];
            homPart = homPart + coeff * x[n+i],
            {i,startIndex-recOrder,startIndex}
        ];
        inhomPart = (eqn - homPart) // Simplify // PrintDebug["[HomTransform] Inhom part"];
        If[PossibleZeroQ[inhomPart],
            PrintDebug["[HomTransform] Rec is homogeneous",rec],
            res = homPart / inhomPart;
            res = (res /. n -> (n+1)) - res;
            index = Max @@ Cases[res,x[n+i_.] -> i,Infinity];
            coeff = Coefficient[res, x[n+index]];
            rec = x[n+index] == Simplify[-(res - coeff * x[n+index]) / coeff];
        ];
        rec
    ];

(* ********************************************************************************** *)
(* Input: system of recurrences {x[n+1]==x[n]+1, y[n+1]==y[n]+x[n]} ****************** *)
(* Checks dependencies among recurrences of the system. ***************************** *)
(* Solves recurrences, if they are solvable. **************************************** *)
(* Output: {closed_form _system, {exponential bases}} if the system is Psolvable *)
(*         and aborts computation otherwise.  *************************************** *)
(* ********************************************************************************** *)


RecSolve[recSystem_,varList_,{recVar_}] :=
    Module[ {indepList,depList,n,indepNr,depNr,cfRules,recsLeft,solvable,i,recEq,rhsEq,recOrder,cfinite,cfRec,exps,newRecSystem,cfSystem,expList,ruleX,rulesListX,expVars,expDepList,finVars,iniVarList,iniVarListCorresp,x,iniVarRules,cfSolSet,expBases},
        n            = recVar;
        newRecSystem = recSystem;
        cfSystem     = {};
        expList      = {};
        iniVarList   = {};
        cfRules      = {};
        recsLeft     = True;
        solvable     = True;
        finVars      = {};
        While[ solvable && recsLeft,
            (* Print["Start RecDependency Check."]; *)
            {indepList,depList} = RecDependencyCheck[newRecSystem,n,{},{}];
            indepNr             = Length[indepList];
            depNr               = Length[depList];
            If[ indepNr == 0 && depNr != 0,
                Print["Illegal coupling detected in loop body - cannot determine P-solvability!"];
                solvable = False;
                cfSystem = {};
                expList  = {};
                Continue[]
            ];
            If[ indepNr == 0 && depNr == 0,
                recsLeft = False;
                Continue[]
            ];
            (* there are still independent recs *)
            Do[
                recEq = indepList[[i]];
                rhsEq = recEq[[2]];
                x     = Union[Cases[recEq,f_[n+j_.]->f,Infinity]][[1]];
                (* RecType Check *)
                (* Print["Start EqRecSolve for ", recEq," with recurrence index: ",n]; *)
                {solvable,cfRec,cfSolSet,exps} = EqRecSolve[recEq,n];
                (* Print["exps: ", exps]; Print["solvable: ",solvable ]; Print["cfRec: ",cfRec ]; Print["cfSolSet: ",cfSolSet ]; *)
                expList = Join[expList,exps];
                If[ Not[solvable],
                    (* TODO Why continue if a recurrence is not solvable? *)
                    cfSystem = {};
                    expList  = {};
                    Continue[],
                    (* it is a solvable recs *)
                    cfSystem     = Join[cfSystem,{{cfRec,cfSolSet,exps}}];
                    ruleX        = Apply[Rule,cfRec];
                    newRecSystem = Complement[newRecSystem,{recEq}];    
                    rulesListX   = CFRulesList[newRecSystem,n,ruleX,x];
                    cfRules      = Join[cfRules,rulesListX];
                    newRecSystem = newRecSystem/.cfRules
                ],
                {i,1,indepNr}
            ]
        ];
        (* Print["Finished computing closed forms."]; *)
        newRecSystem = {};
        expVars      = {};
        expDepList   = {};
        expBases     = {};
        If[ Not[solvable],
            Print["Not P-solvable loop!"];
            Abort[]
        ];
        (* recurrences are solvable, what about P-solvable loop? *)
        (* Print["Start PSolvability Check for ", cfSystem, " with recIndex: ", n]; *)
        {newRecSystem,expVars,expBases,expDepList,auxVars} = CleanPSolvableCheck[cfSystem,n];
        (* Print["newRecSystem: ",newRecSystem];Print["expVars: ",expVars];Print["expBases: ",expBases];Print["expDepList: ",expDepList]; *)
        iniVarListCorresp      = varList/.n->0;
        iniVarList             = Table[iniVarListCorresp[[i,1]],{i,1,Length[iniVarListCorresp]}];
        (* TODO check if SeqToVars is still necessary *)
        {newRecSystem,finVars} = SeqToVars[newRecSystem,varList,expVars,expBases,n];
        iniVarRules            = IniValuesAndVarRules[finVars,iniVarList];
        {newRecSystem/.iniVarRules,{n},expVars,finVars,iniVarList/.iniVarRules,expDepList,auxVars}
    ]


CFRulesList[sys_,n_,ruleX_,x_] :=
    Module[ {xSeq,xSeqShift,xSeqRules,xRulesList,i,cfXSeq},
        xSeq = Union[Cases[sys,x[n+i_.]->i,Infinity]];
        cfXSeq = Cases[ruleX,x[n+i_.]->i,Infinity][[1]];
        xSeqShift = n+#-cfXSeq&/@xSeq;
        xSeqRules = Rule[n,#]&/@xSeqShift;
        xRulesList = ruleX/.#&/@xSeqRules;
        xRulesList
    ]


PSolvableCheck[sys_,n_] :=
    Module[ {x,y,recEq,expVars,newRecSystem,newRecEq,k,i,j,expBases,expCoeffList,Psolvable,polyCoeff,freeCoeff,cfSystem,expSeq,expDepList,solSet,coeffList,coeffTerm,expSeqBases},
        cfSystem     = sys;
        expDepList   = {};
        newRecSystem = {};
        expVars      = {};
        expBases     = {};
        (* Check: polynomial cfSystem - linear combination of exponentials and polys in n*)
        Do[
            recEq        = cfSystem[[i,1]];
            solSet       = cfSystem[[i,2]];
            expCoeffList = Flatten[solSet[[3]]];
            expBases     = cfSystem[[i,3]];
            polyCoeff    = Apply[And,Table[PolynomialQ[expCoeffList[[j]],n],{j,1,Length[expCoeffList]}]];
            (* expCoeffList = Coefficient[recEq[[2]],#^n&/@expBases]; *)
            If[ Not[polyCoeff],
                Print["Not P-solvable loop! Not polynomial closed forms!"];
                Abort[]
            ],
            {i,1,Length[cfSystem]}
        ];
        (*check algebraic dependencies*)
        expBases    = Apply[Join,Table[cfSystem[[i,3]],{i,1,Length[cfSystem]}]];
        expSeq      = #^n&/@expBases;
        expSeqBases = expBases;
        If[ expBases == {},(*Psolvable*)
            newRecSystem = Table[cfSystem[[i,1]],{i,1,Length[cfSystem]}],
            (* ELSE: there are exponential sequences -> get Dependencies *)
            y = Unique[];
            expDepList =(*Dependencies`Private`*) Dependencies[expSeq,y,Variables->{n}];
            If[ expDepList=={}, 
                (* no alg. dep -> not Psolvable *)
                Print["Not P-solvable loop! No algebraic dependencies among exponentials!"];
                Abort[],
                (*Psolvable*)
                expVars    = Table[y[i],{i,1,Length[expSeq]}];
                expDepList = Equal[#,0]&/@expDepList;
                (* rewrite exponentials in cfSystem by the new variables *)
                k = 0;
                (* counter of the nr. of vars stnading for exponential seq, i.e. max value is Length[expSeq]*)
                Do[
                    recEq     = cfSystem[[i,1]];
                    solSet    = cfSystem[[i,2]];
                    expBases  = cfSystem[[i,3]];
                    coeffTerm = 0;
                    If[ expBases == {},
                        newRecEq = recEq,
                        (* otherwise, it has exponentials *)
                        Do[
                            coeffList = solSet[[3,j]];
                            If[ solSet[[2,j]]==1,
                                coeffTerm = coeffTerm+Simplify[Sum[coeffList[[u]]*n^(u-1),{u,1,Length[coeffList]}]],
                                k = k+1;
                                coeffTerm = coeffTerm+Simplify[Sum[coeffList[[u]]*n^(u-1),{u,1,Length[coeffList]}]]*y[k]
                            ],
                            {j,1,Length[solSet[[2]]]}
                        ];
                        newRecEq = recEq[[1]]==coeffTerm
                    ];
                    newRecSystem = Append[newRecSystem,newRecEq],
                    {i,1,Length[cfSystem]}
                ]
            ]
        ];
        {newRecSystem,expVars,expSeqBases,expDepList}
    ];


(* EXPERIMENTAL. Try to get a cleaner PSolvableCheck *)
CleanPSolvableCheck[sys_,n_] :=
    Module[ {x,y,recEq,expVars,newRecSystem,newRecEq,k,i,j,expBases,expCoeffList,Psolvable,polyCoeff,freeCoeff,cfSystem,expSeq,expDepList,solSet,coeffList,coeffTerm,expSeqBases,f},
        cfSystem     = sys;
        expDepList   = {};
        newRecSystem = {};
        expVars      = {};
        expBases     = {};
        auxVars      = {};
        PrintDebug["[PSolvableCheck] Closed form system",cfSystem[[All,1]]];
        (* Check: polynomial cfSystem - linear combination of exponentials and polys in n*)
        Do[
            recEq        = cfSystem[[i,1]];
            solSet       = cfSystem[[i,2]];
            expCoeffList = Flatten[solSet[[3]]];
            expBases     = cfSystem[[i,3]];
            polyCoeff    = Apply[And,Table[PolynomialQ[expCoeffList[[j]],n],{j,1,Length[expCoeffList]}]];
            (* expCoeffList = Coefficient[recEq[[2]],#^n&/@expBases]; *)
            If[ Not[polyCoeff],
                Print["Not P-solvable loop! Not polynomial closed forms!"];
                Abort[]
            ],
            {i,1,Length[cfSystem]}
        ];
        (*check algebraic dependencies*)
        expBases    = DeleteCases[Join @@ Table[cfSystem[[i,3]],{i,1,Length[cfSystem]}], 1];
        expSeq      = (#^n&/@expBases) // PrintDebug["[PSolvableCheck] Exponential sequences"];
        expSeqBases = expBases;
        If[ expBases == {},(*Psolvable*)
            newRecSystem = Table[cfSystem[[i,1]],{i,1,Length[cfSystem]}],
            (* ELSE: there are exponential sequences -> get Dependencies *)
            y = Unique[];
            expDepList = Dependencies[expSeq,y,Variables->{n}] // PrintDebug["[PSolvableCheck] Dependencies among exp seq"];
            If[ expDepList=={}, 
                (* no alg. dep -> not Psolvable *)
                Print["Not P-solvable loop! No algebraic dependencies among exponentials!"];
                Abort[],
                (*Psolvable*)
                expVars    = Table[y[i],{i,1,Length[expSeq]}] // PrintDebug["[PSolvableCheck] Exponential variables"];
                expDepList = Equal[#,0]&/@expDepList;
                {cfSystem[[All,2]],factIndices} = CanonicalSystem[cfSystem[[All,2]],n];
                factVarRules = (FactorialPower[n + #,n] -> Unique[])& /@ factIndices;
                PrintDebug["[PSolvableCheck] Factorial rewrite rules", factVarRules];
                auxVars = Union[auxVars,Values[factVarRules]];
                (* rewrite exponentials in cfSystem by the new variables *)
                k = 0;
                (* counter of the nr. of vars stnading for exponential seq, i.e. max value is Length[expSeq]*)
                Do[
                    recEq  = cfSystem[[i,1]];
                    solSet = cfSystem[[i,2]];

                    recurrence = solSet[[2;;]];
                    recurrence[[1]] = Replace[recurrence[[1]], x_?(# != 1&) :> y[++k],{1}];
                    recurrence[[1]] = Replace[recurrence[[1]],{} -> {{1}}];

                    var = If[solSet[[2]] == {},
                            {1},
                            Table[y[k+i],{i,1,Length[solSet[[2]]]}]
                          ];
                    factVars = Table[f[i],{i,1,Length[solSet]-3}];
                    rec = Flatten[Dot @@ recurrence][[1]];

                    newRecSystem = Append[newRecSystem,recEq[[1]] == rec],
                    {i,1,Length[cfSystem]}
                ];
                newRecSystem = newRecSystem/.factVarRules
            ]
        ];
        PrintDebug["[PSolvableCheck] Return", newRecSystem];
        {newRecSystem,expVars,expSeqBases,expDepList,auxVars}
    ];

IntegerDistance[set_] :=
    Module[{indices,remaining},
        indices = set;
        remaining = {};
        While[indices != {},
            remaining = Append[remaining,indices[[1]]];
            indices = DeleteCases[indices[[2;;]],t_ /; Mod[(t-indices[[1]]),1] == 0];
        ];
        remaining
    ];

FPower[n_,index_,exp_] := FactorialPower[n + index,n]^exp;

CanonicalSystem[solSets_,n_] :=
    Module[{sets,indices,refFact,fact,index,tmp,i,j,k},
        sets = solSets;
        indices = IntegerDistance @ Sort @ Cases[sets,FactorialPower[n+i_.,n]->i,Infinity,Heads->True];
        Do[
            If[Length[sets[[i]]] < 4, Continue[]];
            Do[
                fact     = sets[[i,j]][[1,1]] // PrintDebug["[CS] Factorials"];
                factList = Cases[FactorList[fact],{FactorialPower[n+j_.,n],k_}->{j,k}];

                refFact  = 1;
                expCoeff = 1;
                Do[
                    {index,exp} = f;
                    If[MemberQ[indices,index],
                        refFact  = refFact * FPower[n,index,exp],
                        refIndex = Cases[indices,t_ /; Mod[(t-index),1] == 0][[1]];
                        refFact  = (refFact * FPower[n,refIndex,exp]); 
                        expCoeff = expCoeff * FactorialSimplify[FPower[n,index,exp] / FPower[n,refIndex,exp]];
                    ],
                    {f,factList}
                ];
                sets[[i,3]] = sets[[i,3]] * expCoeff;
                sets[[i,j]] = {{refFact}},
                {j,4,Length[sets[[i]]]}
            ],
            {i,1,Length[sets]}
        ];
        {sets,indices}
    ];

SeqToVars[sys_,varList_,expVars_,expBases_,n_] :=
    Module[ {i,newRecSystem,varCorresp,x,cfRecIndex,seqVal,recEqX,shift,finVars,newEq,expVarRules,j},
        newRecSystem = {};
        finVars      = {};
        Do[
            varCorresp   = varList[[i]];
            x            = varCorresp[[1,0]];
            seqVal       = varCorresp[[1,1]];
            recEqX       = Cases[{sys},x[_] == _,Infinity];
            cfRecIndex   = recEqX[[1,1,1]];
            shift        = seqVal-cfRecIndex;
            expVarRules  = Table[expVars[[j]]->expBases[[j]]^shift*expVars[[j]],{j,1,Length[expVars]}];
            newEq        = ((recEqX/.n->n+shift)/.expVarRules)/.Apply[Rule,varCorresp];
            finVars      = Append[finVars,varCorresp[[2]]];
            newRecSystem = Join[newRecSystem,newEq],
            {i,1,Length[varList]}
        ];
        {newRecSystem,finVars}
    ]


(* ******************************************************************************************** *)
(* Input: smth of the form x[n+1]==x[n]+1 ***************************************************** *)
(* Checks the type of a a given recurrence. Solves it by Gosper or C-finite. ****************** *)
(* if it is not Gosper, nor C-finite, then it returns {False,{},{}}. ************************** *)
(* Otherwise, if it is solvable (for Gosper), it returns {True, closedForm,{exponential bases}} *)
(* if it is not solvable, returns {False, {},{}}. ********************************************* *)
(* ******************************************************************************************** *)


EqRecSolve[x_[y_]==rhs_,n_] :=
    Module[ {recOrder,recEq,cfRec,exps,solvable,gosperCoeff,rhsTerm,needShift,rhsEq,recEqSolved,solSet},
        (* Print["In EqRecSolve with ", recEq]; *)
        recEq     = x[y] == rhs;
        solvable  = False;
        recOrder  = RecurrenceOrder[recEq,n,x];
        needShift = y-(n+recOrder);
        (* shift it to its order first, if needed. E.g. x[n+2]==x[n+1]+1 should be solved as x[n+1]==x[n]+1 *)
        cfRec       = {};
        solSet      = {};
        exps        = {};
        rhsEq       = rhs/.n->n-needShift;
        recEqSolved = recEq/.n->n-needShift;
        (* Print["recOrder: ",recOrder]; *)
        If[recOrder < 1,
            Print["[Not supported] recurrence order is < 1 in ",recEq];
            solvable = False,
            (* Try C-finite *)
            {solvable,cfRec,solSet,exps} = LinRecCSolve[recEqSolved,n];
            If[Not[solvable] && recOrder == 1,
                (* Try Gosper *)
                gosperCoeff = Coefficient[rhsEq,x[n]];
                If[NumberQ[gosperCoeff] &&  gosperCoeff == 1,
                    rhsTerm = rhsEq-x[n];        
                    {solvable,cfRec,solSet,exps} = GosperCheckAndSolve[rhsTerm,x,n];
                ];
            ];
            If[Not[solvable],
                (* Try hypergeometric *)
                {solvable,cfRec,solSet,exps} = HyperSolve[recEqSolved,n];
            ];
        ];
        If[solvable,
            (* TODO Is this needed anymore? *)
            {cfRec,solSet} = {ShiftBackClosedForm[cfRec,n,needShift],ShiftBackSolSet[solSet,n,needShift]}
        ];
        (* Which[
            recOrder < 1,
                
            recOrder > 1, 
                (* Print["start LinRecCSolve."]; *)
                {solvable,cfRec,solSet,exps} = LinRecCSolve[recEqSolved,n];
                Print[solvable];
                If[ solvable,
                    {cfRec,solSet} = {ShiftBackClosedForm[cfRec,n,needShift],ShiftBackSolSet[solSet,n,needShift]}
                ],
            recOrder == 1, 
                gosperCoeff = Coefficient[rhsEq,x[n]];
                (* first Try CFinite, if it does not work, try zb *)
                (* If[Not[solvable] ||Not[NumberQ[gosperCoeff] && (gosperCoeff==1)],  *)
                (* try Cfinite *)
                {solvable,cfRec,solSet,exps} = LinRecCSolve[recEqSolved,n];
                (* Print["solvable as CFinite: ",solvable];*)
                If[ Not[solvable] && NumberQ[gosperCoeff] && (gosperCoeff==1),
                    (* might be Gosper-solvable *)
                    rhsTerm = rhsEq-x[n];        
                    (*Print["Start GosperCheckAndSolve."];*)
                    {solvable,cfRec,solSet,exps} = GosperCheckAndSolve[rhsTerm,x,n];
                    Print["solvable as Gosper: ", solvable];
                ];
                (* make the shift back in the cfRec: x[n]=rhs+x[0] should be x[n+needShift]=rhs+x[0+needShift] *)
                If[ solvable,
                    {cfRec,solSet} = {ShiftBackClosedForm[cfRec,n,needShift],ShiftBackSolSet[solSet,n,needShift]}
                ]
        ]; *)
        {solvable,cfRec,solSet,exps}
    ]


(* If there is a mismatch between the recurrence and loop index, i.e. x[n+2]==x[n+1]+2, mismatch is needshift=1 ->  *)
(* recurrence index of the sequence whose closed form was computed is shifted to the loop index. ***************** *)
(* make the shift back in the cfRec: x[n]=rhs+x[0] should be x[n+needShift]=rhs+x[0+needShift]. ****************** *)


ShiftBackClosedForm[x_[y_]==rhs_,n_,shiftValue_] :=
    Module[ {recIndex,iniValIndexes,rhsMod,iniValShiftRules,i},
        recIndex = y/.(n->n+shiftValue);
        iniValIndexes = Cases[{rhs},x[i_Integer]->i,Infinity];
        iniValShiftRules = (x[#]->x[#+shiftValue])&/@iniValIndexes;
        rhsMod = rhs/.iniValShiftRules;
        x[recIndex] == rhsMod
    ]


ShiftBackSolSet[system__,n_,shiftValue_] :=
    Module[ {recIndex,iniValIndexes,rhsMod,iniValShiftRules,i},
        iniValIndexes = Cases[system,x[i_Integer]->i,Infinity];
        iniValShiftRules = (x[#]->x[#+shiftValue])&/@iniValIndexes;
        system/.iniValShiftRules
    ]


(* ************************************************************************* *)
(* Computes the invariants for a loop with assignments only **************** *)
(* Input: smth of the form Body[S1], where S1 is a sequence of assignments.  *)
(* Output: Polynomial invariants ******************************************* *)
(* ************************************************************************* *)


InvLoopAssg[loop_] :=
    Module[ {recSystem,VarList,CFSystem,recVar,expVars,finVars,iniVars,AlgDep,elimVars,polySystem,invariants},
        {recSystem,VarList,recVar}                       = FromLoopToRecs[loop];
        {CFSystem,recVar,expVars,finVars,iniVars,AlgDep,auxVars} = RecSolve[recSystem,VarList,recVar];
        (* Print["P-solvable Loop!"]; *)
        elimVars   = Union[recVar,expVars,auxVars] // PrintDebug["Elim variables"];
        polySystem = Union[AlgDep,CFSystem] // PrintDebug["System of polynomials"];
        invariants = GroebnerBasis[polySystem,finVars,elimVars];
        Print["Method is complete!"];
        Simplify[invariants]
    ]


(* ******************************************************************************************** *)
(* Computes the invariants for a loop with nested conditionals ******************************** *)
(* Input: smth of the form {Body[S1],...,Body[Sk]}, where S1,...,Sk are the inner loop bodies. *)
(* Output: Polynomial invariants ************************************************************** *)
(* ******************************************************************************************** *)


InvLoopCond[loopList_] :=
    Module[ {closedFormsList,innerLoopPerm,allLoopVars,innerLoop,innerLoopRules,innerFinVars,t = Unique[],perm,invIdeal = {},i,permIdeal = {},sumIntersectionIdeal = {},appendableCF,appendablePerms},
(*Print["Start CfIFLoopSeq."];*)
        {closedFormsList,allLoopVars} = CfIfLoopSeq[loopList,{},{}];
        (* make common variables *)
        (*Print["Start UniformInnerLoopVars."];*)
        closedFormsList = UniformInnerLoopVars[closedFormsList,allLoopVars,{}];
        innerLoopPerm = Permutations[closedFormsList];
        (* intersection ideal of  all permutation *)
        (* first is the identity permutation *)
        perm = innerLoopPerm[[1]];
        (*Print["Start InvIdealLoopSeq."];*)
        invIdeal = InvIdealLoopSeq[perm];
        (* compute the invariant ideals of the rest of permutations; take intersection*)
        Do[
        perm = innerLoopPerm[[i]];
        permIdeal = InvIdealLoopSeq[perm];
        sumIntersectionIdeal = Union[t*invIdeal,(1-t)*permIdeal];
        invIdeal = GroebnerBasis[sumIntersectionIdeal,allLoopVars,{t}],
        {i,2,Length[innerLoopPerm]}
        ];
        (* do the filtering on the candidate polys from invIdeal *)
         (*Print["Candidate Polynomial Invariants: ",invIdeal]; *)
        (*Print["Start InnerLoopRewwriteRules."];*)
        innerLoopRules = InnerLoopRewwriteRules[loopList,{}];
        (*Print["Start InvariantFilter."];*)
        invariants = InvariantFilter[invIdeal,innerLoopRules,allLoopVars];
        If[ (Complement[invIdeal,invariants]=={}) && (Complement[invariants,invIdeal]=={}),
            Print["Method is complete!"],
            {appendableCF,allLoopVars} = CfIfLoopSeq[loopList,{},{}];
            appendableCF = UniformInnerLoopVars[appendableCF,allLoopVars,{}];
            CompletenessCheck[innerLoopPerm,closedFormsList,invariants,appendableCF,invIdeal,allLoopVars]
        ];
        Simplify[invariants]
    ]


(* *********************************************************************************************** *)
(* Introduces, if necessary, missing outer loop variables in the set of inner loop variables. **** *)
(* For each missing outer loop variable x, the introduced recurrence in the inner loop is x==x[0]. *)
(* *********************************************************************************************** *)


UniformInnerLoopVars[{},outerVars_,newClosedFormList_] :=
    newClosedFormList


UniformInnerLoopVars[{cf_,seq___},outerVars_,newClosedFormList_] :=
    Module[ {innerCF,innerRecVar,innerExps,innerFinVars,innerIniVars,innerAlgDep,missingVars,changedCForm,missingRules},
        {innerCF,innerRecVar,innerExps,innerFinVars,innerIniVars,innerAlgDep} = {cf[[1]],cf[[2]],cf[[3]],cf[[4]],cf[[5]],cf[[6]]};
        missingVars = Complement[outerVars,innerFinVars];
        If[ missingVars!= {},
            missingRules = Rule[#,#[0]]&/@missingVars; 
            (* i.e. x is a loop variable that is not changed in the inner loop. *)
            (* If x appears in the RHS of the closed forms of the inner loops, it should be x[0]*)
            innerCF = innerCF/.missingRules;
            innerCF = Union[innerCF,#==#[0]&/@missingVars];
            innerFinVars = Union[innerFinVars,missingVars];
            innerIniVars = Union[innerIniVars,#[0]&/@missingVars]
        ];
        changedCForm = {innerCF,innerRecVar,innerExps,innerFinVars,innerIniVars,innerAlgDep};
        UniformInnerLoopVars[{seq},outerVars,Append[newClosedFormList,changedCForm]]
    ]


(* *************************************************************************** *)
(* Computes the closed forms for a system of loops *************************** *)
(* Each inner loop's closed form is computed using RecSystem and RecSolve.    *)
(* Returns the list of closed forms of inner loops (list of RecSolve outputs). *)
(* It aborts computation, if one loop is not P-solvable ********************** *)
(* *************************************************************************** *)


CfIfLoopSeq[{innerLoop_,innerLoopList___},cfSystemList_,outerLoopVars_] :=
    Module[ {recSystem,VarList,CFSystem,recVar,expVars,finVars,iniVars,AlgDep,newCFSystem,innerCfSytem},
(*Print["Start FromLoopToRecs."];*)
        {recSystem,VarList,recVar} = FromLoopToRecs[innerLoop];
       (*Print["recSystem: ",recSystem];Print["VarList: ",VarList];Print["recVar: ",recVar];Print["Start RecSolve."];*)
        {CFSystem,recVar,expVars,finVars,iniVars,AlgDep} = RecSolve[recSystem,VarList,recVar];
        innerCfSytem = {CFSystem,recVar,expVars,finVars,iniVars,AlgDep};
        newCFSytem = Append[cfSystemList,innerCfSytem];
        CfIfLoopSeq[{innerLoopList},newCFSytem,Union[outerLoopVars,finVars]]
    ]


CfIfLoopSeq[{},cfSystemList_,outerLoopVars_] :=
    {cfSystemList,outerLoopVars}


(* *************************************************************************** *)
(* Merging closed form systems of inner loops (for one permutation) ********** *)
(* *************************************************************************** *)


CFMerge[{},mergedSys_] :=
    mergedSys


CFMerge[{seq___,cf_},{{},{},{},{},{},{}}] :=
    CFMerge[{seq},cf]


CFMerge[{seq___,cf_},mergedSys_] :=
    Module[ {cfSystem1,recVar1,expVar1,finVar1,iniVar1,algDep1,cfSystem2,recVar2,expVar2,finVar2,iniVar2,algDep2,
    mergedCF,recVars,expVars,finVars,iniVars,algDeps,i,cfRules1,iniRules,mergingRules,newMergedSys,lhsIniRules,rhsIniRulesChanges},
        {cfSystem1,recVar1,expVar1,finVar1,iniVar1,algDep1} = {cf[[1]],cf[[2]],cf[[3]],cf[[4]],cf[[5]],cf[[6]]};
        {cfSystem2,recVar2,expVar2,finVar2,iniVar2,algDep2} = {mergedSys[[1]],mergedSys[[2]],mergedSys[[3]],mergedSys[[4]],mergedSys[[5]],mergedSys[[6]]};
        recVars = Union[recVar1,recVar2];
        finVars = finVar1;
        iniVars = iniVar1;
        expVars = Union[expVar1,expVar2];
        algDeps = Union[algDep1,algDep2];
        iniRules = Table[iniVar2[[i]]->finVar2[[i]],{i,1,Length[finVar2]}];
        cfRules1 = Apply[Rule,cfSystem1,{1}];
        rhsIniRulesChanges = (#[[2]]&/@iniRules)/.cfRules1;
        lhsIniRules = (#[[1]]&/@iniRules);
        mergingRules = Table[lhsIniRules[[i]]->rhsIniRulesChanges[[i]],{i,1,Length[rhsIniRulesChanges]}];
        mergedCF = cfSystem2/.mergingRules;
        newMergedSys = {mergedCF,recVars,expVars,finVars,iniVars,algDeps};
        CFMerge[{seq},newMergedSys]
    ]


InvIdealLoopSeq[permSeq_] :=
    Module[ {elimVars,polySys,mergedCF,recVars,expVars,finVars,iniVars, algDeps,invariants},
        {mergedCF,recVars,expVars,finVars,iniVars, algDeps} = CFMerge[permSeq,{{},{},{},{},{},{}}];
        elimVars = Union[recVars,expVars];
        polySys = Union[mergedCF,algDeps];
        invariants = GroebnerBasis[polySys,finVars,elimVars]
    ]


CompletenessCheck[permList_,closedFormsOfPerm_,filteredPolys_,appendableClosedForms_,firstItIdeal_,allLoopVars_] :=
    Module[ {secondIterationList = {},i,perm,loopsToAppend,newLoopSeq,invIdeal,permIdeal,sumIntersectionIdeal,t,posLast,checkIdeal,reductionResult},
        Do[
        perm = permList[[i]];
        (*each permutation, e.g. S1...Sk, construct S1...Sk Sj, j!=k*)
        posLast = Flatten[Position[closedFormsOfPerm,Last[perm]]][[1]];
        loopsToAppend = Delete[appendableClosedForms,posLast];
        newLoopSeq = Append[perm,#]&/@loopsToAppend;
        secondIterationList = Join[secondIterationList,newLoopSeq]
        ,{i,1,Length[permList]}
        ];
        invIdeal = firstItIdeal;
        (* compute the invariant ideals of the rest of permutations; take intersection*)
        Do[
        perm = secondIterationList[[i]];
        permIdeal = InvIdealLoopSeq[perm];
        sumIntersectionIdeal = Union[t*invIdeal,(1-t)*permIdeal];
        invIdeal = GroebnerBasis[sumIntersectionIdeal,allLoopVars,{t}],
        {i,1,Length[secondIterationList]}
        ];
        (* ideal equality check invIdeal==filteredPolys *)
        (*checkIdeal=GroebnerBasis[Union[filteredPolys,invIdeal],allLoopVars];*)
        reductionResult = Union[#[[2]]&/@Table[PolynomialReduce[invIdeal[[i]],filteredPolys],{i,1,Length[invIdeal]}]];
        (*If[(Complement[checkIdeal,filteredPolys]=={}) || (Complement[checkIdeal,invIdeal]=={}),*)
        If[ (filteredPolys=={} && invIdeal=={})
        ||
        ((Length[filteredPolys]==Length[invIdeal]) &&  (Length[reductionResult]==1) && (NumberQ[reductionResult[[1]]]) && (reductionResult[[1]]==0)),
            Print["Method is complete!"],(* after filtering + additional iteration!"],*)
            Print["Cannot determine completeness of the method!"]
        ]
    ]


InvariantFilter[candidateInvPolys_,rewriteRulesInnerLoops_,finVars_] :=
    Module[ {candidates,dependencyPolys,iniVars,renameIniVars,backToIniValsRules,renamedCandidates},
        iniVars = #[0]&/@finVars;
        (* rename iniVars, e.g. a[0] is a a fresh new var. Get a renameIniVars list e.g. {a[0]->$7,b[0]->$8,d[0]->$9,y[0]->$10} *)
        renameIniVars = Rule[#,Unique[]]&/@iniVars;
        (* the rules to get back to original iniVars, e.g.  {$7->a[0],$8->b[0],$9->d[0],$10->y[0]} *)
        backToIniValsRules = Reverse[#]&/@renameIniVars;
        renamedCandidates = candidateInvPolys/.renameIniVars;
        {candidates,dependencyPolys} = CheckInvariant[renamedCandidates,rewriteRulesInnerLoops];
        While[ Complement[dependencyPolys,candidates]!={},
        (* repeat it again the same procedure *)
        {candidates,dependencyPolys} = CheckInvariant[candidates,rewriteRulesInnerLoops]
        ];
        candidates/.backToIniValsRules
    ]


(* wp of polys are in the ideal generated by the polys? Returns the polys whose wp reduces to 0 w.r.t. the polys,
and returns also the set of polys used in the reductuon phase. *)


CheckInvariant[candidates_,rewriteRulesInnerLoops_] :=
    Module[ {dedependencyPolys,newCandidates,wpList,
    reductionList,depList,i,j,wpListPolyI,freeCoeffs,reductionPolysPos},
        dependencyPolys = {};
        newCandidates = candidates;
        wpList = WPPolySet[rewriteRulesInnerLoops,candidates,{}];
        (* Note: Length[candidates]=Length[wpList] *)
        Do[
            wpListPolyI = wpList[[i]];
            reductionList = Table[PolynomialReduce[wpListPolyI[[j]],candidates],{j,1,Length[wpListPolyI]}];
            freeCoeffs = Union[#[[2]]&/@reductionList];
            If[ Length[freeCoeffs]==1 && NumberQ[freeCoeffs[[1]]] && freeCoeffs[[1]]== 0,   
           (* wps of polyI are in the ideal generated by  candidates*)
                reductionPolysPos = #[[2]]&/@reductionList;
                depList = #[[1]]&/@reductionList;
                dependencyPolys = Union[dependencyPolys,PolyDependencyCheck[depList,candidates,{}]],
          (* wps of polyI are NOT in the ideal generated by  candidateInvPolys*)
                newCandidates = Complement[newCandidates,{candidates[[i]]}]
            ],
              {i,1,Length[candidates]}
        ];
        {newCandidates,dependencyPolys}
    ]


(*{{1,0},{2,2}} -> poly1, poly1,poly2 are used in reduction*)


PolyDependencyCheck[{},candidatePolyList_,depPolyList_] :=
    depPolyList


PolyDependencyCheck[{reduction_,seq___},candidatePolyList_,depPolyList_] :=
    Module[ {depModList,i},
        depModList = depPolyList;
        Do[
        If[ !(NumberQ[reduction[[i]]] && reduction[[i]]==0),
            depModList = Union[depModList,{candidatePolyList[[i]]}]
        ],
        {i,1,Length[reduction]}
        ];
        PolyDependencyCheck[{seq},candidatePolyList,depModList]
    ]


InnerLoopRewwriteRules[{},rewriteRules_] :=
    rewriteRules


InnerLoopRewwriteRules[{Body[seq__],innerLoops___},rewriteRules_] :=
    Module[ {eqs,seqRules,newRules},
        eqs = RecEqs[seq,{}];
        seqRules = Apply[Rule,eqs,{1}];
        newRules = Append[rewriteRules,seqRules];
        InnerLoopRewwriteRules[{innerLoops},newRules]
    ]


(*********** WP[Rules,poly] ******************* *)


WP[{},poly_] :=
    Simplify[poly]


WP[{seq___,rule1_},poly_] :=
    WP[{seq},poly/.rule1]


WPInnerLoops[{},poly_,wpPoly_] :=
    wpPoly


WPInnerLoops[{innerLoopRules1_,rulesList___},poly_,wpPoly_] :=
    Module[ {wp1},
        wp1Poly = WP[innerLoopRules1,poly];
        WPInnerLoops[{rulesList},poly,Append[wpPoly,wp1Poly]]
    ]


WPPolySet[RulesList_,{},wpPolyList_] :=
    wpPolyList


WPPolySet[RulesList_,{poly1_,polySeq___},wpPolyList_] :=
    Module[ {wpListPoly1},
        wpListPoly1 = WPInnerLoops[RulesList,poly1,{}];
        WPPolySet[RulesList,{polySeq},Append[wpPolyList,wpListPoly1]]
    ]


(* no particular function. We use MMa's GroebnerBasis[] function. *)


(* returns YES, if candidates=filter_result, and DON'T KNOW/CANNOT DETERMINE COMPLETENESS otherwise *)


(*
Aligator[Recs__,Vars__,SummVars__]:=Module[{RecDep,RecVars=Map[First,Vars],SimpleRecVars=Map[Last,Vars],RewriteRules},
RecDep=Dependencies[RecVars,Variables->SummVars,Where->Recs];
RewriteRules=Apply[Rule,Vars,{1}];
GroebnerBasis[RecDep/.RewriteRules,SimpleRecVars]
]
*)

(* Uncomment/Comment Print[...] to enable/disable       *)
(* Note that PrintDebug returns the original expression *)
PrintDebug[msg_, expr_] :=
    Block[{strMsg},
        strMsg = If[msg == "", msg, msg <> ": "]; 
        (* Print[strMsg,expr]; *)
        expr
    ];

(* Operator form of PrintDebug; allows statements like: var = expr // PrintDebug["Value of var"] *)
PrintDebug[msg_][expr_] := PrintDebug[msg, expr];


End[];


EndPackage[];
