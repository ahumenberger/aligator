#!/usr/bin/env wolframscript
(* ::Package:: *)

(* Clear all definitions *)
Clear["Global`*"];
Clear["Aligator`*"];
(* Set working directory *)
SetDirectory[ParentDirectory[NotebookDirectory[]]];
(* Load Aligator and its dependencies *)
Needs["RISC`fastZeil`"];
Needs["RISC`Dependencies`"];
<< "src/Aligator.m";

(* Specify benchmark directories relative to working directory *)
benchmarkDirs = {"benchmarks/multipath"};
(* Set timeout in seconds *)
timeout = 60;
(* Get all files with extension .al in benchmarkDirs *)
benchmarks = FileNames["*.al", benchmarkDirs];
results = {};
AbortProtect[
  Do[
	  Print[FileBaseName[file]];
    loop = ReadString[file];
    cmd = "Timing[TimeConstrained[Aligator[" <> loop <> "]," <> ToString[timeout] <> ", $Timeout]]";
    res = {file, ToExpression[cmd]};
    AppendTo[results, res],
    {file, benchmarks}
  ]
]
Print[results // Grid];

tex = Cases[results, {f_,{t_,r_}} -> {FileBaseName[f],t}];
Print[tex // TeXForm];



