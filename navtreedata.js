/*
 @licstart  The following is the entire license notice for the JavaScript code in this file.

 The MIT License (MIT)

 Copyright (C) 1997-2020 by Dimitri van Heesch

 Permission is hereby granted, free of charge, to any person obtaining a copy of this software
 and associated documentation files (the "Software"), to deal in the Software without restriction,
 including without limitation the rights to use, copy, modify, merge, publish, distribute,
 sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 furnished to do so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in all copies or
 substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING
 BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
 DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

 @licend  The above is the entire license notice for the JavaScript code in this file
*/
var NAVTREE =
[
  [ "overload", "index.html", [
    [ "Citation index", "md_docs_citations.html", [
      [ "What rests on each sentence", "md_docs_citations.html#autotoc_md1", null ],
      [ "In scope, no counterpart yet", "md_docs_citations.html#autotoc_md2", null ],
      [ "Assumptions", "md_docs_citations.html#autotoc_md3", null ]
    ] ],
    [ "Decision log", "md_docs_decisions.html", [
      [ "draft-pin", "md_docs_decisions.html#autotoc_md6", null ],
      [ "spec-style", "md_docs_decisions.html#autotoc_md8", null ],
      [ "library-dependency", "md_docs_decisions.html#autotoc_md10", null ],
      [ "expression-depth", "md_docs_decisions.html#autotoc_md12", null ],
      [ "lookup-scope", "md_docs_decisions.html#autotoc_md14", null ],
      [ "ranking-fidelity", "md_docs_decisions.html#autotoc_md16", null ],
      [ "missing-instance", "md_docs_decisions.html#autotoc_md18", null ],
      [ "instance-inheritance", "md_docs_decisions.html#autotoc_md20", null ],
      [ "termination-condition", "md_docs_decisions.html#autotoc_md22", null ],
      [ "single-tu", "md_docs_decisions.html#autotoc_md24", null ],
      [ "test-oracle", "md_docs_decisions.html#autotoc_md26", null ],
      [ "citation-granularity", "md_docs_decisions.html#autotoc_md28", null ],
      [ "p3606-mode", "md_docs_decisions.html#autotoc_md30", null ],
      [ "repository", "md_docs_decisions.html#autotoc_md32", null ],
      [ "toolchain-pin", "md_docs_decisions.html#autotoc_md34", null ],
      [ "explicit-instance-routes", "md_docs_decisions.html#autotoc_md36", null ],
      [ "scope-syntax", "md_docs_decisions.html#autotoc_md38", null ]
    ] ],
    [ "Findings", "md_docs_findings.html", [
      [ "Against the Standard", "md_docs_findings.html#autotoc_md40", null ],
      [ "Compiler disagreements", "md_docs_findings.html#autotoc_md41", null ],
      [ "About the model", "md_docs_findings.html#autotoc_md42", null ],
      [ "About the plan", "md_docs_findings.html#autotoc_md43", null ],
      [ "About the library", "md_docs_findings.html#autotoc_md44", null ],
      [ "Design note", "md_docs_findings.html#autotoc_md45", null ]
    ] ],
    [ "A guide to the model", "md_docs_guide.html", [
      [ "Two sides", "md_docs_guide.html#autotoc_md47", null ],
      [ "How to read the Lean", "md_docs_guide.html#autotoc_md48", null ],
      [ "The Standard side, module by module", "md_docs_guide.html#autotoc_md49", [
        [ "Std and Lint", "md_docs_guide.html#autotoc_md50", null ],
        [ "Syntax", "md_docs_guide.html#autotoc_md51", null ],
        [ "Outcome", "md_docs_guide.html#autotoc_md52", null ],
        [ "Deduction", "md_docs_guide.html#autotoc_md53", null ],
        [ "Generality", "md_docs_guide.html#autotoc_md54", null ],
        [ "Constraint", "md_docs_guide.html#autotoc_md55", null ],
        [ "Program", "md_docs_guide.html#autotoc_md56", null ],
        [ "Steps", "md_docs_guide.html#autotoc_md57", null ],
        [ "Ordering", "md_docs_guide.html#autotoc_md58", null ],
        [ "Transitivity", "md_docs_guide.html#autotoc_md59", null ],
        [ "Specs", "md_docs_guide.html#autotoc_md60", null ],
        [ "Resolution", "md_docs_guide.html#autotoc_md61", null ],
        [ "Ranking", "md_docs_guide.html#autotoc_md62", null ],
        [ "Lookup", "md_docs_guide.html#autotoc_md63", null ],
        [ "Environment", "md_docs_guide.html#autotoc_md64", null ],
        [ "Separability", "md_docs_guide.html#autotoc_md65", null ],
        [ "Erasure", "md_docs_guide.html#autotoc_md66", null ],
        [ "Mandates", "md_docs_guide.html#autotoc_md67", null ],
        [ "Sfinae", "md_docs_guide.html#autotoc_md68", null ],
        [ "Dispatch", "md_docs_guide.html#autotoc_md69", null ],
        [ "Units", "md_docs_guide.html#autotoc_md70", null ],
        [ "Access", "md_docs_guide.html#autotoc_md71", null ],
        [ "Conjunction", "md_docs_guide.html#autotoc_md72", null ],
        [ "Emit", "md_docs_guide.html#autotoc_md73", null ]
      ] ],
      [ "What the Standard side established", "md_docs_guide.html#autotoc_md74", null ],
      [ "The typeclass side, module by module", "md_docs_guide.html#autotoc_md75", [
        [ "Encoding", "md_docs_guide.html#autotoc_md76", null ],
        [ "Routes", "md_docs_guide.html#autotoc_md77", null ],
        [ "Inheritance", "md_docs_guide.html#autotoc_md78", null ],
        [ "Units", "md_docs_guide.html#autotoc_md79", null ],
        [ "Members", "md_docs_guide.html#autotoc_md80", null ],
        [ "Emit", "md_docs_guide.html#autotoc_md81", null ]
      ] ],
      [ "From theorems to obligations", "md_docs_guide.html#autotoc_md82", null ],
      [ "What carries beyond typeclasses", "md_docs_guide.html#autotoc_md83", null ],
      [ "Running things", "md_docs_guide.html#autotoc_md84", null ]
    ] ],
    [ "Obligations", "md_docs_obligations.html", [
      [ "Two layers, three overload sets", "md_docs_obligations.html#autotoc_md86", null ],
      [ "Harvested", "md_docs_obligations.html#autotoc_md87", null ],
      [ "Beyond the model", "md_docs_obligations.html#autotoc_md88", null ]
    ] ],
    [ "Modelling C++ overload resolution in Lean: plan", "md_docs_plan.html", [
      [ "Purpose", "md_docs_plan.html#autotoc_md90", null ],
      [ "Scope", "md_docs_plan.html#autotoc_md91", null ],
      [ "Modelling approach", "md_docs_plan.html#autotoc_md92", null ],
      [ "Traceability to the Standard", "md_docs_plan.html#autotoc_md93", null ],
      [ "Phases", "md_docs_plan.html#autotoc_md94", null ],
      [ "Target theorems", "md_docs_plan.html#autotoc_md95", null ],
      [ "Separability suspects", "md_docs_plan.html#autotoc_md96", null ],
      [ "Instance inheritance", "md_docs_plan.html#autotoc_md97", null ],
      [ "Proof obligations", "md_docs_plan.html#autotoc_md98", null ],
      [ "Algorithm-author obligations", "md_docs_plan.html#autotoc_md99", [
        [ "algorithm-constraint-accuracy", "md_docs_plan.html#autotoc_md100", null ],
        [ "callable-copying", "md_docs_plan.html#autotoc_md101", null ],
        [ "result-context-formable", "md_docs_plan.html#autotoc_md102", null ],
        [ "instance-coherence", "md_docs_plan.html#autotoc_md103", null ],
        [ "capability-tests", "md_docs_plan.html#autotoc_md104", null ],
        [ "typeclass-refinement", "md_docs_plan.html#autotoc_md105", null ],
        [ "instance-state", "md_docs_plan.html#autotoc_md106", null ],
        [ "instance-exact-type", "md_docs_plan.html#autotoc_md107", null ],
        [ "Work", "md_docs_plan.html#autotoc_md108", null ]
      ] ],
      [ "Phase 9: declarations and where to find them", "md_docs_plan.html#autotoc_md109", [
        [ "What P1787R6 did to the sections the model cites", "md_docs_plan.html#autotoc_md110", null ],
        [ "The rules to transcribe, as they stand in N5054", "md_docs_plan.html#autotoc_md111", null ],
        [ "Stages", "md_docs_plan.html#autotoc_md112", null ]
      ] ],
      [ "Draft citations and prior art", "md_docs_plan.html#autotoc_md113", null ],
      [ "First steps", "md_docs_plan.html#autotoc_md114", null ]
    ] ],
    [ "Probes", "md_docs_probes.html", [
      [ "Step-order probe", "md_docs_probes.html#autotoc_md116", null ],
      [ "Tie-break probe", "md_docs_probes.html#autotoc_md117", null ],
      [ "Constant-argument conversion probe", "md_docs_probes.html#autotoc_md118", null ],
      [ "Who is right, 15 October 2026", "md_docs_probes.html#autotoc_md119", null ],
      [ "Library probes", "md_docs_probes.html#autotoc_md120", null ],
      [ "Algorithm probes", "md_docs_probes.html#autotoc_md121", null ]
    ] ],
    [ "Namespaces", "namespaces.html", [
      [ "Namespace List", "namespaces.html", "namespaces_dup" ],
      [ "Namespace Members", "namespacemembers.html", [
        [ "All", "namespacemembers.html", null ],
        [ "Functions", "namespacemembers_func.html", null ],
        [ "Variables", "namespacemembers_vars.html", null ]
      ] ]
    ] ],
    [ "Concepts", "concepts.html", "concepts" ],
    [ "Classes", "annotated.html", [
      [ "Class List", "annotated.html", "annotated_dup" ],
      [ "Class Index", "classes.html", null ],
      [ "Class Hierarchy", "hierarchy.html", "hierarchy" ],
      [ "Class Members", "functions.html", [
        [ "All", "functions.html", null ],
        [ "Functions", "functions_func.html", null ],
        [ "Variables", "functions_vars.html", null ]
      ] ]
    ] ],
    [ "Files", "files.html", [
      [ "File List", "files.html", "files_dup" ],
      [ "File Members", "globals.html", [
        [ "All", "globals.html", null ],
        [ "Functions", "globals_func.html", null ]
      ] ]
    ] ]
  ] ]
];

var NAVTREEINDEX =
[
"annotated.html"
];

var SYNCONMSG = 'click to disable panel synchronisation';
var SYNCOFFMSG = 'click to enable panel synchronisation';