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
      [ "cites are unchanged. [temp.spec.partial.general]/7 as before.", "md_docs_decisions.html#autotoc_md7", null ],
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
      [ "scope-syntax", "md_docs_decisions.html#autotoc_md38", null ],
      [ "integer-widths", "md_docs_decisions.html#autotoc_md40", null ],
      [ "value-typing", "md_docs_decisions.html#autotoc_md42", null ],
      [ "user-defined-conversions", "md_docs_decisions.html#autotoc_md44", null ]
    ] ],
    [ "Findings", "md_docs_findings.html", [
      [ "Against the Standard", "md_docs_findings.html#autotoc_md46", null ],
      [ "Compiler disagreements", "md_docs_findings.html#autotoc_md47", null ],
      [ "About the model", "md_docs_findings.html#autotoc_md48", null ],
      [ "About the plan", "md_docs_findings.html#autotoc_md49", null ],
      [ "About the library", "md_docs_findings.html#autotoc_md50", null ],
      [ "Design note", "md_docs_findings.html#autotoc_md51", null ]
    ] ],
    [ "A guide to the model", "md_docs_guide.html", [
      [ "Two sides", "md_docs_guide.html#autotoc_md53", null ],
      [ "How to read the Lean", "md_docs_guide.html#autotoc_md54", null ],
      [ "The Standard side, module by module", "md_docs_guide.html#autotoc_md55", [
        [ "Std and Lint", "md_docs_guide.html#autotoc_md56", null ],
        [ "Syntax", "md_docs_guide.html#autotoc_md57", null ],
        [ "Outcome", "md_docs_guide.html#autotoc_md58", null ],
        [ "Deduction", "md_docs_guide.html#autotoc_md59", null ],
        [ "Generality", "md_docs_guide.html#autotoc_md60", null ],
        [ "Constraint", "md_docs_guide.html#autotoc_md61", null ],
        [ "Program", "md_docs_guide.html#autotoc_md62", null ],
        [ "Arguments", "md_docs_guide.html#autotoc_md63", null ],
        [ "Steps", "md_docs_guide.html#autotoc_md64", null ],
        [ "Identity", "md_docs_guide.html#autotoc_md65", null ],
        [ "Ordering", "md_docs_guide.html#autotoc_md66", null ],
        [ "Transitivity", "md_docs_guide.html#autotoc_md67", null ],
        [ "Specs", "md_docs_guide.html#autotoc_md68", null ],
        [ "Resolution", "md_docs_guide.html#autotoc_md69", null ],
        [ "Ranking", "md_docs_guide.html#autotoc_md70", null ],
        [ "Lookup", "md_docs_guide.html#autotoc_md71", null ],
        [ "Environment", "md_docs_guide.html#autotoc_md72", null ],
        [ "Separability", "md_docs_guide.html#autotoc_md73", null ],
        [ "Erasure", "md_docs_guide.html#autotoc_md74", null ],
        [ "Mandates", "md_docs_guide.html#autotoc_md75", null ],
        [ "Sfinae", "md_docs_guide.html#autotoc_md76", null ],
        [ "Dispatch", "md_docs_guide.html#autotoc_md77", null ],
        [ "Units", "md_docs_guide.html#autotoc_md78", null ],
        [ "DependentCandidate", "md_docs_guide.html#autotoc_md79", null ],
        [ "Access", "md_docs_guide.html#autotoc_md80", null ],
        [ "Conjunction", "md_docs_guide.html#autotoc_md81", null ],
        [ "Scope", "md_docs_guide.html#autotoc_md82", null ],
        [ "Names", "md_docs_guide.html#autotoc_md83", null ],
        [ "Adl", "md_docs_guide.html#autotoc_md84", null ],
        [ "Members", "md_docs_guide.html#autotoc_md85", null ],
        [ "Emit", "md_docs_guide.html#autotoc_md86", null ]
      ] ],
      [ "What the Standard side established", "md_docs_guide.html#autotoc_md87", null ],
      [ "The typeclass side, module by module", "md_docs_guide.html#autotoc_md88", [
        [ "Encoding", "md_docs_guide.html#autotoc_md89", null ],
        [ "Routes", "md_docs_guide.html#autotoc_md90", null ],
        [ "Arguments", "md_docs_guide.html#autotoc_md91", null ],
        [ "Conversion", "md_docs_guide.html#autotoc_md92", null ],
        [ "Inheritance", "md_docs_guide.html#autotoc_md93", null ],
        [ "Units", "md_docs_guide.html#autotoc_md94", null ],
        [ "Members", "md_docs_guide.html#autotoc_md95", null ],
        [ "Lookup", "md_docs_guide.html#autotoc_md96", null ],
        [ "Emit", "md_docs_guide.html#autotoc_md97", null ]
      ] ],
      [ "From theorems to obligations", "md_docs_guide.html#autotoc_md98", null ],
      [ "What carries beyond typeclasses", "md_docs_guide.html#autotoc_md99", null ],
      [ "Running things", "md_docs_guide.html#autotoc_md100", null ]
    ] ],
    [ "Obligations", "md_docs_obligations.html", [
      [ "Two layers, three overload sets", "md_docs_obligations.html#autotoc_md102", null ],
      [ "Harvested", "md_docs_obligations.html#autotoc_md103", null ],
      [ "Beyond the model", "md_docs_obligations.html#autotoc_md104", null ]
    ] ],
    [ "Modelling C++ overload resolution in Lean: plan", "md_docs_plan.html", [
      [ "Purpose", "md_docs_plan.html#autotoc_md106", null ],
      [ "Scope", "md_docs_plan.html#autotoc_md107", null ],
      [ "Modelling approach", "md_docs_plan.html#autotoc_md108", null ],
      [ "Traceability to the Standard", "md_docs_plan.html#autotoc_md109", null ],
      [ "Phases", "md_docs_plan.html#autotoc_md110", null ],
      [ "Target theorems", "md_docs_plan.html#autotoc_md111", null ],
      [ "Separability suspects", "md_docs_plan.html#autotoc_md112", null ],
      [ "Instance inheritance", "md_docs_plan.html#autotoc_md113", null ],
      [ "Proof obligations", "md_docs_plan.html#autotoc_md114", null ],
      [ "Algorithm-author obligations", "md_docs_plan.html#autotoc_md115", [
        [ "algorithm-constraint-accuracy", "md_docs_plan.html#autotoc_md116", null ],
        [ "callable-copying", "md_docs_plan.html#autotoc_md117", null ],
        [ "result-context-formable", "md_docs_plan.html#autotoc_md118", null ],
        [ "instance-coherence", "md_docs_plan.html#autotoc_md119", null ],
        [ "capability-tests", "md_docs_plan.html#autotoc_md120", null ],
        [ "typeclass-refinement", "md_docs_plan.html#autotoc_md121", null ],
        [ "instance-state", "md_docs_plan.html#autotoc_md122", null ],
        [ "instance-exact-type", "md_docs_plan.html#autotoc_md123", null ],
        [ "Work", "md_docs_plan.html#autotoc_md124", null ]
      ] ],
      [ "Phase 9: declarations and where to find them", "md_docs_plan.html#autotoc_md125", [
        [ "What P1787R6 did to the sections the model cites", "md_docs_plan.html#autotoc_md126", null ],
        [ "The rules to transcribe, as they stand in N5054", "md_docs_plan.html#autotoc_md127", null ],
        [ "Stages", "md_docs_plan.html#autotoc_md128", null ]
      ] ],
      [ "Phase 10: template arguments and their conversion", "md_docs_plan.html#autotoc_md129", [
        [ "The rules to transcribe, as they stand in N5054", "md_docs_plan.html#autotoc_md130", null ],
        [ "Design", "md_docs_plan.html#autotoc_md131", null ],
        [ "Stages", "md_docs_plan.html#autotoc_md132", null ]
      ] ],
      [ "Phase 11: user-defined conversions", "md_docs_plan.html#autotoc_md133", [
        [ "The rules to transcribe, as they stand in N5054", "md_docs_plan.html#autotoc_md134", null ],
        [ "Design", "md_docs_plan.html#autotoc_md135", null ],
        [ "Stages", "md_docs_plan.html#autotoc_md136", null ]
      ] ],
      [ "Draft citations and prior art", "md_docs_plan.html#autotoc_md137", null ],
      [ "First steps", "md_docs_plan.html#autotoc_md138", null ]
    ] ],
    [ "Probes", "md_docs_probes.html", [
      [ "Step-order probe", "md_docs_probes.html#autotoc_md140", null ],
      [ "Tie-break probe", "md_docs_probes.html#autotoc_md141", null ],
      [ "Constant-argument conversion probe", "md_docs_probes.html#autotoc_md142", null ],
      [ "Who is right, 15 October 2026", "md_docs_probes.html#autotoc_md143", null ],
      [ "Library probes", "md_docs_probes.html#autotoc_md144", null ],
      [ "Algorithm probes", "md_docs_probes.html#autotoc_md145", null ]
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