-- Overload/Object/P4222.lean                                         -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload.Object.Machine

/-!
# P4222R3, "An initialization profile", against the object model

The checker is parameterized by `Rules`, with the design paper's
reading as the default and P4416R0's as `Rules.wording`
(`Overload/Object/P4416.lean`).

Stroustrup's initialization profile (P4222R3, 22 October 2026) is a
set of compile-time rules with a stated guarantee, "no use of
uninitialized objects", enforced by local static analysis over three
attributes, `[[uninit]]`, `[[ref_to_uninit]]` and `[[must_init]]`, and
one unverified function, `now_init`. This module transcribes the rules
that apply to the fragment's traces as a checker, `check`, and compares
its verdicts with the machine's.

The profile's state is a third notion beside the Standard's two. The
Standard has an object's lifetime ([basic.life]) and the state of its
bytes ([basic.indet]); the profile has "initialized memory", a mark on a
variable, an allocation or a member that `construct_at` and assignment
set and `destroy_at` clears (P4222R3 §4.6, §8.2). The theorems below are
traces on which the mark and the object model disagree, in both
directions, each a `decide`.

What the checker reads into the paper, where the paper leaves room
(`decisions.md#initialization-profile`):

* **Aliasing.** The paper asks for local analysis and says nothing about
  pointers that alias. The checker gives the profile the most favourable
  reading: every pointer carries the variable or allocation it was
  derived from and the member path within it, so `destroy_at(p)` marks
  the object `p` refers to however it was reached. The findings do not
  depend on this; they hold with perfect alias knowledge.
* **Implicit initialization** (§2) is a default constructor, a default
  member initializer, or zero-initialization of a static. `T t;` for a
  class whose default constructor is user-provided counts as initialized,
  and §5.1's check that the constructor initializes every member not
  marked `[[uninit]]` is `classViolations`.
* **Writes.** Assignment through a pointer to an uninitialized complete
  scalar initializes it (§1.3); assignment to a member of an
  uninitialized aggregate or union is an error (§5.4, §5.6); assignment
  to a member marked `[[uninit]]` of an initialized class initializes
  that member (§5.2). Bytes stored through `unsigned char` or
  `std::byte` lvalues are allowed and leave the mark alone (§4.6, §4.8);
  `memcpy` is assignment and sets it.
* **Library functions the paper does not mention.** `std::launder`
  returns what it was given. `std::start_lifetime_as` has two readings:
  unannotated, an ordinary function returning a pointer to initialized
  memory (§4.3, the default for a pointer); or annotated
  `[[ref_to_uninit]]`, so that its result must be initialized before use
  (`Rules.startLifetimeAs`). Both are checked, and the wording's third
  reading in `Overload/Object/P4416.lean`.
-/

namespace Overload.Object.P4222

open Machine

/-- How the library spells `std::start_lifetime_as`, which neither paper
mentions: as an ordinary function whose result refers to initialized
objects and whose argument may be anything (the design paper's default
for a function returning a pointer, P4222R3 §4.3); with its result
`[[ref_to_uninit]]`; or as the wording has every unannotated function,
P4416R0 [profiles.init.ref]/3, /4, whose pointer argument must refer to
initialized objects and whose result refers to initialized objects. -/
inductive StartLifetimeAs where
  | unannotated | refToUninit | wording
  deriving Repr, DecidableEq, Inhabited

/-- The points where the two papers differ, or where either leaves room,
as switches. `design` is P4222R3 read as the session reads it;
`wording` is P4416R0 (`Overload/Object/P4416.lean`). -/
structure Rules where
  /-- Reading an uninitialized `unsigned char` or `std::byte` is allowed
  (P4222R3 abstract, §4.6); the wording's [profiles.init.use]/1 has no
  such exception. -/
  byteReadException : Bool := true
  /-- Bytes may be stored into an uninitialized buffer through byte
  lvalues (P4222R3 §4.8, "assigning to an uninitialized std::byte … is
  allowed"); the wording's [profiles.init.use]/(1.3) makes an
  assignment to an element of an uninitialized array a use, and its
  example rejects `buf[0] = std::byte{0}`. -/
  byteStoresAllowed : Bool := true
  /-- `memcpy` into uninitialized storage initializes it, as assignment
  of bytes; the wording's drafting note under [profiles.init.terms]/4
  says deliberately not, and its [profiles.init.ref]/4 then rejects the
  call, since `memcpy`'s parameters are unannotated. -/
  memcpyInitializes : Bool := true
  /-- Arguments to unannotated library functions, `std::launder` among
  them, must refer to initialized objects ([profiles.init.ref]/4). -/
  libraryArgumentsInitialized : Bool := false
  /-- An object with automatic storage duration whose type is not
  trivially destructible must be initialized where its scope ends
  ([profiles.init.life]/2). The design paper has no explicit rule;
  its §4.6 "Destruction has a similar pattern" is read as agreeing. -/
  initializedAtScopeExit : Bool := true
  startLifetimeAs : StartLifetimeAs := .unannotated
  deriving Repr, DecidableEq, Inhabited

/-- The attribute on a pointer parameter: none, so that it refers to
initialized objects; `[[ref_to_uninit]]` (§4.2); or `[[must_init]]`, a
`[[ref_to_uninit]]` the function must initialize (§4.2, P4416R0
[dcl.attr.mustinit]). -/
inductive ParamAttr where
  | plain | refToUninit | mustInit
  deriving Repr, DecidableEq, Inhabited

/-- A function's annotations: one per parameter, in order; whether the
function is `[[now_init]]`, so that its `[[ref_to_uninit]]` parameters
count as initialized by the call without the body being checked
(P4416R0 [dcl.attr.nowinit]); whether its result is `[[ref_to_uninit]]`
(§4.2, [dcl.attr.reftouninit]/(1.3)); and the pointee type of its
result, for member access on it. A function with no entry is
unannotated: every parameter plain, the result referring to initialized
objects (P4416R0 [profiles.init.general]/5). -/
structure FunSig where
  name : String
  params : List ParamAttr := []
  nowInit : Bool := false
  retRefToUninit : Bool := false
  ret : Ty := .named "void"
  /-- The body's variables defined `[[uninit]]`: a body has names of its
  own. -/
  uninit : List String := []
  deriving Repr, DecidableEq, Inhabited

/-- The profile's annotations on a trace: the variables defined
`[[uninit]]` (§4.1), the class members marked `[[uninit]]` by class and
element index (§5.2), the functions' annotations, and the rule set. -/
structure Annotations where
  uninit : List String := []
  uninitMembers : List (Ty × Nat) := []
  functions : List FunSig := []
  rules : Rules := {}
  deriving Repr, Inhabited

/-- The signature of a function, unannotated when none is given. -/
def Annotations.sig (a : Annotations) (f : String) (arity : Nat) : FunSig :=
  match a.functions.find? (·.name == f) with
  | some sg => sg
  | none => { name := f, params := List.replicate arity .plain }

/-- P4416R0's rule set. -/
def Rules.wording : Rules :=
  { byteReadException := false, byteStoresAllowed := false, memcpyInitializes := false
    libraryArgumentsInitialized := true, initializedAtScopeExit := true, startLifetimeAs := .wording }

/-- The profile's two states of memory (§4.1, §4.6). -/
inductive Mark where
  | init | uninit
  deriving Repr, DecidableEq, Inhabited

/-- What a pointer refers to, as the analysis knows it: a root, a
variable's name or an allocation's, and the member path within it. -/
structure Ref where
  root : String
  path : List Nat := []
  deriving Repr, DecidableEq, Inhabited

/-- A violation of the profile, by rule. -/
inductive Violation where
  /-- An uninitialized object not marked `[[uninit]]` (§4.1). -/
  | uninitializedNotMarked (name : String)
  /-- An initialized object marked `[[uninit]]` (§4.1), including an
  aggregate some of whose members default-construct (§5.4). -/
  | initializedAndUninit (name : String)
  /-- A read of uninitialized memory (§4.1, §4.6). -/
  | readUninit (ptr : String)
  /-- Assignment to a member of an uninitialized aggregate or union
  (§5.4, §5.6). -/
  | memberAssignment (ptr : String)
  /-- `construct_at` on initialized memory: initialized twice (§4.6). -/
  | constructTwice (ptr : String)
  /-- `destroy_at` on uninitialized memory: destroyed twice (§4.6). -/
  | destroyTwice (ptr : String)
  /-- `now_init` on memory the profile holds initialized (§4.4). -/
  | nowInitOfInitialized (ptr : String)
  /-- A constructor that leaves a member neither initialized nor marked
  `[[uninit]]` (§5.1). -/
  | constructorLeavesMember (cls : Ty) (element : Nat)
  /-- An argument that refers to uninitialized objects passed to a
  function whose parameter refers to initialized ones (P4416R0
  [profiles.init.ref]/4). -/
  | uninitArgument (ptr : String)
  /-- An argument that refers to initialized objects passed to a
  `[[ref_to_uninit]]` or `[[must_init]]` parameter (§4.2, P4416R0
  [profiles.init.ref]/2, /4). -/
  | initializedArgument (ptr : String)
  /-- A `[[must_init]]` parameter whose referent is not initialized at
  the end of the body (P4416R0 [profiles.init.ref]/5). -/
  | mustInitNotInitialized (fn param : String)
  /-- A return whose operand's marking is not the function's: a
  `[[ref_to_uninit]]` function returning a pointer to initialized
  objects, or any other function returning one to uninitialized objects
  (P4416R0 [profiles.init.ref]/6). -/
  | returnMarkMismatch (fn : String)
  /-- An automatic object of a type that is not trivially destructible,
  uninitialized where its scope ends (P4416R0 [profiles.init.life]/2). -/
  | uninitAtScopeExit (name : String)
  /-- A pointer variable the trace never bound. -/
  | unbound (name : String)
  deriving Repr, DecidableEq, Inhabited

/-- The analysis state. -/
structure CheckState where
  /-- The mark of each root. -/
  roots : List (String × Mark) := []
  /-- The type of each root's object. -/
  types : List (String × Ty) := []
  /-- Marks on member paths, where they differ from the root's. -/
  paths : List (Ref × Mark) := []
  /-- What each pointer variable refers to, with its static type. -/
  ptrs : List (String × Ref × Ty) := []
  /-- The open blocks, innermost first, each with the automatic
  variables defined in it. -/
  blocks : List (List String) := [[]]
  violations : List Violation := []
  deriving Repr, Inhabited

namespace CheckState

def violate (c : CheckState) (v : Violation) : CheckState := { c with violations := c.violations ++ [v] }

def setRoot (c : CheckState) (r : String) (t : Ty) (mk : Mark) : CheckState :=
  { c with roots := (r, mk) :: c.roots.filter (·.1 != r), types := (r, t) :: c.types.filter (·.1 != r)
           paths := c.paths.filter (·.1.root != r) }

def setPath (c : CheckState) (ref : Ref) (mk : Mark) : CheckState :=
  if ref.path.isEmpty then
    match c.roots.find? (·.1 == ref.root) with
    | some _ => { c with roots := (ref.root, mk) :: c.roots.filter (·.1 != ref.root)
                         paths := c.paths.filter (·.1.root != ref.root) }
    | none => c
  else { c with paths := (ref, mk) :: c.paths.filter (·.1 != ref) }

def setPtr (c : CheckState) (x : String) (ref : Ref) (t : Ty) : CheckState :=
  { c with ptrs := (x, ref, t) :: c.ptrs.filter (·.1 != x) }

def declare (c : CheckState) (x : String) : CheckState :=
  match c.blocks with
  | b :: bs => { c with blocks := (b ++ [x]) :: bs }
  | [] => c

def ptr? (c : CheckState) (x : String) : Option (Ref × Ty) := (c.ptrs.find? (·.1 == x)).map (·.2)

end CheckState

/-- The element type at a member path within a type. -/
def elementAt (m : Model) : Ty → List Nat → Option Ty
  | t, [] => some t
  | t, i :: is => ((m.elements t)[i]?).bind fun e => elementAt m e is

/-- Does default-initialization initialize an object of the type, in the
profile's sense (§2, §5.4): a class whose default constructor is
user-provided, or an aggregate every element of which has a default
member initializer or is itself so initialized? A scalar and a union are
not. -/
def defaultInitializes (m : Model) : Nat → Ty → Bool
  | 0, _ => false
  | fuel + 1, t =>
    if Model.isScalar t || m.isUnion t then false
    else if m.userProvidedDefaultCtor t then true
    else
      let members := m.membersOf t
      let bases := m.baseCount t
      (m.elements t).zipIdx.all fun (e, i) =>
        (i ≥ bases && (members[i - bases]?.any (·.init))) || defaultInitializes m fuel e

/-- Does default-initialization initialize some element of the type:
the condition under which `[[uninit]]` is an error for an aggregate
(§5.4, `S s4 [[uninit]]` with a `string` member)? -/
def defaultInitializesSome (m : Model) (t : Ty) : Bool :=
  if Model.isScalar t || m.isUnion t then false
  else if m.userProvidedDefaultCtor t then true
  else
    let members := m.membersOf t
    let bases := m.baseCount t
    (m.elements t).zipIdx.any fun (e, i) =>
      (i ≥ bases && (members[i - bases]?.any (·.init))) || defaultInitializes m m.depth e

/-- Is an object initialized by its definition (§2, §4.1)? -/
def initializedBy (m : Model) (t : Ty) : Init → Bool
  | .default => defaultInitializes m m.depth t
  | _ => true

/-- The mark of a reference: the most specific path mark, else the
root's; a member marked `[[uninit]]` whose path has no mark is
uninitialized (§5.2). -/
def markOf (m : Model) (a : Annotations) (c : CheckState) (ref : Ref) : Mark :=
  match c.paths.find? (·.1 == ref) with
  | some (_, mk) => mk
  | none =>
    let annotated :=
      match ref.path.getLast?, c.types.find? (·.1 == ref.root) with
      | some i, some (_, t) =>
        match elementAt m t ref.path.dropLast with
        | some cls => a.uninitMembers.contains (cls.stripConst, i)
        | none => false
      | _, _ => false
    if annotated then .uninit
    else (c.roots.find? (·.1 == ref.root)).map (·.2) |>.getD .init

/-- Is the referent a scalar complete object or a scalar member? -/
def referentType (m : Model) (c : CheckState) (ref : Ref) : Option Ty :=
  (c.types.find? (·.1 == ref.root)).bind fun (_, t) => elementAt m t ref.path

/-- One operation under the profile's rules. -/
def checkOp (m : Model) (a : Annotations) (c : CheckState) : Op → CheckState
  | .var x ty init _ _ =>
    let initialized := initializedBy m ty init
    let c := c.declare x
    if a.uninit.contains x then
      if initialized || (init == .default && defaultInitializesSome m ty) then
        (c.setRoot x ty .uninit).violate (.initializedAndUninit x)
      else c.setRoot x ty .uninit
    else if initialized then c.setRoot x ty .init
    else (c.setRoot x ty .uninit).violate (.uninitializedNotMarked x)
  | .staticVar x ty _ =>
    -- Zero-initialized before any other initialization: initialized (§2, §3).
    if a.uninit.contains x then (c.setRoot x ty .init).violate (.initializedAndUninit x)
    else c.setRoot x ty .init
  | .malloc x _ =>
    -- `malloc` is `[[ref_to_uninit]]` (§4.3).
    (c.setRoot ("#" ++ x) (.named "void") .uninit).setPtr x ⟨"#" ++ x, []⟩ (.named "void")
  | .free _ => c
  | .newObject x ty init =>
    let mk := if initializedBy m ty init then Mark.init else .uninit
    (c.setRoot ("#" ++ x) ty mk).setPtr x ⟨"#" ++ x, []⟩ ty
  | .delete q =>
    -- A delete-expression is not a destruction in either paper: P4222R3
    -- §4.6 names `destroy_at`, P4416R0 [profiles.init.terms]/5 names
    -- `destroy_at`, `destroy` and explicit destructor calls. The state
    -- is unchanged, and the dangling pointer is the invalidation
    -- profile's.
    match c.ptr? q with
    | some _ => c
    | none => c.violate (.unbound q)
  | .placementNew x ty q init =>
    match c.ptr? q with
    | some (ref, _) =>
      if initializedBy m ty init then
        let c := if markOf m a c ref == .init then c.violate (.constructTwice q) else c
        (c.setPath ref .init).setPtr x ref ty
      else
        -- A placement new whose initialization leaves the object
        -- uninitialized is not an initialization ([profiles.init.terms]/4.3);
        -- the object is uninitialized at its definition (/3.3).
        (c.setPath ref .uninit).setPtr x ref ty
    | none => c.violate (.unbound q)
  | .destroy q =>
    match c.ptr? q with
    | some (ref, _) =>
      if markOf m a c ref == .uninit then c.violate (.destroyTwice q) else c.setPath ref .uninit
    | none => c.violate (.unbound q)
  | .startLifetimeAs x ty q =>
    match c.ptr? q with
    | some (ref, _) =>
      match a.rules.startLifetimeAs with
      | .refToUninit => (c.setPath ref .uninit).setPtr x ref ty
      | .unannotated => (c.setPath ref .init).setPtr x ref ty
      | .wording =>
        let c := if markOf m a c ref == .uninit then c.violate (.uninitArgument q) else c
        (c.setPath ref .init).setPtr x ref ty
    | none => c.violate (.unbound q)
  | .startLifetime _ => c
  | .launder x q =>
    match c.ptr? q with
    | some (ref, t) =>
      let c := if a.rules.libraryArgumentsInitialized && markOf m a c ref == .uninit then
        c.violate (.uninitArgument q) else c
      c.setPtr x ref t
    | none => c.violate (.unbound q)
  | .nowInit x q =>
    match c.ptr? q with
    | some (ref, t) =>
      let c := if markOf m a c ref == .init then c.violate (.nowInitOfInitialized q) else c
      (c.setPath ref .init).setPtr x ref t
    | none => c.violate (.unbound q)
  | .cast x ty q =>
    match c.ptr? q with
    | some (ref, _) => c.setPtr x ref ty
    | none => c.violate (.unbound q)
  | .addr x v =>
    match c.types.find? (·.1 == v) with
    | some (_, t) => c.setPtr x ⟨v, []⟩ t
    | none => c.violate (.unbound v)
  | .member x q i =>
    match c.ptr? q with
    | some (ref, t) =>
      let ref' : Ref := { ref with path := ref.path ++ [i] }
      c.setPtr x ref' (((m.elements t)[i]?).getD t)
    | none => c.violate (.unbound q)
  | .read _ q =>
    match c.ptr? q with
    | some (ref, t) =>
      if markOf m a c ref == .uninit && !(a.rules.byteReadException && isByteType t) then
        c.violate (.readUninit q)
      else c
    | none => c.violate (.unbound q)
  | .write q _ =>
    match c.ptr? q with
    | some (ref, _) =>
      if markOf m a c ref == .init then c
      else if ref.path.isEmpty then c.setPath ref .init
      else
        -- A member of an uninitialized object: an error unless the
        -- object is initialized and the member alone is `[[uninit]]`.
        let parent : Ref := { ref with path := ref.path.dropLast }
        if markOf m a c parent == .init then c.setPath ref .init
        else c.violate (.memberAssignment q)
    | none => c.violate (.unbound q)
  | .memcpy dst src _ =>
    match c.ptr? dst, c.ptr? src with
    | some (rd, _), some (rs, _) =>
      if a.rules.memcpyInitializes then
        let c := if markOf m a c rs == .uninit then c.violate (.readUninit src) else c
        c.setPath rd .init
      else
        -- Not an initialization, and both parameters unannotated.
        let c := if markOf m a c rs == .uninit then c.violate (.uninitArgument src) else c
        if markOf m a c rd == .uninit then c.violate (.uninitArgument dst) else c
    | none, _ => c.violate (.unbound dst)
    | _, none => c.violate (.unbound src)
  | .storeBytes q _ =>
    match c.ptr? q with
    | some (ref, _) =>
      if !a.rules.byteStoresAllowed && markOf m a c ref == .uninit then c.violate (.memberAssignment q) else c
    | none => c.violate (.unbound q)
  | .call x f args =>
    -- The call affects the arguments only through the callee's
    -- attributes ([profiles.init.analysis]/1 note): a plain parameter
    -- wants an initialized argument, a `[[ref_to_uninit]]` or
    -- `[[must_init]]` one an uninitialized argument, and after the call
    -- the referents of `[[must_init]]` parameters, and of every
    -- `[[ref_to_uninit]]` parameter of a `[[now_init]]` function, are
    -- initialized.
    let sg := a.sig f args.length
    let c := (sg.params.zip args).foldl (fun c (attr, q) =>
      match c.ptr? q with
      | some (ref, _) =>
        let mk := markOf m a c ref
        match attr with
        | .plain => if mk == .uninit then c.violate (.uninitArgument q) else c
        | .refToUninit =>
          let c := if mk == .init then c.violate (.initializedArgument q) else c
          if sg.nowInit then c.setPath ref .init else c
        | .mustInit =>
          let c := if mk == .init then c.violate (.initializedArgument q) else c
          c.setPath ref .init
      | none => c.violate (.unbound q)) c
    match x with
    | some x =>
      let root := "#" ++ x
      (c.setRoot root sg.ret (if sg.retRefToUninit then .uninit else .init)).setPtr x ⟨root, []⟩ sg.ret
    | none => c
  | .beginBlock => { c with blocks := [] :: c.blocks }
  | .endBlock =>
    match c.blocks with
    | b :: bs =>
      let c := { c with blocks := bs }
      if !a.rules.initializedAtScopeExit then c
      else b.foldl (fun c x =>
        match c.types.find? (·.1 == x) with
        | some (_, t) =>
          if m.nontrivialDtor t && markOf m a c ⟨x, []⟩ == .uninit then c.violate (.uninitAtScopeExit x) else c
        | none => c) c
    | [] => c

/-- A class's constructors initialize every member not marked
`[[uninit]]` (§5.1): for each class with a user-provided default
constructor, every member has a default member initializer, is written
by the constructor, or is marked. -/
def classViolations (m : Model) (a : Annotations) : List Violation :=
  (m.program.filterMap fun d =>
    match d with
    | .class n _ _ _ => some (Ty.named n)
    | _ => none).flatMap fun cls =>
    if !m.userProvidedDefaultCtor cls then []
    else
      let bases := m.baseCount cls
      let members := m.membersOf cls
      let written := (m.ctorInitsOf cls).map (·.1)
      (m.elements cls).zipIdx.filterMap fun (e, i) =>
        let hasDmi := i ≥ bases && (members[i - bases]?.any (·.init))
        if hasDmi || written.contains i || a.uninitMembers.contains (cls, i) ||
            defaultInitializes m m.depth e then none
        else some (.constructorLeavesMember cls i)

/-- A function body under the profile's rules, each function analyzed on
its own (P4416R0 [profiles.init.general]/3): each parameter refers to an
object whose mark is its attribute's; at the end of the body every
`[[must_init]]` parameter's referent is initialized unless the function
is `[[now_init]]` ([profiles.init.ref]/5), and the returned pointer's
referent is uninitialized exactly when the function is
`[[ref_to_uninit]]` ([profiles.init.ref]/6). -/
def functionViolations (m : Model) (a : Annotations) : List Violation :=
  m.functions.flatMap fun fd =>
    let sg := a.sig fd.name fd.params.length
    let a : Annotations := { a with uninit := sg.uninit }
    let c₀ : CheckState := (fd.params.zip sg.params).foldl (fun c ((pn, pty), attr) =>
      let root := "*" ++ pn
      (c.setRoot root pty (if attr == .plain then .init else .uninit)).setPtr pn ⟨root, []⟩ pty) {}
    let c := fd.body.foldl (checkOp m a) c₀
    let obligations := (fd.params.zip sg.params).filterMap fun ((pn, _), attr) =>
      if attr == .mustInit && !sg.nowInit && markOf m a c ⟨"*" ++ pn, []⟩ != .init then
        some (Violation.mustInitNotInitialized fd.name pn)
      else none
    let ret := match fd.ret with
      | some r =>
        match c.ptr? r with
        | some (ref, _) =>
          if (markOf m a c ref == .uninit) != sg.retRefToUninit then [Violation.returnMarkMismatch fd.name] else []
        | none => [Violation.unbound r]
      | none => []
    c.violations ++ obligations ++ ret

/-- The violations of a trace, with those of the model's classes and
functions. -/
def check (m : Model) (a : Annotations) (t : Trace) : List Violation :=
  classViolations m a ++ functionViolations m a ++ (t.foldl (checkOp m a) {}).violations

/-- Does the profile accept the trace? -/
def accepts (m : Model) (a : Annotations) (t : Trace) : Bool := (check m a t).isEmpty

/-- The hazard the profile's guarantee is about: undefined behaviour or
an erroneous read in the run. -/
def hazard (m : Model) (t : Trace) : Bool :=
  match run m t with
  | .undefined _ | .erroneous _ _ => true
  | _ => false

/-! ## The traces -/

private def int : Ty := .named "int"
private def uchar : Ty := .named "unsigned char"
private def short : Ty := .named "short"
private def cX : Ty := .named "X"
private def cC : Ty := .named "C"
private def cPair : Ty := .named "Pair"
private def cPoint : Ty := .named "Point"
private def cT : Ty := .named "T"
private def cU : Ty := .named "U"
private def cB : Ty := .named "B"
private def cD : Ty := .named "D"

/-- `struct X { int n; }; struct C { int i; }; struct Pair { short a, b; };
struct Point { int x, y; }; struct T { T() {} int x; }; union U { int i;
short s; }; struct B { int b; }; struct D : B { int d; };` -/
def model : Model :=
  { program :=
      [ .class "X", .member cX { name := "n", ty := int }
      , .class "C", .member cC { name := "i", ty := int }
      , .class "Pair", .member cPair { name := "a", ty := short }, .member cPair { name := "b", ty := short }
      , .class "Point", .member cPoint { name := "x", ty := int }, .member cPoint { name := "y", ty := int }
      , .class "T", .special cT { kind := .defaultCtor }, .member cT { name := "x", ty := int }
      , .class "B", .member cB { name := "b", ty := int }
      , .class "D" [cB], .member cD { name := "d", ty := int } ]
    unions := [("U", [{ name := "i", ty := int }, { name := "s", ty := short }])] }

/-- No annotations, and `T::x` marked `[[uninit]]` so that `T`'s
constructor passes §5.1. -/
def plain : Annotations := { uninitMembers := [(cT, 0)] }

/-! ### The paper's own examples, §4.1 -/

/-- `int loc; // error: no initialization` -/
theorem loc_rejected : check model plain [.var "loc" int] = [.uninitializedNotMarked "loc"] := by decide

/-- `int loc2 [[uninit]]; // OK` -/
theorem loc2_accepted : accepts model { plain with uninit := ["loc2"] } [.var "loc2" int] = true := by decide

/-- `int loc4 [[uninit]] = 4; // error: initialized and [[uninit]]` -/
theorem loc4_rejected :
    check model { plain with uninit := ["loc4"] } [.var "loc4" int (.scalar 4)] = [.initializedAndUninit "loc4"] := by
  decide

/-- `int loc5 [[uninit]]; int x = loc5; // error: read before initialized` -/
theorem loc5_rejected :
    check model { plain with uninit := ["loc5"] } [.var "loc5" int, .addr "p" "loc5", .read "x" "p"] =
      [.readUninit "p"] := by
  decide

/-- `int loc6 [[uninit]]; loc6 = 7; int y = loc6; // OK` -/
theorem loc6_accepted :
    accepts model { plain with uninit := ["loc6"] }
      [.var "loc6" int, .addr "p" "loc6", .write "p" 7, .read "y" "p"] = true := by
  decide

/-- `int glob; // OK: default initialized`, and `int glob2 [[uninit]];
// error: initialized and [[uninit]]` (§4.1). -/
theorem glob_examples :
    accepts model plain [.staticVar "glob" int] = true ∧
    check model { plain with uninit := ["glob2"] } [.staticVar "glob2" int] = [.initializedAndUninit "glob2"] := by
  decide

/-- `Point p [[uninit]]; p.x = 7; // error: member assignment` (§5.4). -/
theorem point_member_assignment_rejected :
    check model { plain with uninit := ["p"] } [.var "p" cPoint, .addr "pp" "p", .member "px" "pp" 0, .write "px" 7] =
      [.memberAssignment "px"] := by
  decide

/-- `S x3; // error` and `S x4 [[uninit]]; x4.s = …; // not accepted`
(§5.6). -/
theorem union_definition_examples :
    check model plain [.var "x3" cU] = [.uninitializedNotMarked "x3"] ∧
    check model { plain with uninit := ["x4"] } [.var "x4" cU, .addr "p" "x4", .member "ps" "p" 1, .write "ps" 3] =
      [.memberAssignment "ps"] := by
  decide

/-- `destroy_at` twice is an error (§4.6). -/
theorem destroy_twice_rejected :
    check model plain [.var "c" cC (.braces [1]), .addr "p" "c", .destroy "p", .destroy "p"] = [.destroyTwice "p"] := by
  decide

/-- `construct_at` on an initialized object is an error (§4.6). -/
theorem construct_twice_rejected :
    check model plain [.var "c" cC (.braces [1]), .addr "p" "c", .placementNew "p2" cC "p" (.braces [2])] =
      [.constructTwice "p"] := by
  decide

/-! ### Accepted and undefined: the mark says initialized, the object
model says no object, or a dead one -/

/-- [ptr.launder]/6 made profile-conformant: the const `X` is destroyed
before the storage is reused, as §4.6 requires, and `p->n` is read. The
profile accepts; the Standard makes it undefined, since `p` points to
the old object and a const complete object is not transparently
replaceable. -/
def launderExample : Trace :=
  [ .newObject "p" (.const cX) (.braces [3]), .member "pn" "p" 0, .read "a" "pn"
  , .destroy "p", .cast "q" cX "p", .placementNew "p2" cX "q" (.braces [5])
  , .member "pn2" "p" 0, .read "b" "pn2" ]

theorem launder_example_accepted : accepts model plain launderExample = true := by decide

theorem launder_example_undefined : run model launderExample = .undefined .outsideLifetime := by decide

/-- The same through `std::launder` is defined. The profile has no
opinion on `std::launder`; the Standard requires it here. -/
theorem launder_example_laundered :
    accepts model plain (launderExample.dropLast.dropLast ++ [.launder "l" "p", .member "ln" "l" 0, .read "b" "ln"]) =
      true ∧
    ((run model (launderExample.dropLast.dropLast ++ [.launder "l" "p", .member "ln" "l" 0, .read "b" "ln"])).state?.bind
      (·.val? "b")) = some (.int 5) := by
  decide

/-- A base class subobject destroyed and recreated as a complete `B`:
the profile marks `*pb` destroyed then initialized and `d` untouched;
the Standard ends `d`'s lifetime when its base's storage is reused by an
object not nested within it, so `d.d` is undefined. -/
def baseReplaced : Trace :=
  [ .var "d" cD (.braces [1, 2]), .addr "pd" "d", .member "pb" "pd" 0
  , .destroy "pb", .placementNew "nb" cB "pb" (.braces [7])
  , .addr "pd2" "d", .member "pdd" "pd2" 1, .read "v" "pdd" ]

theorem base_replaced_accepted : accepts model plain baseReplaced = true := by decide

theorem base_replaced_undefined : run model baseReplaced = .undefined .outsideLifetime := by decide

/-- `U u = {7}; auto v = u.s;`: the union is initialized, so the profile
accepts the read of either member; the Standard makes reading the
inactive member undefined. -/
def unionInactive : Trace := [.var "u" cU (.braces [7]), .addr "pu" "u", .member "ps" "pu" 1, .read "v" "ps"]

theorem union_inactive_accepted : accepts model plain unionInactive = true := by decide

theorem union_inactive_undefined : run model unionInactive = .undefined .inactiveMember := by decide

/-- `int x = 1; auto* q = reinterpret_cast<Pair*>(&x); auto v = q->a;`:
a cast preserves the mark (§6), so the profile accepts; no `Pair` exists
and an `int` is not type-accessible through a `short` glvalue. The paper
leaves casts to another profile; the initialization guarantee alone does
not say the read is of an object. -/
def typePun : Trace := [.var "x" int (.scalar 1), .addr "p" "x", .cast "q" cPair "p", .member "qa" "q" 0, .read "v" "qa"]

theorem type_pun_accepted : accepts model plain typePun = true := by decide

theorem type_pun_undefined : run model typePun = .undefined .typeInaccessible := by decide

/-- A byte buffer, §4.8's pattern without `now_init`: bytes stored, read
as a `Pair`, bytes stored again, read as an `int`. The profile holds the
buffer initialized after the first `memcpy`-free fill? No: bytes stored
through `unsigned char` leave the mark, so the buffer must be
`[[uninit]]` and the reads need `now_init`. With `now_init` at each read
the profile accepts; the second read is undefined, since the `Pair`
created at the first occupies the storage and nothing created an `int`
([intro.object]/13); `std::start_lifetime_as`, which the paper does not
mention, is what makes it defined. -/
def bufferReuse : Trace :=
  [ .var "buf" uchar .default false 8, .addr "b" "buf", .storeBytes "b" [1, 0, 2, 0]
  , .nowInit "b1" "b", .cast "q" cPair "b1", .member "qa" "q" 0, .read "v" "qa"
  , .storeBytes "b" [9, 0, 0, 0]
  , .cast "r" int "b1", .read "w" "r" ]

theorem buffer_reuse_accepted : accepts model { plain with uninit := ["buf"] } bufferReuse = true := by decide

theorem buffer_reuse_undefined : run model bufferReuse = .undefined .typeInaccessible := by decide

theorem buffer_reuse_start_lifetime_as_defined :
    ((run model (bufferReuse.dropLast.dropLast ++ [.startLifetimeAs "r" int "b", .read "w" "r"])).state?.bind
      (·.val? "w")) = some (.int 9) := by
  decide

/-- `std::start_lifetime_as`, unannotated: `malloc` then
`start_lifetime_as<Pair>` then a read. The result is a pointer to
initialized memory by the paper's default for a function returning a
pointer (§4.3), so the profile accepts; the bytes are indeterminate and
the read undefined. -/
def startLifetimeAsIndeterminate : Trace :=
  [.malloc "m" 4, .startLifetimeAs "p" cPair "m", .member "pa" "p" 0, .read "v" "pa"]

theorem start_lifetime_as_unannotated_accepted : accepts model plain startLifetimeAsIndeterminate = true := by decide

theorem start_lifetime_as_unannotated_undefined :
    run model startLifetimeAsIndeterminate = .undefined .indeterminateValue := by decide

/-- `std::start_lifetime_as`, annotated `[[ref_to_uninit]]`: the
indeterminate case is rejected, and so is the case the function exists
for, `int x = …; auto* r = start_lifetime_as<Pair>(&x); r->a`, which is
defined with the `int`'s bytes. Under this reading the function is
unusable without `now_init`. -/
def annotated : Annotations := { plain with rules := { startLifetimeAs := .refToUninit } }

def startLifetimeAsDefined : Trace :=
  [.var "x" int (.scalar 0x00020001), .addr "p" "x", .startLifetimeAs "r" cPair "p", .member "ra" "r" 0, .read "v" "ra"]

theorem start_lifetime_as_annotated :
    accepts model annotated startLifetimeAsIndeterminate = false ∧
    accepts model annotated startLifetimeAsDefined = false ∧
    hazard model startLifetimeAsDefined = false := by
  decide

/-! ### Rejected and defined: the mark says uninitialized, the object
model says a live object with a determinate value -/

/-- `Point p [[uninit]]; p.x = 7; p.y = 9; auto v = p.x;`: banned by
§5.4, defined by [basic.life]/2 and [basic.indet]/1, both members
written before they are read. -/
def pointAssigned : Trace :=
  [ .var "p" cPoint, .addr "pp" "p", .member "px" "pp" 0, .member "py" "pp" 1
  , .write "px" 7, .write "py" 9, .read "v" "px" ]

theorem point_assigned_rejected : accepts model { plain with uninit := ["p"] } pointAssigned = false := by decide

theorem point_assigned_defined : hazard model pointAssigned = false := by decide

/-- `U u [[uninit]]; u.i = 1; auto v = u.i;`: banned by §5.6, and
exactly the assignment [class.union.general]/5 makes begin the member's
lifetime. -/
def unionAssigned : Trace := [.var "u" cU, .addr "pu" "u", .member "pi" "pu" 0, .write "pi" 1, .read "v" "pi"]

theorem union_assigned_rejected : accepts model { plain with uninit := ["u"] } unionAssigned = false := by decide

theorem union_assigned_defined : hazard model unionAssigned = false := by decide

/-- `C c{1}; std::construct_at(&c, 2); auto v = c.i;`: "constructed once
only" (§8.2) bans it; the Standard reuses the storage, ends the old
object's lifetime without a destructor call ([basic.life]/6), replaces it
transparently, and reads 2. -/
def constructOverLive : Trace :=
  [.var "c" cC (.braces [1]), .addr "p" "c", .placementNew "p2" cC "p" (.braces [2]), .addr "p3" "c",
   .member "ci" "p3" 0, .read "v" "ci"]

theorem construct_over_live_rejected : accepts model plain constructOverLive = false := by decide

theorem construct_over_live_defined :
    hazard model constructOverLive = false ∧ ((run model constructOverLive).state?.bind (·.val? "v")) = some (.int 2) := by
  decide

/-! ### Where the two agree -/

/-- `int x; auto v = x;` is rejected and erroneous; with `[[uninit]]`
and a write first it is accepted and defined. -/
theorem uninit_read_agree :
    accepts model plain [.var "x" int, .addr "p" "x", .read "v" "p"] = false ∧
    hazard model [.var "x" int, .addr "p" "x", .read "v" "p"] = true ∧
    accepts model { plain with uninit := ["x"] } [.var "x" int, .addr "p" "x", .write "p" 1, .read "v" "p"] = true ∧
    hazard model [.var "x" int, .addr "p" "x", .write "p" 1, .read "v" "p"] = false := by
  decide

/-- `int* p = new int; auto v = *p;`: the pointer refers to uninitialized
memory, so the read is rejected (§2, §4.1), and undefined. -/
theorem new_int_agree :
    accepts model plain [.newObject "p" int, .read "v" "p"] = false ∧
    hazard model [.newObject "p" int, .read "v" "p"] = true := by
  decide

/-- `T t{}; auto v = t.x;` with `T() {}`: §5.1 makes `T` ill-formed
unless `x` is `[[uninit]]`, and then the read is rejected; the run is
erroneous. Without the member annotation the class itself is the
violation. -/
theorem user_ctor_agree :
    check model { plain with uninitMembers := [] } [] = [.constructorLeavesMember cT 0] ∧
    accepts model plain [.var "t" cT .value, .addr "p" "t", .member "px" "p" 0, .read "v" "px"] = false ∧
    hazard model [.var "t" cT .value, .addr "p" "t", .member "px" "p" 0, .read "v" "px"] = true := by
  decide

/-- The attributes change no execution: `now_init` is the identity on
its pointer, and the checker reads the trace the machine runs. -/
theorem now_init_identity (m : Model) (s : State) (x q : String) :
    step m s (.nowInit x q) = (ptr s q >>= fun p => .defined (s.setPtr x p)) := by
  rfl

/-! ### The four disagreements, as a table

The profile's mark against the object model's two notions, on the
traces above: accepted and undefined where the mark says initialized
and the Standard says the object is dead (`launderExample`,
`baseReplaced`), was never active (`unionInactive`), or does not exist
(`typePun`, `bufferReuse`, `startLifetimeAsIndeterminate`); rejected and
defined where the mark says uninitialized and the Standard has a live
object with a determinate value (`pointAssigned`, `unionAssigned`,
`constructOverLive`, `startLifetimeAsDefined` under the annotated
reading). -/

/-- The accepted traces with a hazard. -/
def acceptedHazards : List (Annotations × Trace) :=
  [ (plain, launderExample), (plain, baseReplaced), (plain, unionInactive), (plain, typePun)
  , ({ plain with uninit := ["buf"] }, bufferReuse), (plain, startLifetimeAsIndeterminate) ]

theorem accepted_hazards :
    acceptedHazards.all (fun (a, t) => accepts model a t && hazard model t) = true := by decide

/-- The rejected traces without one. -/
def rejectedSafe : List (Annotations × Trace) :=
  [ ({ plain with uninit := ["p"] }, pointAssigned), ({ plain with uninit := ["u"] }, unionAssigned)
  , (plain, constructOverLive), (annotated, startLifetimeAsDefined) ]

theorem rejected_safe :
    rejectedSafe.all (fun (a, t) => !accepts model a t && !hazard model t) = true := by decide

/-- The profile's guarantee, "no use of uninitialized objects" (§8.2),
does not hold on the fragment: an accepted trace has the hazard. -/
theorem guarantee_fails : ∃ a t, accepts model a t = true ∧ hazard model t = true :=
  ⟨plain, unionInactive, by decide⟩

end Overload.Object.P4222
