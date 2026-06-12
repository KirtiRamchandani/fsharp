module FSharpChecker.SemanticClassificationRegressions

open Xunit
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.EditorServices
open FSharp.Compiler.Text
open FSharp.Test.ProjectGeneration
open FSharp.Test.ProjectGeneration.Helpers

#nowarn "57"

/// Get semantic classification items for a single-file source using the transparent compiler.
let getClassifications (source: string) =
    let fileName, snapshot, checker = singleFileChecker source
    let results = checker.ParseAndCheckFileInProject(fileName, snapshot) |> Async.RunSynchronously
    let checkResults = getTypeCheckResult results
    checkResults.GetSemanticClassification(None, RelatedSymbolUseKind.All)

/// Extract the source substring covered by a classification item's range (single-line ranges).
let private substringOfRange (source: string) (r: Range) =
    let lines = source.Replace("\r\n", "\n").Split('\n')
    let line = lines[r.StartLine - 1]
    line.Substring(r.StartColumn, r.EndColumn - r.StartColumn)

/// (#15290 regression) Copy-and-update record fields must not be classified as type names.
/// Before the fix, Item.Types was registered with mWholeExpr and ItemOccurrence.Use, producing
/// a wide type classification that overshadowed the correct RecordField classification.
[<Fact>]
let ``Copy-and-update field should not be classified as type name`` () =
    let source =
        """
module Test

type MyRecord = { ValidationErrors: string list; Name: string }
let x: MyRecord = { ValidationErrors = []; Name = "" }
let updated = { x with ValidationErrors = [] }
"""

    let items = getClassifications source

    // Line 6 contains "{ x with ValidationErrors = [] }"
    // "ValidationErrors" starts around column 23 (after "let updated = { x with ")
    // It should be RecordField, NOT ReferenceType/ValueType.
    let fieldLine = 6

    let fieldItems =
        items
        |> Array.filter (fun item ->
            item.Range.StartLine = fieldLine
            && item.Type = SemanticClassificationType.RecordField)

    Assert.True(fieldItems.Length > 0, "Expected RecordField classification on the copy-and-update line")

    // No type classification should cover the field name on that line with a visible range
    let typeItemsCoveringField =
        items
        |> Array.filter (fun item ->
            item.Range.StartLine <= fieldLine
            && item.Range.EndLine >= fieldLine
            && item.Range.Start <> item.Range.End
            && (item.Type = SemanticClassificationType.ReferenceType
                || item.Type = SemanticClassificationType.ValueType
                || item.Type = SemanticClassificationType.Type))

    Assert.True(
        typeItemsCoveringField.Length = 0,
        sprintf
            "No type classification should cover the copy-and-update line, but found: %A"
            (typeItemsCoveringField |> Array.map (fun i -> i.Range, i.Type))
    )

/// (#16621) Helper: assert UnionCase classifications on expected lines.
/// Each entry is (line, expectedCount, maxRangeWidth).
/// maxRangeWidth guards against dot-coloring regressions (range including "x." prefix).
let expectUnionCaseClassifications source (expectations: (int * int * int) list) =
    let items = getClassifications source

    for (line, expectedCount, maxWidth) in expectations do
        let found =
            items
            |> Array.filter (fun item ->
                item.Type = SemanticClassificationType.UnionCase
                && item.Range.StartLine = line)

        Assert.True(
            found.Length = expectedCount,
            sprintf "Line %d: expected %d UnionCase classification(s), got %d. Items on that line: %A" line expectedCount found.Length
                (items
                 |> Array.filter (fun i -> i.Range.StartLine = line)
                 |> Array.map (fun i -> i.Range.StartColumn, i.Range.EndColumn, i.Type))
        )

        for item in found do
            let width = item.Range.EndColumn - item.Range.StartColumn

            Assert.True(
                width <= maxWidth,
                sprintf "Line %d: UnionCase range is too wide (%d columns, max %d): %A" line width maxWidth item.Range
            )

/// (#16621 regression) Union case tester classification must not include the dot.
[<Fact>]
let ``Union case tester classification range should not include dot`` () =
    let source =
        """
module Test

type Shape = Circle | Square | HyperbolicCaseWithLongName
let s = Circle
let r1 = s.IsCircle
let r2 = s.IsHyperbolicCaseWithLongName
"""
    //                        line, count, maxWidth
    expectUnionCaseClassifications source [ (6, 1, 8); (7, 1, 30) ]

/// (#16621) Union case tester classification across scenarios: chaining, RequireQualifiedAccess,
/// multiple testers on one line, and self-referential members.
[<Fact>]
let ``Union case tester classification across scenarios`` () =
    let source =
        """
module Test

type Shape = Circle | Square
let s = Circle
let chained = s.IsCircle.ToString()
let both = s.IsCircle && s.IsSquare

[<RequireQualifiedAccess>]
type Token = Ident of string | Keyword
let t = Token.Keyword
let rqa = t.IsIdent

type Animal =
    | Cat
    | Dog
    member this.IsFeline = this.IsCat
"""
    //                        line, count, maxWidth
    expectUnionCaseClassifications source
        [ (6, 1, 8)    // s.IsCircle.ToString() — chained
          (7, 2, 8)    // s.IsCircle && s.IsSquare — two on same line
          (12, 1, 7)   // t.IsIdent — RequireQualifiedAccess
          (17, 1, 5) ] // this.IsCat — self-referential member

/// (#18009 regression) Static method on a generic type with a *qualified* type argument
/// must still classify the type name as a type.
[<Fact>]
let ``Static method on generic type should classify type name as type`` () =
    let source =
        """
module Test

type MyType<'T> =
    static member S = 1

let _ = MyType<int>.S
let _ = MyType<System.Int32>.S
"""

    let items = getClassifications source

    let isMyTypeRefOnLine line (item: SemanticClassificationItem) =
        item.Type = SemanticClassificationType.ReferenceType
        && item.Range.StartLine = line
        && item.Range.StartColumn = 8
        && item.Range.EndColumn = 14

    let unqualified = items |> Array.filter (isMyTypeRefOnLine 7)
    Assert.True(
        unqualified.Length = 1,
        sprintf
            "Expected exactly one ReferenceType classification for MyType on line 7, got: %A"
            (items |> Array.filter (fun i -> i.Range.StartLine = 7)
                   |> Array.map (fun i -> i.Range.StartColumn, i.Range.EndColumn, i.Type))
    )

    let qualified = items |> Array.filter (isMyTypeRefOnLine 8)
    Assert.True(
        qualified.Length = 1,
        sprintf
            "Expected exactly one ReferenceType classification for MyType on line 8, got: %A"
            (items |> Array.filter (fun i -> i.Range.StartLine = 8)
                   |> Array.map (fun i -> i.Range.StartColumn, i.Range.EndColumn, i.Type))
    )

/// (#18009 follow-up) Accepting ItemOccurrence.InvalidUse in LegitTypeOccurrence must
/// not cause unresolved identifiers to be classified as types.
[<Fact>]
let ``Undeclared identifier in expression position is not classified as a type`` () =
    let source =
        """
module Test

let _ = NotDeclaredAnywhere.S
"""

    let items = getClassifications source

    let badSpans =
        items
        |> Array.filter (fun item ->
            item.Range.StartLine = 4
            && item.Range.StartColumn = 8
            && item.Range.EndColumn = 27
            && (item.Type = SemanticClassificationType.ReferenceType
                || item.Type = SemanticClassificationType.ValueType
                || item.Type = SemanticClassificationType.Type))

    Assert.True(
        badSpans.Length = 0,
        sprintf
            "Undeclared identifier should not be classified as a type, but found: %A"
            (badSpans |> Array.map (fun i -> i.Range.StartColumn, i.Range.EndColumn, i.Type))
    )

/// (#16982) Delegate `Invoke` synthesized in a delegate declaration must not be classified as Method.
[<Fact>]
let ``Delegate Invoke in declaration not classified as method`` () =
    let source = """
type MyDelegate = delegate of int -> string
"""
    let classifications = getClassifications source
    let invokeMethods =
        classifications
        |> Array.filter (fun c ->
            c.Type = SemanticClassificationType.Method
            && substringOfRange source c.Range = "Invoke")
    Assert.Empty(invokeMethods)

/// (#16982) Negative: at a real call site, `Invoke` must still classify as Method.
[<Fact>]
let ``Delegate Invoke at call site classified as method`` () =
    let source = """
type MyDelegate = delegate of int -> string
let d = MyDelegate(fun i -> string i)
let result = d.Invoke(42)
"""
    let classifications = getClassifications source
    let invokeCallSite =
        classifications
        |> Array.filter (fun c ->
            c.Type = SemanticClassificationType.Method && c.Range.StartLine = 4)
    Assert.NotEmpty(invokeCallSite)

/// (#16982) Generic delegate variant.
[<Fact>]
let ``Generic delegate Invoke not classified as method in decl`` () =
    let source = """
type MyGenDelegate<'T> = delegate of 'T -> 'T
"""
    let classifications = getClassifications source
    let invokeMethods =
        classifications
        |> Array.filter (fun c ->
            c.Type = SemanticClassificationType.Method
            && substringOfRange source c.Range = "Invoke")
    Assert.Empty(invokeMethods)

/// (#16982) The synthesized async-pattern members `BeginInvoke`/`EndInvoke` must also be suppressed in the declaration.
[<Fact>]
let ``BeginInvoke EndInvoke also not classified in decl`` () =
    let source = """
type MyDelegate = delegate of int -> string
"""
    let classifications = getClassifications source
    let asyncInvokeMethods =
        classifications
        |> Array.filter (fun c ->
            c.Type = SemanticClassificationType.Method
            && (let text = substringOfRange source c.Range
                text = "BeginInvoke" || text = "EndInvoke"))
    Assert.Empty(asyncInvokeMethods)

// =====================================================================
// Issue #19905 - F# editor classification cluster (Phase 0 verification)
// Each test below pins down the CURRENT behaviour observed on HEAD.
// Facts that document an unfixed bug are marked [<Fact(Skip = ...)>]
// and will be un-skipped (and inverted) by their corresponding fix sprint.
// =====================================================================

/// (#19905 item 1) Delegate signature must not produce a synthesized Invoke Method classification.
/// Already fixed by #19813. Sibling coverage exists at
/// `Delegate Invoke in declaration not classified as method` above; this is a Phase 0 confirmation.
[<Fact>]
let ``19905 item 1 - delegate sig not classified as method`` () =
    let source =
        """
type SumDelegate = delegate of x: int * y: int -> int
"""
    let items = getClassifications source
    let invokeMethods =
        items
        |> Array.filter (fun c ->
            c.Type = SemanticClassificationType.Method
            && substringOfRange source c.Range = "Invoke")
    Assert.Empty(invokeMethods)

/// (#19905 item 2) Computation expression builder identifier used inside a list comprehension
/// must be classified as ComputationExpression on every occurrence, not as Value/LocalValue.
[<Fact>]
let ``19905 item 2 - CE inside list comp classified as ComputationExpression`` () =
    let source =
        """
module Test
type OptionalBuilder() =
    member _.Zero() = None
    member _.Bind(x, f) = Option.bind f x
    member _.Return(x) = Some x
    member _.ReturnFrom(x) = x
let optional = OptionalBuilder()
let myList = [1; 2; 3]
let myNewList = [
    for i in myList do
        optional {
            return! Some(i+1)
        }
]
"""
    let items = getClassifications source
    // Line 12: "        optional {"
    let ceLine = 12

    let optionalClassifications =
        items
        |> Array.filter (fun c ->
            c.Range.StartLine = ceLine
            && substringOfRange source c.Range = "optional")

    Assert.True(
        optionalClassifications
        |> Array.exists (fun c -> c.Type = SemanticClassificationType.ComputationExpression),
        sprintf "Expected `optional` on line %d to have a ComputationExpression classification, but got: %A"
            ceLine (optionalClassifications |> Array.map (fun c -> c.Type)))

    // And ensure no Value/LocalValue paints over the same span (would still
    // visually wash out the CE colour in VS).
    Assert.True(
        optionalClassifications
        |> Array.forall (fun c ->
            c.Type <> SemanticClassificationType.Value
            && c.Type <> SemanticClassificationType.LocalValue),
        sprintf "`optional` on line %d should not have a Value/LocalValue classification: %A"
            ceLine (optionalClassifications |> Array.map (fun c -> c.Type)))

/// (#19905 item 2 negative) Plain `async { .. }` outside a comprehension still classifies as CE.
[<Fact>]
let ``19905 item 2 negative - plain CE classification unchanged`` () =
    let source =
        """
module Test
let _ = async { return 1 }
"""
    let items = getClassifications source
    Assert.True(
        items
        |> Array.exists (fun c ->
            c.Range.StartLine = 3
            && substringOfRange source c.Range = "async"
            && c.Type = SemanticClassificationType.ComputationExpression),
        "`async` should still classify as ComputationExpression")

/// (#19905 item 3) Generic static method call `Type.Method<int>()` must not emit a Method
/// classification covering the `<int>` type-argument text.
[<Fact>]
let ``19905 item 3 - generic static method does not classify type args as method`` () =
    let source =
        """
module Test
type MyType() =
    static member Method<'a>() = Unchecked.defaultof<'a>
    static member Method2<'a, 'b>() = Unchecked.defaultof<'a>, Unchecked.defaultof<'b>
let x = MyType.Method<int>()
let y, z = MyType.Method2<int, string>()
"""
    let items = getClassifications source
    // Line 6: "let x = MyType.Method<int>()"
    //         "MyType" ends at col 14, ".Method" ends at col 21, "<int>" ends at col 26.
    let badL6 =
        items
        |> Array.filter (fun c ->
            c.Range.StartLine = 6
            && (c.Type = SemanticClassificationType.Method
                || c.Type = SemanticClassificationType.Function)
            && c.Range.EndColumn > 21)
    Assert.True(
        badL6.Length = 0,
        sprintf "No Method/Function classification on line 6 should extend past column 21 (end of 'Method'). Found: %A"
            (badL6 |> Array.map (fun c -> c.Range.StartColumn, c.Range.EndColumn, c.Type)))
    // Line 7: "let y, z = MyType.Method2<int, string>()"
    //         ".Method2" ends at col 25, "<int, string>" ends at col 38.
    let badL7 =
        items
        |> Array.filter (fun c ->
            c.Range.StartLine = 7
            && (c.Type = SemanticClassificationType.Method
                || c.Type = SemanticClassificationType.Function)
            && c.Range.EndColumn > 25)
    Assert.True(
        badL7.Length = 0,
        sprintf "No Method/Function classification on line 7 should extend past column 25 (end of 'Method2'). Found: %A"
            (badL7 |> Array.map (fun c -> c.Range.StartColumn, c.Range.EndColumn, c.Type)))

/// (#19905 item 4) Generic constructor `new MailboxProcessor<int * int>(.)` must not emit a
/// type classification covering the `<int * int>` text.
[<Fact>]
let ``19905 item 4 - generic ctor does not classify type args as type`` () =
    let source =
        """
module Test
let myMailbox = new MailboxProcessor<int * int>(fun mbx -> async { return () })
"""
    let items = getClassifications source
    // Line 3: "let myMailbox = new MailboxProcessor<int * int>(.)"
    //         "MailboxProcessor" ends at col 36, "<int * int>" ends at col 47.
    let badTypeSpans =
        items
        |> Array.filter (fun c ->
            c.Range.StartLine = 3
            && (c.Type = SemanticClassificationType.ReferenceType
                || c.Type = SemanticClassificationType.DisposableType
                || c.Type = SemanticClassificationType.ConstructorForReferenceType)
            && c.Range.EndColumn > 36)
    Assert.True(
        badTypeSpans.Length = 0,
        sprintf "No type-like classification on line 3 should extend past column 36 (end of 'MailboxProcessor'). Found: %A"
            (badTypeSpans |> Array.map (fun c -> c.Range.StartColumn, c.Range.EndColumn, c.Type)))
    let badFuncSpans =
        items
        |> Array.filter (fun c ->
            c.Range.StartLine = 3
            && (c.Type = SemanticClassificationType.Method
                || c.Type = SemanticClassificationType.Function)
            && c.Range.StartColumn >= 36
            && c.Range.EndColumn <= 47)
    Assert.True(
        badFuncSpans.Length = 0,
        sprintf "No Method/Function classification should cover the <int * int> punctuation on line 3. Found: %A"
            (badFuncSpans |> Array.map (fun c -> c.Range.StartColumn, c.Range.EndColumn, c.Type)))

/// (#19905 item 5) Open-ended slice `list[0..]` must not emit a Method/Function classification
/// whose range ends at the closing `]`.
[<Fact>]
let ``19905 item 5 - open-ended slice does not classify closing bracket as function`` () =
    let source =
        """
module Test
let list = [1; 2; 3]
let x = list[0..]
"""
    let items = getClassifications source
    // Line 4: "let x = list[0..]"  — closing ']' is at column 17.
    let badSpans =
        items
        |> Array.filter (fun c ->
            c.Range.StartLine = 4
            && (c.Type = SemanticClassificationType.Method
                || c.Type = SemanticClassificationType.Function)
            && c.Range.EndColumn = 17)
    Assert.True(
        badSpans.Length = 0,
        sprintf "No Method/Function classification on line 4 should end at column 17 (the ']'). Found: %A"
            (badSpans |> Array.map (fun c -> c.Range.StartColumn, c.Range.EndColumn, c.Type)))

/// (#19905 item 5 sibling) Open-ended lower slice `list[..2]` must not emit a Method/Function
/// classification whose range starts at the opening `[`.
[<Fact>]
let ``19905 item 5 - open-ended lower slice does not classify opening bracket as function`` () =
    let source =
        """
module Test
let list = [1; 2; 3]
let x = list[..2]
"""
    let items = getClassifications source
    // Line 4: "let x = list[..2]"  — opening '[' is at column 12.
    let badSpans =
        items
        |> Array.filter (fun c ->
            c.Range.StartLine = 4
            && (c.Type = SemanticClassificationType.Method
                || c.Type = SemanticClassificationType.Function)
            && c.Range.StartColumn <= 12
            && c.Range.EndColumn >= 17)
    Assert.True(
        badSpans.Length = 0,
        sprintf "No Method/Function classification on line 4 should span the whole `list[..2]` expression. Found: %A"
            (badSpans |> Array.map (fun c -> c.Range.StartColumn, c.Range.EndColumn, c.Type)))

/// (#19905 item 5 negative) Closed slice `list[0..2]` must not emit a wide Method/Function
/// classification that spans `list[0..2]` either - regression guard to ensure the
/// open-ended slice fix also covers the closed-slice path (same code path in TcIndexingThen).
[<Fact>]
let ``19905 item 5 negative - closed slice classification unchanged`` () =
    let source =
        """
module Test
let list = [1; 2; 3]
let x = list[0..2]
"""
    let items = getClassifications source
    Assert.True(
        items |> Array.exists (fun c -> c.Range.StartLine = 4),
        "Expected at least one classification on line 4 for the closed slice")
    // Line 4: "let x = list[0..2]" — closing ']' is at column 18. No Method/Function
    // classification on line 4 should reach the `]` (it would paint the synthesized
    // GetSlice lookup as Method, identical to the open-ended bug).
    let badSpans =
        items
        |> Array.filter (fun c ->
            c.Range.StartLine = 4
            && (c.Type = SemanticClassificationType.Method
                || c.Type = SemanticClassificationType.Function)
            && c.Range.EndColumn = 18)
    Assert.True(
        badSpans.Length = 0,
        sprintf "No Method/Function classification on line 4 should end at column 18 (the ']'). Found: %A"
            (badSpans |> Array.map (fun c -> c.Range.StartColumn, c.Range.EndColumn, c.Type)))

/// (#19905 item 6) Generic-type static method call `MailboxProcessor<int>.Start(.)` must not
/// emit a Method classification whose range starts before the `.` (i.e., spans the type name).
[<Fact>]
let ``19905 item 6 - generic type static method classifies only the method name`` () =
    let source =
        """
module Test
let mbx = MailboxProcessor<int>.Start(fun mbx -> async { return () })
"""
    let items = getClassifications source
    // Line 3: "let mbx = MailboxProcessor<int>.Start(.)"
    //         "MailboxProcessor" ends at col 26, "<int>" ends at col 31, ".Start" ends at col 37.
    // The Method classification for the call should cover only "Start" (cols 32-37), not the
    // wider "MailboxProcessor<int>.Start" (cols 10-37).
    let badMethodSpans =
        items
        |> Array.filter (fun c ->
            c.Range.StartLine = 3
            && c.Type = SemanticClassificationType.Method
            && c.Range.StartColumn < 32
            && c.Range.EndColumn = 37)
    Assert.True(
        badMethodSpans.Length = 0,
        sprintf "Method classification on line 3 should cover only 'Start' (32-37), not a wider span. Found: %A"
            (badMethodSpans |> Array.map (fun c -> c.Range.StartColumn, c.Range.EndColumn, c.Type)))
    // The type-name classification for MailboxProcessor must not extend past col 26 either.
    let badTypeSpans =
        items
        |> Array.filter (fun c ->
            c.Range.StartLine = 3
            && (c.Type = SemanticClassificationType.ReferenceType
                || c.Type = SemanticClassificationType.DisposableType)
            && c.Range.EndColumn > 26)
    Assert.True(
        badTypeSpans.Length = 0,
        sprintf "No type-like classification on line 3 should extend past column 26 (end of 'MailboxProcessor'). Found: %A"
            (badTypeSpans |> Array.map (fun c -> c.Range.StartColumn, c.Range.EndColumn, c.Type)))

/// (#19905 item 7) `open type X.Y` must not be reported as unused when a static member of the
/// opened type is invoked unqualified below the open.
/// NOTE: on HEAD with this minimal snippet the unused-opens analysis already returns no
/// unused opens. The bug from the issue may require a richer setup; we pin the current
/// passing behaviour so regression of even the simple case is caught.
[<Fact>]
let ``19905 item 7 - open type used by static call is not flagged unused`` () =
    let source =
        """
module Test
module Inner =
    type Helper() =
        static member Greet() = "hi"
open type Inner.Helper
let _ = Greet()
"""
    let fileName, snapshot, checker = singleFileChecker source
    let results = checker.ParseAndCheckFileInProject(fileName, snapshot) |> Async.RunSynchronously
    let checkResults = getTypeCheckResult results
    let lines = source.Replace("\r\n", "\n").Split('\n')
    let getSourceLineStr n =
        if n >= 1 && n <= lines.Length then lines[n - 1] else ""
    let unused =
        UnusedOpens.getUnusedOpens(checkResults, getSourceLineStr)
        |> Async.RunSynchronously
    // The `open type Inner.Helper` is on line 6.
    let unusedOnOpenLine =
        unused
        |> List.filter (fun r -> r.StartLine = 6)
    Assert.True(
        unusedOnOpenLine.IsEmpty,
        sprintf "'open type Inner.Helper' (line 6) must not be flagged unused; got ranges: %A"
            (unusedOnOpenLine |> List.map (fun r -> r.StartLine, r.StartColumn, r.EndColumn)))

/// (#19905 item 7 negative) `open type X.Y` with no usage of any imported member must still
/// be reported as unused. Guards against the fix over-reaching and silencing all `open type`.
[<Fact>]
let ``19905 item 7 negative - open type with no usage is still flagged unused`` () =
    let source =
        """
module Test
module Inner =
    type Helper() =
        static member Greet() = "hi"
open type Inner.Helper
let _ = 1
"""
    let fileName, snapshot, checker = singleFileChecker source
    let results = checker.ParseAndCheckFileInProject(fileName, snapshot) |> Async.RunSynchronously
    let checkResults = getTypeCheckResult results
    let lines = source.Replace("\r\n", "\n").Split('\n')
    let getSourceLineStr n =
        if n >= 1 && n <= lines.Length then lines[n - 1] else ""
    let unused =
        UnusedOpens.getUnusedOpens(checkResults, getSourceLineStr)
        |> Async.RunSynchronously
    let unusedOnOpenLine =
        unused
        |> List.filter (fun r -> r.StartLine = 6)
    Assert.True(
        not unusedOnOpenLine.IsEmpty,
        "'open type Inner.Helper' with no usage of imported members must still be flagged unused")

/// (#19905 item 7 regression-guard) Plain `open Namespace` whose contents are unused must still
/// be reported as unused. Guards against the splitSymbolUses change regressing the namespace case.
[<Fact>]
let ``19905 item 7 regression - unused open System is still flagged unused`` () =
    let source =
        """
module Test
open System
let _ = 1
"""
    let fileName, snapshot, checker = singleFileChecker source
    let results = checker.ParseAndCheckFileInProject(fileName, snapshot) |> Async.RunSynchronously
    let checkResults = getTypeCheckResult results
    let lines = source.Replace("\r\n", "\n").Split('\n')
    let getSourceLineStr n =
        if n >= 1 && n <= lines.Length then lines[n - 1] else ""
    let unused =
        UnusedOpens.getUnusedOpens(checkResults, getSourceLineStr)
        |> Async.RunSynchronously
    let unusedOnOpenLine =
        unused
        |> List.filter (fun r -> r.StartLine = 3)
    Assert.True(
        not unusedOnOpenLine.IsEmpty,
        "'open System' with no usage must still be flagged unused")
