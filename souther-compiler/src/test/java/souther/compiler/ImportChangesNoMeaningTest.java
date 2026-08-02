package souther.compiler;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Located;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An import lets a library name be written without its qualifier and changes nothing else. So a
 * module written with the qualifier and the same module written through an import must compile to
 * the same thing: the same classes, the same reports, and — where the two are run — the same answer.
 *
 * <p>This is the one invariant behind a defect that has landed nine times in one change. A pass that
 * asks which declaration a call reaches by looking at how it is spelled misses when an import
 * dropped the qualifier, and it misses <i>silently</i>: a table keyed by names answers a name it has
 * not got with nothing, which every one of those passes reads as "not one of mine". The failures
 * that follow name something else — a parameter that is not determined, an invariant left to run
 * time, a constant not folded — so none of them points back here.
 *
 * <p>A pair per pass that keys on a name. Adding a pass that does means adding a pair.
 */
class ImportChangesNoMeaningTest {

    /**
     * One program written both ways: the qualifier, and an import that elides it.
     *
     * <p>{@code recordedText} is what a class that stores the program's own text is expected to
     * shrink by — an invariant carries its clause so a violation can quote it, and the clause is
     * shorter by the qualifiers the import elided. Stated as a number rather than skipped, so a
     * class that shrinks for any other reason is a failure.
     */
    private record Pair(String what, String recordedText, String qualified, String imported) {}

    private static final List<Pair> PAIRS = List.of(
            new Pair("a helper's parameter is typed by the declaration a call reaches", "", """
                    module demo
                    data In = { s: String }
                    data Out = { n: Int }
                    let size (s) = String.length(s)
                    behavior go : (i: In) -> Out constructs Out
                    let go (i) = Out { n = size(i.s) }
                    """, """
                    module demo
                    import String ( length )
                    data In = { s: String }
                    data Out = { n: Int }
                    let size (s) = length(s)
                    behavior go : (i: In) -> Out constructs Out
                    let go (i) = Out { n = size(i.s) }
                    """),
            new Pair("a guard discharges an invariant written the other way", "demo.NonEmpty=7", """
                    module demo
                    data Empty
                    data NonEmpty = String
                        invariant String.length(value) > 0
                    data In = { s: String }
                    data Out = { v: NonEmpty }
                    behavior go : (i: In) -> Out | Empty constructs Out, NonEmpty, Empty
                    let go (i) = {
                        guard String.length(i.s) > 0
                            else Empty
                        Out { v = NonEmpty(i.s) }
                    }
                    """, """
                    module demo
                    import String ( length )
                    data Empty
                    data NonEmpty = String
                        invariant length(value) > 0
                    data In = { s: String }
                    data Out = { v: NonEmpty }
                    behavior go : (i: In) -> Out | Empty constructs Out, NonEmpty, Empty
                    let go (i) = {
                        guard length(i.s) > 0
                            else Empty
                        Out { v = NonEmpty(i.s) }
                    }
                    """),
            new Pair("a size bound an invariant lowers to a constraint", "demo.Several=5", """
                    module demo
                    data TooFew
                    data Several = List<Int>
                        invariant List.length(value) >= 2
                    data In = { xs: List<Int> }
                    data Out = { v: Several }
                    behavior go : (i: In) -> Out | TooFew constructs Out, Several, TooFew
                    let go (i) = {
                        guard List.length(i.xs) >= 2
                            else TooFew
                        Out { v = Several(i.xs) }
                    }
                    """, """
                    module demo
                    import List ( length )
                    data TooFew
                    data Several = List<Int>
                        invariant length(value) >= 2
                    data In = { xs: List<Int> }
                    data Out = { v: Several }
                    behavior go : (i: In) -> Out | TooFew constructs Out, Several, TooFew
                    let go (i) = {
                        guard length(i.xs) >= 2
                            else TooFew
                        Out { v = Several(i.xs) }
                    }
                    """),
            new Pair("a constant folded out of an invariant", "demo.Code=14", """
                    module demo
                    data Code = String
                        invariant String.length(value) == String.length("AB")
                    data In = { s: String }
                    data Out = { c: Code }
                    data Bad
                    behavior go : (i: In) -> Out | Bad constructs Out, Code, Bad
                    let go (i) = {
                        guard Code(i.s) as c
                            else Bad
                        Out { c = c }
                    }
                    """, """
                    module demo
                    import String ( length )
                    data Code = String
                        invariant length(value) == length("AB")
                    data In = { s: String }
                    data Out = { c: Code }
                    data Bad
                    behavior go : (i: In) -> Out | Bad constructs Out, Code, Bad
                    let go (i) = {
                        guard Code(i.s) as c
                            else Bad
                        Out { c = c }
                    }
                    """),
            new Pair("a recursive helper's call graph", "", """
                    module demo
                    data In = { xs: List<Int> }
                    data Out = { n: Int }
                    let total (xs: List<Int>) : Int = List.fold((a, x) -> a + x, 0, xs)
                    behavior go : (i: In) -> Out constructs Out
                    let go (i) = Out { n = total(i.xs) }
                    """, """
                    module demo
                    import List ( fold )
                    data In = { xs: List<Int> }
                    data Out = { n: Int }
                    let total (xs: List<Int>) : Int = fold((a, x) -> a + x, 0, xs)
                    behavior go : (i: In) -> Out constructs Out
                    let go (i) = Out { n = total(i.xs) }
                    """),
            new Pair("a library function handed over by name", "", """
                    module demo
                    data In = { xs: List<String> }
                    data Out = { ys: List<String> }
                    behavior go : (i: In) -> Out constructs Out
                    let go (i) = Out { ys = List.map(String.trim, i.xs) }
                    """, """
                    module demo
                    import String ( trim )
                    data In = { xs: List<String> }
                    data Out = { ys: List<String> }
                    behavior go : (i: In) -> Out constructs Out
                    let go (i) = Out { ys = List.map(trim, i.xs) }
                    """));

    @Test
    void anImportChangesNothingButTheSpelling() {
        for (Pair pair : PAIRS) {
            Compiler.Compiled q = Compiler.compileWithWarnings(pair.qualified());
            Compiler.Compiled b = Compiler.compileWithWarnings(pair.imported());
            assertEquals(names(q), names(b), pair.what() + ": the classes differ");
            assertEquals(codes(q), codes(b), pair.what() + ": the reports differ");
            assertEquals(pair.recordedText(), shrinkage(q, b),
                    pair.what() + ": the emitted code differs");
        }
    }

    private static Set<String> names(Compiler.Compiled c) {
        return c.classes().keySet();
    }

    private static List<String> codes(Compiler.Compiled c) {
        return c.warnings().stream().map(Diagnostic::code).sorted().toList();
    }

    /**
     * How much smaller each emitted class got when the qualifiers were elided. A pass that read the
     * spelling produces different code — an invariant it could not discharge is a check it emits, a
     * constant it could not fold is an expression it emits — and the byte count says so without
     * pinning the bytes themselves, which differ in the line numbers the two spellings sit on.
     *
     * <p>The module's metadata class is left out: it carries the module's source so an importer can
     * read a published body back, and the two sources really are different text. Every other class
     * is expected to be byte-for-byte the same size unless it records the program's text too.
     */
    private static String shrinkage(Compiler.Compiled qualified, Compiler.Compiled imported) {
        return qualified.classes().entrySet().stream()
                .filter(e -> !e.getKey().endsWith(".$Module"))
                .sorted(java.util.Map.Entry.comparingByKey())
                .filter(e -> e.getValue().length != imported.classes().get(e.getKey()).length)
                .map(e -> e.getKey() + "="
                        + (e.getValue().length - imported.classes().get(e.getKey()).length))
                .collect(Collectors.joining(","));
    }
}
