package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import souther.compiler.diag.Located;
import souther.compiler.diag.Severity;

/**
 * An import lets a library name be written without its qualifier (spec §stdlib). What it brings in
 * is one table, and what each name means where it is written is answered once, with the bindings in
 * force. So a name an import brought in reads the same wherever an expression may be written, and a
 * binding of the same name wins over it everywhere.
 */
class CompileImportedNameTest {

    @Test
    void anImportedNameIsAValue() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo
                import String ( isEmpty )
                data In = { xs: List<String> }
                data Out = { ok: Bool }
                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { ok = List.all(isEmpty, i.xs) }
                """));
    }

    @Test
    void anImportedNameReadsInsideAnAttemptedConstruction() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo
                import String ( trim )
                data Empty
                data Name = String
                    invariant String.length(value) > 0
                data In = { s: String }
                data Out = { t: String }
                behavior go : (i: In) -> Out | Empty constructs Out, Name, Empty
                let go (i) = {
                    guard Name(i.s) as n
                        else Empty
                    Out { t = trim(n.value) }
                }
                """));
    }

    @Test
    void anImportedNameReadsInAnExampleRow() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo
                import String ( trim )
                data In = { s: String }
                data Out = { t: String }
                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { t = trim(i.s) }
                example go
                    | "trims" : (In { s = " a " }) -> Out { t = "a" }
                """));
    }

    @Test
    void aParameterOfTheSameNameWinsOverAnImport() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo
                import List ( map )
                data In = { n: Int }
                data Out = { m: Int }
                let use (map: (Int) -> Int, x: Int) = map(x)
                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { m = use((k) -> k + 1, i.n) }
                """));
    }

    @Test
    void aLocalLetOfTheSameNameWinsOverAnImport() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo
                import String ( trim )
                data In = { s: String }
                data Out = { t: String }
                behavior go : (i: In) -> Out constructs Out
                let go (i) = {
                    let trim: (String) -> String = (s) -> s ++ "!"
                    Out { t = trim(i.s) }
                }
                """));
    }

    @Test
    void aNameTheLibraryDoesNotHaveIsRejected() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile("""
                module demo
                import String ( shout )
                data In = { s: String }
                data Out = { t: String }
                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { t = i.s }
                """));
        assertTrue(e.getMessage().contains("shout"), e.getMessage());
    }

    @Test
    void aNameExposedFromTwoLibrariesIsRejected() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile("""
                module demo
                import List ( map )
                import Option ( map )
                data In = { xs: List<Int> }
                data Out = { ys: List<Int> }
                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { ys = i.xs }
                """));
        assertTrue(e.getMessage().contains("map"), e.getMessage());
    }

    /**
     * An import lets a name be written without its qualifier; it does not rename it. A report quotes
     * and underlines what the source has, and a table keyed by a declaration's name finds the
     * declaration — two questions, and writing one answer over the other loses the other.
     */
    @Test
    void aReportQuotesTheImportedSpelling() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile("""
                module demo
                import String ( trim )
                data In = { n: Int }
                data Out = { t: String }
                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { t = trim(i.n) }
                """));
        assertTrue(e.getMessage().contains("of trim:"), e.getMessage());
        assertTrue(!e.getMessage().contains("String.trim"), e.getMessage());
    }

    /**
     * A name that was answered is not an unknown one, whatever it turns out to denote. A composition
     * is answered and is still not a value — its requirements are inferred from its stages, so a
     * body holding one would take on a set that changes when an upstream stage does.
     */
    @Test
    void aNameThatDenotesSomethingUnusableSaysWhatItDenotes() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile("""
                module demo exposing ( In, Mid, Out, one, two, chain : Out, go )
                data In = { n: Int }
                data Mid = { n: Int }
                data Out = { n: Int }
                behavior one : (i: In) -> Mid constructs Mid
                let one (i) = Mid { n = i.n }
                behavior two : (m: Mid) -> Out constructs Out
                let two (m) = Out { n = m.n }
                behavior chain = one >-> two
                behavior go : (i: In) -> Out
                let go (i) = {
                    let f = chain
                    f(i)
                }
                """));
        assertTrue(e.getMessage().contains("is a behavior"), e.getMessage());
    }

    /** A behavior handed to a combinator is the behavior: what a Java implementation replaces. */
    @Test
    void aBehaviorHandedOverReachesTheBehavior() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo
                data In = { xs: List<Int> }
                data Out = { ys: List<Int> }
                behavior twice : (n: Int) -> Int
                let twice (n) = n * 2
                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { ys = List.map(twice, i.xs) }
                """));
    }

    /**
     * A helper's parameter takes its type from a call whose parameter type is declared, and which
     * declaration a call reaches is not decided by whether an import let the name be written bare.
     */
    @Test
    void aParameterIsTypedByADeclarationReachedThroughAnImport() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo
                import String ( length )
                data In = { s: String }
                data Out = { n: Int }
                let size (s) = length(s)
                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { n = size(i.s) }
                """));
    }

    /**
     * An invariant and the guards on the path to a construction are compared by what each call
     * reaches, so a clause written bare and a guard written qualified are one statement — and the
     * invariant is discharged rather than left to run time.
     */
    @Test
    void anInvariantDischargesThroughAnImportedName() {
        Compiler.Compiled c = Compiler.compileWithWarnings("""
                module demo
                import String ( length )
                data Empty
                data NonEmpty = String
                    invariant length(value) > 0
                data In = { s: String }
                data Out = { v: NonEmpty }
                behavior go : (i: In) -> Out | Empty constructs Out, NonEmpty, Empty
                let go (i) = {
                    guard String.length(i.s) > 0
                        else Empty
                    Out { v = NonEmpty(i.s) }
                }
                """);
        assertEquals(0, c.warnings().stream()
                        .filter(d -> d.severity() == Severity.WARNING).count(),
                c.warnings().toString());
    }

    @Test
    void anImportThatCollidesWithADataIsRejected() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile("""
                module demo
                import List ( map )
                data map
                data In = { n: Int }
                data Out = { m: Int }
                behavior go : (i: In) -> Out constructs Out
                let go (i) = Out { m = i.n }
                """));
        assertTrue(e.getMessage().contains("map"), e.getMessage());
    }

    @Test
    void aFieldOfABindingNamedLikeAQualifierIsAField() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo
                data Holder = { empty: Bool }
                data In = { m: Holder }
                data Out = { ok: Bool }
                behavior go : (i: In) -> Out constructs Out
                let go (i) = {
                    let Map = i.m
                    Out { ok = Map.empty }
                }
                """));
    }
}
