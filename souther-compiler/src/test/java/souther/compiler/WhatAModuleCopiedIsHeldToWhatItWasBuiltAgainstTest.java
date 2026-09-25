package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.msg.ModuleMessage;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A module off the path is held to what its classes copied of another module's declarations, as it
 * is to what they link against (spec {@code [#a-published-module-agrees-with-what-it-copied]}).
 *
 * <p>Each refused case is a dependency rebuilt with something changed that a reader's classes carry
 * a copy of and do not name: a constant folded where it is named, a helper expanded where it is
 * called, a type's invariant checked by a type that includes it. Each accepted case changes the same
 * dependency in a way the reader's classes did not copy, or in a way the copy does not see.
 */
class WhatAModuleCopiedIsHeldToWhatItWasBuiltAgainstTest {

    private static final String READS_THE_CONSTANT = """
            module app.k exposing ( use )
            import lib.k ( limit )
            behavior use : (n: Int) -> Int
            let use (n) = n + limit
            """;

    private static final String CALLS_THE_HELPER = """
            module app.r exposing ( use )
            import lib.p ( capped )
            behavior use : (n: Int) -> Int
            let use (n) = capped(n)
            """;

    /** The issue's first case: a constant is folded into its reader, so a reader built against
     *  `limit = 3` answers with 3 wherever the rest of the program answers with 4. */
    @Test
    void aConstantThatFoldsToAnotherValueIsSaid() {
        Map<String, ClassFileImage> path = builtAgainst("""
                module lib.k exposing ( limit )
                let limit = 3
                """, READS_THE_CONSTANT, """
                module lib.k exposing ( limit )
                let limit = 4
                """);

        assertEquals(new ModuleMessage.ItCopiedAnotherConstant("app.k", "limit", "lib.k", "3", "4"),
                refusal(path, readerOf("app.k")));
    }

    /** The same, with the new `lib.k` compiled here rather than read off the path: what it offers is
     *  what its classes are about to offer. */
    @Test
    void aConstantOfAModuleCompiledHereIsHeldTheSameWay() {
        Map<String, ClassFileImage> path = new HashMap<>(Compiler.compileModules(
                List.of(READS_THE_CONSTANT), ModulePath.of(Compiler.compile("""
                        module lib.k exposing ( limit )
                        let limit = 3
                        """))));
        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module lib.k exposing ( limit )
                        let limit = 4
                        """, readerOf("app.k")), ModulePath.of(path)));

        assertEquals("E1510", refused.diagnostic().code(), refused.getMessage());
        assertEquals(new ModuleMessage.ItCopiedAnotherConstant("app.k", "limit", "lib.k", "3", "4"),
                refused.diagnostic().said());
    }

    /** The issue's second case: a published helper is expanded into its reader, so a reader built
     *  against the bound 10 compares against 10. */
    @Test
    void aHelperWhoseBodyMovedIsSaid() {
        Map<String, ClassFileImage> path = builtAgainst("""
                module lib.p exposing ( capped )
                let capped (n: Int) = if n > 10 then 10 else n
                """, CALLS_THE_HELPER, """
                module lib.p exposing ( capped )
                let capped (n: Int) = if n > 20 then 20 else n
                """);

        assertEquals(new ModuleMessage.ItCopiedAnotherVersion("app.r", "helper", "capped", "lib.p",
                        "closed helper"),
                refusal(path, readerOf("app.r")));
    }

    /** A helper is copied closed over its own module, so a value of that module it names is part of
     *  the copy: the helper's text is the same and what the reader expands is not. */
    @Test
    void aHelperIsHeldToTheValuesOfItsModuleItIsClosedOver() {
        Map<String, ClassFileImage> path = builtAgainst("""
                module lib.p exposing ( capped )
                let cap = 10
                let capped (n: Int) = if n > cap then cap else n
                """, CALLS_THE_HELPER, """
                module lib.p exposing ( capped )
                let cap = 20
                let capped (n: Int) = if n > cap then cap else n
                """);

        assertEquals(new ModuleMessage.ItCopiedAnotherVersion("app.r", "helper", "capped", "lib.p",
                        "closed helper"),
                refusal(path, readerOf("app.r")));
    }

    /** A type's invariant is checked where a type that includes it is built, so the including
     *  module carries its clauses. */
    @Test
    void anInvariantATypeIncludesIsHeldWhereItIsIncluded() {
        Map<String, ClassFileImage> path = builtAgainst("""
                module lib.t exposing ( Base )
                data Base = { total: Int }
                    invariant valid = total >= 1
                """, """
                module app.w exposing ( Wrapped, wrap )
                import lib.t ( Base )
                data Wrapped = { ...Base, w: Int }
                behavior wrap : (n: Int) -> Wrapped
                let wrap (n) = Wrapped { total = 5, w = n }
                """, """
                module lib.t exposing ( Base )
                data Base = { total: Int }
                    invariant valid = total >= 2
                """);

        assertEquals(new ModuleMessage.ItCopiedAnotherVersion("app.w", "invariant", "Base", "lib.t",
                        "clauses"),
                refusal(path, """
                        module main.m
                        import app.w ( wrap, Wrapped )
                        behavior go : (n: Int) -> Wrapped
                        let go (n) = wrap(n)
                        """));
    }

    /** A helper a clause names is expanded into the clause, and so into the construction that checks
     *  it: the module that writes the clause carries the helper. */
    @Test
    void aHelperAClauseNamesIsHeldWhereTheClauseIsChecked() {
        Map<String, ClassFileImage> path = builtAgainst("""
                module lib.q exposing ( atLeastOne )
                let atLeastOne (n: Int) = n >= 1
                """, """
                module app.v exposing ( Count, counted )
                import lib.q ( atLeastOne )
                data Count = { n: Int }
                    invariant valid = atLeastOne(n)
                behavior counted : (x: Int) -> Count
                let counted (x) = Count { n = 5 }
                """, """
                module lib.q exposing ( atLeastOne )
                let atLeastOne (n: Int) = n >= 2
                """);

        assertEquals(new ModuleMessage.ItCopiedAnotherVersion("app.v", "helper", "atLeastOne",
                        "lib.q", "closed helper"),
                refusal(path, """
                        module main.m
                        import app.v ( counted, Count )
                        behavior go : (x: Int) -> Count
                        let go (x) = counted(x)
                        """));
    }

    /**
     * A helper of a third module is expanded into a published one when that one is closed, and a
     * reader expanding the published helper carries both. The reader is the one built against the
     * third's old helper and is the one said. The middle module offers its helper as naming the
     * third's, and its own classes never run the body, so it is not.
     */
    @Test
    void whatClosingAPublishedHelperCopiedIsHeldAgainstTheModuleThatCopiedTheHelper() {
        Map<String, ClassFileImage> path = new HashMap<>();
        Map<String, ClassFileImage> c = Compiler.compile("""
                module lib.c exposing ( h )
                let h (n: Int) = n + 1
                """);
        Map<String, ClassFileImage> b = Compiler.compileModules(List.of("""
                module lib.b exposing ( f )
                import lib.c ( h )
                let f (n: Int) = h(n) * 2
                """), ModulePath.of(c));
        Map<String, ClassFileImage> built = new HashMap<>(c);
        built.putAll(b);
        path.putAll(Compiler.compileModules(List.of("""
                module app.a exposing ( use )
                import lib.b ( f )
                behavior use : (n: Int) -> Int
                let use (n) = f(n)
                """), ModulePath.of(built)));
        path.putAll(b);
        path.putAll(Compiler.compile("""
                module lib.c exposing ( h )
                let h (n: Int) = n + 2
                """));

        assertEquals(new ModuleMessage.ItCopiedAnotherVersion("app.a", "helper", "h", "lib.c",
                        "closed helper"),
                refusal(path, readerOf("app.a")));
        assertAccepted(path, """
                module main.b
                import lib.b ( f )
                behavior go : (n: Int) -> Int
                let go (n) = n
                """);
    }

    private static final String C_LIMIT_SUMMED = """
            module lib.c exposing ( limit )
            let limit = 1 + 2
            """;

    private static final String B_BOUNDED_BY_C = """
            module lib.b exposing ( Base )
            import lib.c ( limit )
            data Base = { n: Int }
                invariant bound = n <= limit
            """;

    private static final String A_INCLUDES_B = """
            module app.a exposing ( Wrapped, wrap )
            import lib.b ( Base )
            data Wrapped = { ...Base, w: Int }
            behavior wrap : (x: Int) -> Wrapped
            let wrap (x) = Wrapped { n = 1, w = x }
            """;

    private static final String READS_A = """
            module main.m
            import app.a ( wrap, Wrapped )
            behavior go : (x: Int) -> Wrapped
            let go (x) = wrap(x)
            """;

    /**
     * A clause naming another module's constant is held, where a type includes it, to what that
     * constant is and not to how it was written. `lib.b` is built against `limit = 1 + 2`, which is
     * then written `3`; `app.a` is built including `Base` against the new `lib.c`, and `lib.b` is
     * built again beside it. Nothing any of them carries moved, so nothing is refused.
     */
    @Test
    void aConstantAClauseNamesIsHeldAsTheConstantThroughEveryTypeThatIncludesIt() {
        Map<String, ClassFileImage> c = Compiler.compile("""
                module lib.c exposing ( limit )
                let limit = 3
                """);
        Map<String, ClassFileImage> path = new HashMap<>(c);
        path.putAll(Compiler.compileModules(List.of(B_BOUNDED_BY_C),
                ModulePath.of(Compiler.compile(C_LIMIT_SUMMED))));
        path.putAll(Compiler.compileModules(List.of(A_INCLUDES_B), ModulePath.of(path)));

        assertAccepted(path, READS_A);

        path.putAll(Compiler.compileModules(List.of(B_BOUNDED_BY_C), ModulePath.of(c)));
        assertAccepted(path, READS_A);
    }

    /** The same, with the constant moved: `app.a` carries the old one in the clause it checks, and
     *  is said for it though what it names is only `Base`. */
    @Test
    void aConstantAnIncludedClauseNamesThatMovedIsSaidOfTheModuleThatIncludesIt() {
        Map<String, ClassFileImage> built = new HashMap<>(Compiler.compile(C_LIMIT_SUMMED));
        built.putAll(Compiler.compileModules(List.of(B_BOUNDED_BY_C), ModulePath.of(built)));
        Map<String, ClassFileImage> path = new HashMap<>(
                Compiler.compileModules(List.of(A_INCLUDES_B), ModulePath.of(built)));
        Map<String, ClassFileImage> c = Compiler.compile("""
                module lib.c exposing ( limit )
                let limit = 4
                """);
        path.putAll(c);
        path.putAll(Compiler.compileModules(List.of(B_BOUNDED_BY_C), ModulePath.of(c)));

        assertEquals(new ModuleMessage.ItCopiedAnotherConstant("app.a", "limit", "lib.c", "3", "4"),
                refusal(path, READS_A));
    }

    /** The departures of an attempted construction are a lookup by the clause that failed, so a
     *  helper that writes them in another order is the helper it was. */
    @Test
    void theOrderDeparturesAreWrittenInIsNotPartOfTheCopy() {
        Map<String, ClassFileImage> path = builtAgainst("""
                module lib.g exposing ( R, graded )
                data R = Int
                    invariant low = value >= 0
                    invariant high = value <= 100
                let graded (x: Int) = if R(x) as r then 0 else
                    | low -> 1
                    | high -> 2
                """, """
                module app.g exposing ( use )
                import lib.g ( graded )
                behavior use : (n: Int) -> Int
                let use (n) = graded(n)
                """, """
                module lib.g exposing ( R, graded )
                data R = Int
                    invariant low = value >= 0
                    invariant high = value <= 100
                let graded (x: Int) = if R(x) as r then 0 else
                    | high -> 2
                    | low -> 1
                """);

        assertAccepted(path, readerOf("app.g"));
    }

    /** A recursive helper of another module is emitted as a method of the reader, so the reader
     *  carries its body. */
    @Test
    void aRecursiveHelperTakenOnAsAMethodIsHeld() {
        Map<String, ClassFileImage> path = builtAgainst("""
                module lib.n exposing ( steps )
                partial let steps (n: Int): Int = if n <= 0 then 0 else 1 + steps(n - 1)
                """, """
                module app.n exposing ( use )
                import lib.n ( steps )
                behavior use : (n: Int) -> Int
                let use (n) = steps(n)
                """, """
                module lib.n exposing ( steps )
                partial let steps (n: Int): Int = if n <= 0 then 0 else 2 + steps(n - 1)
                """);

        assertEquals(new ModuleMessage.ItCopiedAnotherVersion("app.n", "helper", "steps", "lib.n",
                        "closed helper"),
                refusal(path, readerOf("app.n")));
    }

    /** Importing a constant and never reading it copies nothing of it. */
    @Test
    void aModuleThatCopiedNothingOfWhatMovedIsAccepted() {
        Map<String, ClassFileImage> path = builtAgainst("""
                module lib.k exposing ( limit )
                let limit = 3
                """, """
                module app.k exposing ( use )
                behavior use : (n: Int) -> Int
                let use (n) = n + 1
                """, """
                module lib.k exposing ( limit )
                let limit = 4
                """);

        assertAccepted(path, readerOf("app.k"));
    }

    /** A value that is not a constant runs where it is declared and its reader calls it, so a
     *  change to what it computes leaves the reader as it was. */
    @Test
    void aValueTheReaderCallsRatherThanCopiesIsNotHeldToItsBody() {
        Map<String, ClassFileImage> path = builtAgainst("""
                module lib.k exposing ( limit )
                let limit = List.length([1, 2, 3])
                """, READS_THE_CONSTANT, """
                module lib.k exposing ( limit )
                let limit = List.length([1, 2])
                """);

        assertAccepted(path, readerOf("app.k"));
    }

    /** An edit to a declaration the reader did not copy leaves it as it was, though the module it
     *  copied from moved. */
    @Test
    void anotherDeclarationOfTheModuleMovingIsNotHeldAgainstTheReader() {
        Map<String, ClassFileImage> path = builtAgainst("""
                module lib.p exposing ( capped, other )
                let capped (n: Int) = if n > 10 then 10 else n
                let other (n: Int) = n + 1
                """, CALLS_THE_HELPER, """
                module lib.p exposing ( capped, other )
                let capped (n: Int) = if n > 10 then 10 else n
                let other (n: Int) = n + 2
                """);

        assertAccepted(path, readerOf("app.r"));
    }

    /** What a copy holds is what a run of it turns on. Where the source put the helper, what it
     *  calls its parameter and its bindings, and a comment beside it are not; nor is how a constant
     *  was written, where it folds to the same value. */
    @Test
    void anEditTheCopyDoesNotSeeLeavesTheReaderAsItWas() {
        Map<String, ClassFileImage> helper = builtAgainst("""
                module lib.p exposing ( capped )
                let capped (n: Int) = {
                    let bound = 10
                    if n > bound then bound else n
                }
                """, CALLS_THE_HELPER, """
                module lib.p exposing ( capped )

                // the bound a reading is held to
                let capped (value: Int) = {
                    let limit = 10
                    if value > limit
                        then limit
                        else value
                }
                """);
        Map<String, ClassFileImage> constant = builtAgainst("""
                module lib.k exposing ( limit )
                let limit = 1 + 2
                """, READS_THE_CONSTANT, """
                module lib.k exposing ( limit )
                let limit = 3
                """);

        assertAccepted(helper, readerOf("app.r"));
        assertAccepted(constant, readerOf("app.k"));
    }

    /** A module that imports {@code module}'s {@code use} and calls it. */
    private static String readerOf(String module) {
        return """
                module main.m
                import %s ( use )
                behavior go : (n: Int) -> Int
                let go (n) = use(n)
                """.formatted(module);
    }

    /** {@code app} built against {@code before}, on a path beside {@code after}. */
    private static Map<String, ClassFileImage> builtAgainst(String before, String app,
                                                            String after) {
        Map<String, ClassFileImage> path = new HashMap<>(Compiler.compileModules(List.of(app),
                ModulePath.of(Compiler.compile(before))));
        path.putAll(Compiler.compile(after));
        return path;
    }

    /** What {@code reader} is refused with, against {@code path}. */
    private static ModuleMessage refusal(Map<String, ClassFileImage> path, String reader) {
        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(reader), ModulePath.of(path)));
        assertEquals("E1510", refused.diagnostic().code(), refused.getMessage());
        return assertInstanceOf(ModuleMessage.class, refused.diagnostic().said());
    }

    private static void assertAccepted(Map<String, ClassFileImage> path, String reader) {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(reader), ModulePath.of(path)));
    }
}
