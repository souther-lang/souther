package souther.compiler;

import souther.compiler.diag.Citation;
import souther.compiler.diag.Located;
import souther.compiler.diag.SourcePos;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A module read off the class path is read from text this compile put back together out of what the
 * module published, so a coordinate in it is a line and a column of a file nobody holds. A report
 * found there is said at the nearest place on the way to that module a source of this compilation
 * writes, and names where the code is rather than pointing at it.
 *
 * <p>Both halves matter. Quoted as it stands, the coordinate lands wherever those numbers happen to
 * fall in the file the author is looking at — a compile of one source has no way to tell an untagged
 * report from one about no file at all — and filed as it stands it lands nowhere, which left a
 * failing compile answering no classes and no diagnostics.
 */
class AReportAboutAModuleOffThePathIsSaidWhereItWasReachedTest {

    /** A module compiled against {@code path}, as its own project's build produced it. */
    private static Map<String, byte[]> built(String source, Map<String, byte[]> path) {
        return Compiler.compileModules(List.of(source), path::get);
    }

    private static Map<String, byte[]> and(Map<String, byte[]> one, Map<String, byte[]> other) {
        Map<String, byte[]> both = new java.util.LinkedHashMap<>(one);
        both.putAll(other);
        return both;
    }

    private static Compilation reading(String source, Map<String, byte[]> path) {
        Compilation compilation = Compilation.ofSources(List.of(source), path::get);
        compilation.answerEverything();
        return compilation;
    }

    /** The classes of {@code lib.deep}, which every path here leaves out. */
    private static Map<String, byte[]> deep() {
        return Compiler.compile("""
                module lib.deep exposing ( Deep )
                data Deep = String
                """);
    }

    /** The declaring project's build of {@code lib.held}, which needs {@code lib.deep}. */
    private static Map<String, byte[]> held() {
        return built("""
                module lib.held exposing ( Held )
                import lib.deep ( Deep )

                data Held = { deep: Deep }
                """, deep());
    }

    @Test
    void itIsSaidAtTheImportThatNamedTheModule() {
        // `lib.held` is on the path and the module it needs is not, so reading it back has something
        // to report about a declaration written where this compile has no file.
        Compilation compilation = reading("""
                module app.uses




                import lib.held ( Held )

                data Page = { held: Held }
                """, held());

        SourcePos said = whereTheReportAboutIsSaid(compilation, "lib.held");
        assertEquals("0", said.sourceId(), "a reader can only be sent to a file this compile holds");
        assertEquals(6, said.line(), "the import line naming the module, not a line of the module");
        assertEquals(1, said.column());
    }

    /** The coordinate says the code is elsewhere, so no surface reads it as the place. */
    @Test
    void theCoordinateStandsInForCodeWrittenInThatModule() {
        Compilation compilation = reading("""
                module app.uses
                import lib.held ( Held )

                data Page = { held: Held }
                """, held());

        Citation citation = Citation.of(whereTheReportAboutIsSaid(compilation, "lib.held"));

        assertEquals("lib.held",
                assertInstanceOf(Citation.OutOfSight.class, citation).declaration());
    }

    /**
     * A module reached only through another off the path inherits that one's place. There is no
     * import line naming it anywhere a reader here can look, and the one naming the dependency that
     * led there is the nearest thing there is.
     */
    @Test
    void oneReachedThroughAnotherIsSaidAtTheImportThatLedThere() {
        Map<String, byte[]> held = held();
        Map<String, byte[]> front = built("""
                module lib.front exposing ( Front )
                import lib.held ( Held )

                data Front = { held: Held }
                """, and(held, deep()));

        Compilation compilation = reading("""
                module app.uses


                import lib.front ( Front )

                data Page = { front: Front }
                """, and(held, front));

        SourcePos said = whereTheReportAboutIsSaid(compilation, "lib.held");
        assertEquals("0", said.sourceId());
        assertEquals(4, said.line(), "the import of the dependency that led to it");
    }

    /** The route this was found on. The report is about a module the caller has no file for, and it
     *  still reaches the file the caller does have. */
    @Test
    void itIsPublishedOnTheSourceThatReachedIt() {
        Compilation compilation = reading("""
                module app.uses
                import lib.held ( Held )

                data Page = { held: Held }
                """, held());

        List<Located> onTheSource = compilation.diagnostics().get("0");
        assertNotNull(onTheSource);
        assertFalse(onTheSource.isEmpty(),
                "a compile that emitted nothing said nothing about why");
    }

    /**
     * Every error reaches a file. What the command line stops for and what an editor marks are the
     * same set, and a report that reached neither is one the author is never told about — the
     * walk over the path is one question about the whole compilation and names no module of its
     * own, so what it finds has to say where it is said.
     *
     * <p>Measured on the reports rather than on the classes. A compile that emits nothing and says
     * nothing is what this looked like, but which of those is the defect is the second one: what a
     * build produces is its own question, and one that legitimately produces no classes would make
     * the first reading say this had been fixed.
     */
    @Test
    void noErrorIsLeftWithNowhereToBeSaid() {
        Compilation compilation = reading("""
                module app.uses
                import lib.held ( Held )

                data Page = { held: Held }
                """, held());

        List<String> unreachable = new ArrayList<>();
        for (Db.Found found : compilation.reports()) {
            if (found.report().isError() && compilation.publishSourceIdsOf(found).isEmpty()) {
                unreachable.add(found.report().diagnostic().code() + " about " + found.module());
            }
        }
        assertEquals(List.of(), unreachable, "an error the author is never shown");
    }

    /**
     * A dependency two files import is reached by both, and both authors are told.
     *
     * <p>Neither import is the premise the other is measured by, and neither author has anything
     * different to do about it. Marking one of them leaves the other looking at a file that is fine
     * while the build fails — and which of the two it would be is the order the sources happened to
     * arrive in.
     */
    @Test
    void everySourceThatReachesItIsTold() {
        Compilation compilation = Compilation.ofSources(List.of("""
                module app.a exposing ( A )
                import lib.held ( Held )

                data A = { held: Held }
                """, """
                module app.b exposing ( B )
                import lib.held ( Held )

                data B = { held: Held }
                """), held()::get);
        compilation.answerEverything();

        Map<String, List<Located>> byId = compilation.diagnostics();
        assertFalse(byId.get("0").isEmpty(), "the source that was reached first");
        assertFalse(byId.get("1").isEmpty(), "the one that reaches it just as much");
    }

    /**
     * Two findings that differed only in where they were written are said once.
     *
     * <p>Reading a report for where it may be said is what makes them one. Their coordinates are in
     * a text nobody holds and are what told them apart; said at the place the module was reached
     * from, they are one sentence at one caret, and an author shown it twice has nothing to tell
     * them apart by either.
     */
    @Test
    void twoFindingsInOnePublishedModuleAreSaidOnce() {
        Map<String, byte[]> withDeep = Compiler.compile("""
                module lib.deep exposing ( Deep )
                data Deep = String
                """);
        Map<String, byte[]> twice = built("""
                module lib.twice exposing ( Twice )
                data Twice = { a: lib.deep.Deep, b: lib.deep.Deep }
                """, withDeep);
        // the dependency is rebuilt without the type, so both field types fail to resolve
        Map<String, byte[]> withoutDeep = Compiler.compile("""
                module lib.deep exposing ( Other )
                data Other = String
                """);

        Compilation compilation = reading("""
                module app.uses
                import lib.twice ( Twice )

                data Page = { twice: Twice }
                """, and(withoutDeep, twice));

        assertEquals(2, compilation.db().allReports().size(),
                "two findings, at the two places the module writes the name");
        assertEquals(1, compilation.diagnostics().get("0").size(),
                "one thing to be told, said once");
    }

    /** Where the report about {@code module} is said. */
    private static SourcePos whereTheReportAboutIsSaid(Compilation compilation, String module) {
        List<SourcePos> said = new ArrayList<>();
        for (Db.Found found : compilation.reports()) {
            if (module.equals(found.module()) && found.report().diagnostic().pos() != null) {
                said.add(found.report().diagnostic().pos());
            }
        }
        assertFalse(said.isEmpty(), "nothing was reported about " + module);
        return said.get(0);
    }
}
