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
