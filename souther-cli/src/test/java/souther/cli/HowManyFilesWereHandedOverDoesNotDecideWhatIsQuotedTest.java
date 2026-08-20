package souther.cli;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticRenderer;
import souther.compiler.diag.HumanRenderer;
import souther.compiler.diag.Located;
import souther.compiler.diag.ReportContext;
import souther.compiler.diag.SourceContextResolver;

import java.lang.reflect.Method;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a report quotes does not depend on how many files the command line was handed.
 *
 * <p>It did. A report reaches this command as a diagnostic and a list of sources, and the list used
 * to answer the only file it had for any id at all — including for no id. That made two rules hold
 * each other up: a report that arrived without a source was quoted correctly whenever exactly one
 * file had been handed over, and lost its file name and its line the moment a second one was. The
 * numbers were never in doubt; the report said which source they were of and nothing on the way
 * carried it.
 *
 * <p>So this renders one report twice, against one file and against two, and holds the two outputs
 * to being the same string. The report is the same report and the file it points into is the same
 * file; a second file the report says nothing about is not a fact about it.
 */
class HowManyFilesWereHandedOverDoesNotDecideWhatIsQuotedTest {

    private static final String BROKEN = """
            module a

            let f (x: Int): Int = x + "no"
            """;

    private static final String UNRELATED = """
            module b

            let g (x: Int): Int = x
            """;

    /** The command line's own resolver over {@code files} — the thing that used to answer the one
     *  file it had for whatever it was asked. */
    private static SourceContextResolver resolverOf(List<Path> files) throws Exception {
        Method sourcesOf = Main.class.getDeclaredMethod("sourcesOf", List.class);
        sourcesOf.setAccessible(true);
        return (SourceContextResolver) sourcesOf.invoke(null, files);
    }

    private static String rendered(List<Path> files, CompileException e) throws Exception {
        return DiagnosticRenderer.renderAll(e.locatedDiagnostics(), resolverOf(files),
                new HumanRenderer(false), Locale.ENGLISH).get(0);
    }

    @Test
    void oneFileAndTwoQuoteTheSameThing(@TempDir Path dir) throws Exception {
        Path a = dir.resolve("a.sou");
        Path b = dir.resolve("b.sou");
        Files.writeString(a, BROKEN);
        Files.writeString(b, UNRELATED);

        CompileException e = assertThrows(CompileException.class,
                () -> Main.compileToDir(List.of(a), dir.resolve("out")));

        String alone = rendered(List.of(a), e);
        String beside = rendered(List.of(a, b), e);

        assertTrue(alone.contains("a.sou:3:"), alone);
        assertTrue(alone.contains("let f (x: Int): Int = x + \"no\""), alone);
        assertEquals(alone, beside,
                "a second file the report says nothing about is not a fact about the report");
    }

    /**
     * And the same of a report the command line was told nothing about.
     *
     * <p>The route that used to lose it: a report raised without a source list at all. Where it
     * points is on the report, so both renderings quote it, and neither reads the file count as an
     * answer to a question the report had already answered.
     */
    @Test
    void aReportCarryingNoSourceListQuotesItsOwnFileEitherWay(@TempDir Path dir) throws Exception {
        Path a = dir.resolve("a.sou");
        Path b = dir.resolve("b.sou");
        Files.writeString(a, BROKEN);
        Files.writeString(b, UNRELATED);

        CompileException tagged = assertThrows(CompileException.class,
                () -> Main.compileToDir(List.of(a), dir.resolve("out")));
        CompileException untagged = CompileException.of(tagged.diagnostic());

        String alone = new HumanRenderer(false).render(
                new Located(untagged.diagnostic(), ReportContext.NONE),
                resolverOf(List.of(a)), Locale.ENGLISH);
        String beside = new HumanRenderer(false).render(
                new Located(untagged.diagnostic(), ReportContext.NONE),
                resolverOf(List.of(a, b)), Locale.ENGLISH);

        assertTrue(alone.contains("a.sou:3:"), alone);
        assertTrue(alone.contains("let f (x: Int): Int = x + \"no\""), alone);
        assertEquals(alone, beside, "the report names its own file, told or not");
    }

    /**
     * A report this command cannot place is not quoted from the only file to hand.
     *
     * <p>What the single-file answer was for, and the one thing losing it changes. A report that
     * points at nothing and is listed under no file has said, twice, that it is not about a line of
     * anybody's source; naming the only file handed over is this command deciding otherwise, and it
     * is a decision it has nothing to make it on.
     */
    @Test
    void aReportThisCommandCannotPlaceIsNotQuotedFromTheOnlyFileToHand(@TempDir Path dir)
            throws Exception {
        Path a = dir.resolve("a.sou");
        Files.writeString(a, BROKEN);

        String out = new HumanRenderer(false).render(
                new Located(Diagnostic.literal(null, "boom"), ReportContext.NONE),
                resolverOf(List.of(a)), Locale.ENGLISH);

        assertTrue(out.contains("boom"), out);
        assertFalse(out.contains("a.sou"),
                "one file to hand is not a reason to say the report is about it: " + out);
        assertFalse(out.contains("let f"), out);
    }
}
