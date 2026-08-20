package souther.compiler.query;

import souther.compiler.diag.Primary;

import souther.compiler.source.SourceId;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.Located;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a compile calls its sources and what it tells a caller about them are two questions. A file
 * is how a report is filed and how its lines are quoted; a caller holding its own list of files is a
 * separate matter, and a compile of one source tells that caller nothing because it already knows.
 */
class WhereADiagnosticIsSaidTest {

    private static final String BROKEN = """
            module m
            data N = { v: Int }
            let f (n: N) = bogus
            """;

    @Test
    void aCompileOfOneSourceStillFilesItsProblemsUnderThatSource() {
        Compilation c = Compilation.ofSource(BROKEN, "Main");

        Map<SourceId, List<Located>> found = c.diagnostics();

        assertEquals(List.of(new SourceId("0")), List.copyOf(found.keySet()));
        assertEquals(1, found.get(new SourceId("0")).size(),
                "the one source is where its one problem is: " + found);
    }

    @Test
    void aCompileOfOneSourceFilesUnderTheSourceItQuotesFrom() {
        Compilation c = Compilation.ofSource(BROKEN, "Main");

        Map<SourceId, List<Located>> found = c.diagnostics();

        assertEquals(new SourceId("0"), found.get(new SourceId("0")).get(0).context().filedUnder().orElse(null),
                "the entry and the file it is filed under agree, or nothing can be quoted");
    }

    /**
     * A compile of one source names it like any other.
     *
     * <p>It used to name none, on the grounds that a caller holding one file knows which it is. What
     * that left was a primary naming nothing and every secondary naming the one source there was, so
     * a renderer comparing the two read them as two files and printed a file name over a note in the
     * file it was already quoting. Whether to print an id at all is answered by the names a caller
     * gives, and never by leaving the report unable to say where it is.
     */
    @Test
    void aCompileOfOneSourceNamesItLikeAnyOther() {
        Compilation c = Compilation.ofSource(BROKEN, "Main");
        c.answerEverything();

        Db.Found only = c.db().allReports().get(0);

        assertEquals(new SourceId("0"), c.filedUnderOf(only),
                "the one source is a source, and a report in it says so");
    }

    @Test
    void aCompileOfSeveralSourcesTellsACallerWhichOne() {
        Compilation c = Compilation.ofSources(List.of("""
                module a
                data N = { v: Int }
                """, """
                module b
                import a ( N )
                let f (n: N) = bogus
                """), souther.compiler.meta.ModulePath.EMPTY);
        c.answerEverything();

        List<SourceId> said = c.db().allReports().stream().map(c::filedUnderOf).toList();

        assertTrue(said.contains(new SourceId("1")), "the mistake is in the second source: " + said);
    }

    /** Where a report goes is read off where it points, so there is no way to name a file it has
     *  nothing to show in. */
    @Test
    void aReportIsSaidWhereItPointsAndNowhereElse() {
        Compilation c = Compilation.ofSource(BROKEN, "Main");
        c.answerEverything();

        for (Db.Found found : c.db().allReports()) {
            List<SourceId> saidAt = c.publishSourceIdsOf(found);
            for (SourceId id : saidAt) {
                assertTrue(hasARegionIn(found, id, c),
                        found.report().diagnostic().code() + " is said at " + id
                                + " and points into nothing there");
            }
        }
    }

    private static boolean hasARegionIn(Db.Found found, SourceId id, Compilation c) {
        if (id.equals(c.publishSourceIdsOf(found).get(0))) {
            return true;
        }
        return found.report().diagnostic().secondary().stream()
                .anyMatch(label -> label.place() instanceof souther.compiler.diag.DiagnosticPlace.InSource in
                        && in.region().start().isIn(id));
    }

    // --- one problem, one report; two problems, two ----------------------------------------------

    /**
     * A helper is checked on its own and again in each body it is expanded into, and both are looking
     * at one line of one file. Neither is wrong to have found it and neither can see the other, so it
     * is the reading of them that settles that it is one problem.
     */
    @Test
    void theSameProblemFoundThroughTwoQuestionsIsOneReport() {
        // `Bodies.ModuleCheck` finds this checking the helper on its own, and
        // `Bodies.CheckedBehavior` finds it again in each body the helper is expanded into. Both
        // report it; both name the same line of the same file, so the reading of them is one report.
        Compilation c = Compilation.ofSources(List.of("""
                module m
                data N = { v: Int }
                let joined (n: N) = n.v + "text"
                behavior f : (n: N) -> Int
                let f (n) = joined(n)
                behavior g : (n: N) -> Int
                let g (n) = joined(n)
                """), souther.compiler.meta.ModulePath.EMPTY);

        Map<SourceId, List<Located>> found = c.diagnostics();

        assertEquals(1, found.get(new SourceId("0")).size(),
                "the helper and the two bodies it is expanded into found one mistake: " + found);
    }

    /**
     * Two checks of one expression against different expectations say the same thing at the same
     * place with different arguments, and those are two problems. Nothing about filing a report by
     * where it points may collapse them.
     */
    @Test
    void twoDifferentProblemsAtOneCoordinateInOneFileAreTwoReports() {
        Compilation c = Compilation.ofSources(List.of("""
                module m
                data N = { v: Int }
                behavior f : (n: N) -> Int
                let f (n) = bogusOne
                behavior g : (n: N) -> Int
                let g (n) = bogusTwo
                """), souther.compiler.meta.ModulePath.EMPTY);

        Map<SourceId, List<Located>> found = c.diagnostics();

        assertEquals(2, found.get(new SourceId("0")).size(),
                "two names denote nothing, so there are two things to say: " + found);
    }

    /**
     * The same mistake written at the same line and column of two files is two mistakes. Before a
     * position said which file it was read from, the coordinate was all there was to tell them apart
     * by — so this is the reading that the earlier design could not have got right.
     */
    @Test
    void oneCoordinateInTwoFilesIsTwoReports() {
        String same = """
                data N = { v: Int }
                behavior f : (n: N) -> Int
                let f (n) = bogus
                """;
        Compilation c = Compilation.ofSources(
                List.of("module a\n" + same, "module b\n" + same),
                souther.compiler.meta.ModulePath.EMPTY);

        Map<SourceId, List<Located>> found = c.diagnostics();

        assertEquals(1, found.get(new SourceId("0")).size(), "a's is said on a: " + found);
        assertEquals(1, found.get(new SourceId("1")).size(), "b's is said on b: " + found);
    }
}
