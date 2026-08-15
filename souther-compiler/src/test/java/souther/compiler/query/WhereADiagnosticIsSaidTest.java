package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.Located;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
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

        Map<String, List<Located>> found = c.diagnostics();

        assertEquals(List.of("0"), List.copyOf(found.keySet()));
        assertEquals(1, found.get("0").size(),
                "the one source is where its one problem is: " + found);
    }

    @Test
    void aCompileOfOneSourceFilesUnderTheSourceItQuotesFrom() {
        Compilation c = Compilation.ofSource(BROKEN, "Main");

        Map<String, List<Located>> found = c.diagnostics();

        assertEquals("0", found.get("0").get(0).primarySourceId(),
                "the entry and the file it is filed under agree, or nothing can be quoted");
    }

    @Test
    void aCallerHoldingItsOwnFileIsToldNothingAboutWhichSource() {
        Compilation c = Compilation.ofSource(BROKEN, "Main");
        c.answerEverything();

        Db.Found only = c.db().allReports().get(0);

        assertNull(c.sourceIdOf(only),
                "one source: the caller knows the file it handed over");
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

        List<String> said = c.db().allReports().stream().map(c::sourceIdOf).toList();

        assertTrue(said.contains("1"), "the mistake is in the second source: " + said);
    }

    /** Where a report goes is read off where it points, so there is no way to name a file it has
     *  nothing to show in. */
    @Test
    void aReportIsSaidWhereItPointsAndNowhereElse() {
        Compilation c = Compilation.ofSource(BROKEN, "Main");
        c.answerEverything();

        for (Db.Found found : c.db().allReports()) {
            List<String> saidAt = c.publishSourceIdsOf(found);
            for (String id : saidAt) {
                assertTrue(hasARegionIn(found, id, c),
                        found.report().diagnostic().code() + " is said at " + id
                                + " and points into nothing there");
            }
        }
    }

    private static boolean hasARegionIn(Db.Found found, String id, Compilation c) {
        if (id.equals(c.publishSourceIdsOf(found).get(0))) {
            return true;
        }
        return found.report().diagnostic().secondary().stream()
                .anyMatch(label -> label.place().pointsAt().filter(r -> id.equals(r.start().sourceId())).isPresent());
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

        Map<String, List<Located>> found = c.diagnostics();

        assertEquals(1, found.get("0").size(),
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

        Map<String, List<Located>> found = c.diagnostics();

        assertEquals(2, found.get("0").size(),
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

        Map<String, List<Located>> found = c.diagnostics();

        assertEquals(1, found.get("0").size(), "a's is said on a: " + found);
        assertEquals(1, found.get("1").size(), "b's is said on b: " + found);
    }
}
