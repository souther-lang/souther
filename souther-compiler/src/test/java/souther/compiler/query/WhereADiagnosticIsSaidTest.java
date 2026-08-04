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
        String primary = c.publishSourceIdsOf(found).get(0);
        if (id.equals(primary)) {
            return true;
        }
        return found.report().diagnostic().secondary().stream()
                .anyMatch(label -> id.equals(label.sourceIdOr(primary)));
    }
}
