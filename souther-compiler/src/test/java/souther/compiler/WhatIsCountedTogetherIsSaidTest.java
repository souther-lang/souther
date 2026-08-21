package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two arms counted as one are said to be, where nothing can show they are one.
 *
 * <p>What tells two copies of a library fork apart is the predicate each was handed. A closure
 * comparing nothing an author wrote — a {@code filter} over a {@code Bool} field — leaves nothing to
 * tell them by, so they are counted together.
 *
 * <p>Together rather than apart, and that is the safer of the two. Split, each would be owed a row
 * establishing what the row beside it already does, and a specific piece of work that is already
 * done is worse to be told than nothing. What it costs is a count that holds two predicates where it
 * says one, and that is exactly the shape of a behavior reported complete over something nothing
 * ran — so it is said rather than left to be found.
 */
class WhatIsCountedTogetherIsSaidTest {

    private static final String MODULE = "example.flags";

    private static final String MODEL = """
            module example.flags

            data Person =
                { active: Bool
                , retired: Bool
                }
            data Count = Int

            behavior twice : (a: List<Person>, b: List<Person>) -> Count
                constructs Count
            let twice (a, b) =
                Count(List.length(List.filter(x -> x.active, a))
                    + List.length(List.filter(y -> y.retired, b)))

            example twice
                | "the second is never entered"
                    : ([ Person { active = true, retired = false } ], [ ]) -> Count(1)
            """;

    private static Compilation measured() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return compilation;
    }

    /** The two calls come out under one pair of keys, since neither closure compares anything. */
    @Test
    void armsNothingCanTellApartAreCountedTogether() {
        Adequacy.BranchEvidence twice = measured().db()
                .ask(new Adequacy.BranchCoverage(MODULE)).value().get("twice");
        assertNotNull(twice, "the model under test compiles");

        assertEquals(4, twice.all().size(), "each call is emitted and probed on its own");
        assertEquals(2, twice.obligations(), "and the four are counted under two keys");
        assertEquals(1, twice.countedTogether().size(),
                () -> "one fork whose copies cannot be told apart: " + twice.countedTogether());
    }

    /** And the report says so, rather than printing a number that quietly holds both. */
    @Test
    void theReportSaysWhichForkThatIs() {
        String human = AdequacyReport.of(measured()).human(SourceNameResolver.identity());

        assertTrue(human.contains("arms of a fork `souther.list` wrote are counted as one"), human);
        assertEquals(1, human.lines().filter(line -> line.contains("counted as one")).count(),
                () -> "said once for the fork and not once per arm: " + human);
    }

    /**
     * And a document says it too, not only the prose.
     *
     * <p>What a count holding two predicates where it says one costs is the same either way, and a
     * consumer reads the document. Said in the prose alone, the numbers a build acts on carry the
     * collapse with nothing beside them saying so.
     */
    @Test
    void theDocumentSaysItToo() {
        String json = souther.compiler.report.AdequacyReport.of(measured())
                .json(SourceNameResolver.identity());

        assertTrue(json.contains("\"countedTogether\" : [ \"souther.list\" ]"), json);
    }

    /** Nothing is said where the closures do compare something, since then they are told apart. */
    @Test
    void nothingIsSaidWhereThePredicatesAreToldApart() {
        Compilation compilation = Compilation.ofSource("""
                module example.flags

                data Age = Int
                data Person =
                    { age: Age
                    }
                data Count = Int

                behavior twice : (a: List<Person>, b: List<Person>) -> Count
                    constructs Count
                let twice (a, b) =
                    Count(List.length(List.filter(x -> x.age.value >= 18, a))
                        + List.length(List.filter(y -> y.age.value >= 65, b)))

                example twice
                    | "the second is never entered"
                        : ([ Person { age = Age(20) } ], [ ]) -> Count(1)
                """, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Adequacy.BranchEvidence twice = compilation.db()
                .ask(new Adequacy.BranchCoverage(MODULE)).value().get("twice");
        assertNotNull(twice, "the model under test compiles");

        assertEquals(4, twice.obligations(), "each call's arms are its own to cover");
        assertEquals(java.util.List.of(), twice.countedTogether(),
                "so there is nothing counted together to say");
    }
}
