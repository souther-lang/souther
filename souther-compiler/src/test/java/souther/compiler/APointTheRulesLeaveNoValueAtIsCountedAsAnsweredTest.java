package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderObligationPointAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ObligationSummary;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A point the rules are proved to leave nothing at is an obligation with an answer, and an author
 * reads it as one.
 *
 * <p>The proof is made where a row is looked for, out of the region the rules on the way to the
 * border leave — so it arrives after the point is already owed, and what it settles is what became
 * of the obligation. The sentence a reader gets said the model's word already; what the account
 * beside it said was that nobody could say anything, which is the state for something this compiler
 * could not do.
 *
 * <p>The obligation stays in the count. What a border owes is read off the declarations, and they
 * do not move while a body is read: taken out on the strength of this proof, a model would owe
 * fewer rows the more of its body this compiler managed to take in.
 *
 * <p>The model is two guards that close between them, which is what an author writes one line at a
 * time. Neither of them refuses anything on its own.
 */
class APointTheRulesLeaveNoValueAtIsCountedAsAnsweredTest {

    private static final String CLOSED = """
            module m

            behavior f : (x: Int, y: Int) -> Bool

            let f (x, y) = {
                guard y <= x else false
                guard y >= x + 1 else false
                guard y >= 100 else false

                true
            }
            """;

    /** What an author is told at the point the guards close between them. */
    @Test
    void theProvedPointIsSaidAsAnAnswerAndNotAsAnOpenQuestion() {
        List<String> said = about("comparison@7:13");

        assertTrue(said.stream().anyMatch(line ->
                        line.contains("· no row can stand at the ON point")),
                () -> "the rules leave the point no value, which is said as the answer it is: "
                        + said);
        assertFalse(said.stream().anyMatch(line ->
                        line.contains("nothing could show a row can be written")),
                () -> "nothing here was stopped and no search fell short, so there is no open"
                        + " question to name: " + said);
    }

    /** And the account it is counted in says the same thing. */
    @Test
    void theAccountHoldsItAsAnsweredAndKeepsItInTheCount() {
        ObligationSummary<BorderObligationPointAssessment> owed = account();

        assertEquals(List.of("ON", "IN"),
                owed.refuted().stream().map(point -> point.role().toString()).toList(),
                "the two points the guards close between them are the ones no row can be written"
                        + " at, and which points they are is where the proof was made");
        assertEquals(6, owed.undecided().size(),
                "the other six are open on what nobody read, which is what they were");
        assertEquals(8, owed.counted(),
                "the line owes what the declarations say it owes, whatever the body proved");
    }

    /** The count a reader sees, with the answered points beside the fraction and not inside it. */
    @Test
    void theBlockPrintsTheAnsweredPointsBesideTheFraction() {
        assertTrue(report().contains("obligations 0/8   refuted 2"),
                () -> "no row stands at any of the points, and two of them are points no row can"
                        + " stand at:\n" + report());
    }

    /**
     * The control: the border ahead of that guard is said exactly as it was.
     *
     * <p>Its four points are on the same pair of positions and are searched for the same way; what
     * differs is that nothing on the way to them narrows the distance. A proof reaching them would
     * be this reading refusing a border an author can write a row at.
     */
    @Test
    void andTheBorderNothingNarrowsIsSaidAsItWas() {
        List<String> said = about("comparison@6:13");

        assertFalse(said.stream().anyMatch(line -> line.contains("no row can stand at")),
                () -> "the declarations leave this border's distance every value it has: " + said);
        assertEquals(4, said.stream()
                        .filter(line -> line.contains("undecided whether a row is at")).count(),
                () -> "its four points are owed and unsettled, as they were: " + said);
    }

    /** The account of the one behavior this model has. */
    private static ObligationSummary<BorderObligationPointAssessment> account() {
        AdequacyReport.BehaviorReport behavior = ANALYSED.modules().get(0).behaviors().get(0);
        return ObligationSummary.of(behavior.account(), BorderObligationPointAssessment::owed);
    }

    /**
     * The lines of the report that name one reading of the body, each with what is said under it.
     *
     * <p>What a point comes to is on the line naming it and why is on the line under it, so a check
     * reading one of the two reads half of what an author does.
     */
    private static List<String> about(String comparison) {
        List<String> out = new java.util.ArrayList<>();
        boolean under = false;
        for (String line : report().lines().map(String::strip).toList()) {
            if (line.startsWith("·") && !line.contains("no row can stand at")) {
                if (under || line.contains(comparison)) {
                    out.add(line);
                }
                continue;
            }
            under = line.contains(comparison);
            if (under) {
                out.add(line);
            }
        }
        return out;
    }

    private static String report() {
        return REPORT;
    }

    private static final AdequacyReport ANALYSED = measure();

    private static final String REPORT = written();

    private static Compilation compiled;

    private static AdequacyReport measure() {
        compiled = Compilation.ofSource(CLOSED, "Main");
        compiled.measure(Adequacy.Asked.fullReport());
        compiled.answerEverything();
        return AdequacyReport.of(compiled);
    }

    private static String written() {
        return ANALYSED.human(SourceRendering.namedByIdentity(compiled.texts()));
    }
}
