package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A border the way to it contradicts is refused by the rules, and no figure of this compiler's is
 * spent on it or named to a reader.
 *
 * <p>The same fact as the realizer's, read where an author reads it. What the search answers has to
 * cross a coverage measure and a report before it is a sentence, and the answer that is the model's
 * word can be read back as this compiler falling short at either hop. That reading is the one an
 * author acts on by raising a number that would not have helped.
 *
 * <p>The model is two guards that close between them, which is what an author writes one line at a
 * time. Neither of them refuses anything on its own.
 */
class ABorderTheWayToItContradictsIsRefusedAndNotSearchedForTest {

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

    /** What an author is told about the border the guards close between them. */
    @Test
    void theBorderBehindTheSecondGuardIsSaidAsTheModelsWord() {
        List<String> said = about("comparison@7:13");

        assertTrue(said.stream().anyMatch(line -> line.contains("the rules leave no value at")),
                () -> "no row is at the line the guards close between them, which is the rules'"
                        + " answer and not a search that stopped: " + said);
    }

    /** And no figure of this compiler's is named anywhere in what is said. */
    @Test
    void andNoFigureOfThisCompilersIsNamed() {
        assertFalse(report().contains("a figure of this compiler's"),
                () -> "nothing here needed searching for, so there is no number to raise:\n"
                        + report());
    }

    /**
     * The control: the border ahead of that guard is said exactly as it was.
     *
     * <p>Its four points are on the same pair of positions and are searched for the same way; what
     * differs is that nothing on the way to them narrows the distance. A proof reaching them would
     * be this reading refusing a border an author can write a row at, and it is the one thing that
     * separates the fix from a search that gives up sooner.
     */
    @Test
    void andTheBorderNothingNarrowsIsSaidAsItWas() {
        List<String> said = about("comparison@6:13");

        assertFalse(said.stream().anyMatch(line -> line.contains("the rules leave no value at")),
                () -> "the declarations leave this border's distance every value it has: " + said);
        assertTrue(said.stream().filter(line -> line.contains("undecided whether a row is at"))
                        .count() == 4,
                () -> "its four points are owed and unsettled, as they were: " + said);
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
            // A point of its own and not a sentence under one, which is what a point the rules
            // leave no value at is said as. What is under it is the reading that proved it, so the
            // line begins a point rather than continuing the one before.
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

    /** Measured once, because every sentence here is about the one block. */
    private static String report() {
        return REPORT;
    }

    private static final String REPORT = measure();

    private static String measure() {
        Compilation compilation = Compilation.ofSource(CLOSED, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
