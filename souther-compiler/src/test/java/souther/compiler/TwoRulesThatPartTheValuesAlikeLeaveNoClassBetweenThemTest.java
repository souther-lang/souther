package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Two rules that part a position's values in one place leave one line and no class between them.
 *
 * <p>{@code n <= 4} and {@code n < 5} divide the whole numbers once. Taken as two thresholds, they
 * leave a range above four and below five — inhabited by the arithmetic, since four is less than
 * five, and holding no value any row could ever be written at. A report counts it, tells an author
 * no row is in it, and the generator is asked for one it cannot compose.
 *
 * <p>Written as two {@code guard}s the class never appeared, because the second comparison has an
 * arm nothing reaches and draws no line at all. That is a different rule doing the work, and it
 * stops doing it as soon as the two rules are written anywhere the reachability of an arm is not the
 * question — in a clause, or across a clause and a body.
 */
class TwoRulesThatPartTheValuesAlikeLeaveNoClassBetweenThemTest {

    private static List<String> classesOf(String clause, String body) {
        Compilation compilation = Compilation.ofSource("""
                module example.parted

                data No = { why: Int }
                data Yes = { v: Int }
                data Result = No | Yes

                behavior f : (n: Int) -> Result
                    constructs Yes, No
                %s

                let f (n) = {
                %s
                    Yes { v = 1 }
                }

                example f
                    | "one" : (1) -> Yes { v = 1 }
                """.formatted(clause, body), "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, PartitionEvidence> all = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");
        PartitionEvidence evidence = all.get("f");
        assertEquals(1, evidence.axes().size(), "the behavior takes one position");
        return evidence.axes().get(0).classes();
    }

    /** One clause, as the baseline the other is read against. */
    @Test
    void oneClauseLeavesTheTwoClassesItParts() {
        assertEquals(List.of("n/x <= 4", "n/4 < x"),
                classesOf("    ensures asked = Yes -> n <= 4", ""));
    }

    /**
     * And the same division said a second way leaves the same two.
     *
     * <p>Not three. The range between them is where the defect shows: nothing can be written in it,
     * so it is not a class of the position, and a measure that counts it is counting a distinction
     * the model does not draw.
     */
    @Test
    void theSameDivisionSaidTwoWaysLeavesTheSameTwoClasses() {
        assertEquals(List.of("n/x <= 4", "n/4 < x"),
                classesOf("    ensures asked = Yes -> n <= 4",
                        "    guard n < 5 else No { why = 0 }"));
    }
}
