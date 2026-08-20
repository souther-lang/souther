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
        return classesOf("Int", clause, body);
    }

    private static List<String> classesOf(String type, String clause, String body) {
        Compilation compilation = Compilation.ofSource("""
                module example.parted

                data No = { why: Int }
                data Yes = { v: Int }
                data Result = No | Yes

                behavior f : (n: %s) -> Result
                    constructs Yes, No
                %s

                let f (n) = {
                %s
                    Yes { v = 1 }
                }

                example f
                    | "one" : (%s) -> Yes { v = 1 }
                """.formatted(type, clause, body,
                        type.equals("Decimal") ? "0.1m" : "1"), "Main");
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
     * And where the two operators are two divisions, they leave the value between them.
     *
     * <p>Over a carrier whose values fill, {@code <= 0.5} keeps the number and {@code < 0.5} gives
     * it away, so together they part the decimals twice and what lies between the two lines is that
     * number and nothing else. Ordered by a value either of them names — both name it — the two
     * came out in whichever order they were read, and one of the readings left the number in the
     * class on each side of itself. A position's classes are exclusive, so that is not a partition
     * at all and the classifier reading a row against it has no answer.
     */
    @Test
    void twoDivisionsAtOneNumberLeaveThatNumberBetweenThem() {
        assertEquals(List.of("n/x < 0.5", "n/0.5 <= x <= 0.5", "n/0.5 < x"),
                classesOf("Decimal", "    ensures asked = Yes -> n <= 0.5m",
                        "    guard n < 0.5m else No { why = 0 }"));
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
