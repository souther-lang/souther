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
 * A rule that writes a multiple of a position still divides that position.
 *
 * <p>{@code n > 10} and {@code 2 * n > 40} draw two lines through one position, at ten and at
 * twenty. Read by the shape the comparison arrived as, only the first of them divides anything: the
 * second is a line on an arithmetic form, and a form over several positions divides none of them. So
 * a report counts two equivalence partitions where the model states three, and the class between
 * eleven and twenty — which the model does treat differently — is one nothing is ever told about.
 *
 * <p>And the line lands on a value of the position rather than on a number it never takes.
 * {@code 2 * n <= 9} cuts the even numbers at nine, which is why the reading refused to put it on
 * the position at all: divided out, it would ask for a class of the whole numbers at four and a
 * half. Where the values part is between four and five, and that is a value the position holds.
 */
class ARuleWrittenInMultiplesStillDividesThePositionTest {

    private static List<String> classesOf(String guards) {
        Compilation compilation = Compilation.ofSource("""
                module example.scaled

                data Yes = { n: Int }
                data No = { n: Int }

                behavior f : (n: Int) -> Yes | No
                    constructs Yes, No

                let f (n) = {
                %s
                    Yes { n = n }
                }

                example f
                    | (1) -> Yes { n = 1 }
                """.formatted(guards), "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, PartitionEvidence> all = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");
        PartitionEvidence evidence = all.get("f");
        assertEquals(1, evidence.axes().size(), "the behavior takes one position");
        return evidence.axes().get(0).classes();
    }

    /**
     * Two lines through one position, one of them written in twos.
     *
     * <p>The class the model treats differently and the report did not count is the middle one: a
     * row at fifteen goes through the first guard and not the second, and nothing said that was a
     * case to cover.
     */
    @Test
    void twoRulesAtDifferentScalesDrawTwoLinesThroughOnePosition() {
        assertEquals(List.of("n/x <= 10", "n/10 < x <= 20", "n/20 < x"), classesOf("""
                    guard n > 10 else No { n = n }
                    guard 2 * n > 40 else No { n = n }"""));
    }

    /**
     * And a threshold the written form never reaches divides at a value the position holds.
     *
     * <p>Nine is not a value {@code 2 * n} takes, so there is no number to divide out. What the rule
     * does is part the whole numbers between four and five, and the classes are named by the values
     * either side rather than by half of the threshold.
     */
    @Test
    void aThresholdTheFormNeverReachesDividesAtAValueThePositionHolds() {
        assertEquals(List.of("n/x <= 4", "n/4 < x"),
                classesOf("    guard 2 * n <= 9 else No { n = n }"));
    }
}
