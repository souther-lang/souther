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
 * A partition of a position is what the model treats alike, and not what this compiler can name.
 *
 * <p>{@code 3 * d <= 1} tells 0.3 from 0.34: the behavior answers one way for one and the other way
 * for the other, so the position has two classes. What it does not have is a number to name the line
 * by — a third is no decimal this language writes — and a measure that counted the classes it could
 * write a boundary for would be reporting how far this compiler's own numbers reach rather than what
 * the model distinguishes. Which is the confusion #880 is about, one level in.
 *
 * <p>Naming them is a separate question with a separate answer. Where the line falls on a value of
 * the position, the classes are named by that value as they always were; where it does not, they are
 * named by the rule that drew it. What tells two classes apart is neither of those spellings: two
 * rules that divide a position in one place make one division however they were written.
 */
class AnEquivalencePartitionIsWhatTheModelDistinguishesTest {

    private static PartitionEvidence measured(String type, String guards) {
        Compilation compilation = Compilation.ofSource("""
                module example.exact

                data No = { why: Int }
                data Yes = { v: Int }
                data Result = No | Yes

                behavior f : (n: %s) -> Result
                    constructs Yes, No

                let f (n) = {
                %s
                    Yes { v = 1 }
                }

                example f
                    | "one" : (%s) -> Yes { v = 1 }
                """.formatted(type, guards, type.equals("Decimal") ? "0.1m" : "1"), "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, PartitionEvidence> all = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");
        return all.get("f");
    }

    private static List<String> classesOf(String type, String guards) {
        PartitionEvidence evidence = measured(type, guards);
        assertEquals(1, evidence.axes().size(),
                "the behavior takes one position and the model divides it");
        return evidence.axes().get(0).classes();
    }

    /**
     * A line at a place the position holds no value at still divides it.
     *
     * <p>Two classes, because the behavior answers two ways. The line is at a third and no decimal
     * is a third, so what names the classes is the rule.
     */
    @Test
    void aLineTheCarrierNamesNoValueAtStillDividesThePosition() {
        assertEquals(List.of("n/3 * x <= 1", "n/1 < 3 * x"),
                classesOf("Decimal", "    guard 3m * n <= 1m else No { why = 0 }"),
                "named by the rule, in numbers this language has, rather than by a third");
    }

    /**
     * And two rules that draw that line at two scales draw one line.
     *
     * <p>A third and two sixths are one place. Told apart by the numbers the rules carry, the
     * position would have three classes and the one between them would hold nothing.
     */
    @Test
    void twoScalesOfOneLineAtSuchAPlaceAreOneLine() {
        assertEquals(classesOf("Decimal", "    guard 3m * n <= 1m else No { why = 0 }"),
                classesOf("Decimal", "    guard 6m * n <= 2m else No { why = 0 }"),
                "a third and two sixths are one place, and the classes either side are the same"
                        + " two");
        assertEquals(List.of("n/3 * x <= 1", "n/1 < 3 * x"),
                classesOf("Decimal", "    guard 6m * n <= 2m else No { why = 0 }"),
                "and the name is the reduced one, so the rule that wrote it in sixths does not"
                        + " leave a class nothing else can be compared against");
    }

    /**
     * And two lines at two such places leave three classes.
     *
     * <p>The control for the test above: a reading that made every line at an unnameable place one
     * line would pass that one and fail this.
     */
    @Test
    void twoLinesAtTwoSuchPlacesLeaveThreeClasses() {
        assertEquals(List.of("n/3 * x <= 1", "n/1 < 3 * x <= 2", "n/2 < 3 * x"),
                classesOf("Decimal", """
                    guard 3m * n > 1m else No { why = 0 }
                    guard 3m * n > 2m else No { why = 1 }"""));
    }

    /**
     * And a line that does fall on a value of the position is still named by that value.
     *
     * <p>{@code 2 * n <= 9} cuts the whole numbers between four and five, and four is a value the
     * position holds. Naming every class by the rule that drew it would spell this one
     * {@code 2 * n <= 9}, which is the same set said less plainly.
     */
    @Test
    void aLineThatFallsOnAValueOfThePositionIsNamedByThatValue() {
        assertEquals(List.of("n/x <= 4", "n/4 < x"),
                classesOf("Int", "    guard 2 * n <= 9 else No { why = 0 }"));
    }
}
