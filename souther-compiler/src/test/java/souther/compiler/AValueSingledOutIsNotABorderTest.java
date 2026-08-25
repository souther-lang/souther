package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A value a rule singles out is not a border, and no border is built on it.
 *
 * <p>A border has an order across it: rows are owed either side, and each side has a role a document
 * names ({@code ON} and {@code OFF}). {@code x == c} and {@code x /= c} place the same thing and it
 * is not that — what they tell apart is {@code c} from every other value, and the values either side
 * of {@code c} are one class. Reading it as a place to cut puts an order between the two sides that
 * the model never drew.
 *
 * <p><b>What the comparison is about is the canonical comparison's answer.</b> Positions named on
 * either side establish nothing on their own: {@code r.a <= r.a + 1} names one twice and cancels,
 * and {@code r.a <= r.other * r.other} names two and stops the reading before anything is known
 * about what it divides. Both were read as orders between two things that move with the row, and
 * both had a border collected for them.
 */
class AValueSingledOutIsNotABorderTest {

    private static final String SOURCE = """
                module m

                data R = { cost: Int, a: Int, other: Int }
                data A
                data B

                behavior b : (r: R) -> A | B
                let b (r) = if %s then A else B

                example b
                    | "one" : (R { cost = 1, a = 1, other = 2 }) -> B
                """;

    private static PartitionEvidence measured(String condition) {
        Compilation compilation = Compilation.ofSource(SOURCE.formatted(condition), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).modules().get(0).behaviors().get(0).partition();
    }

    /** The classes the rules divide the behavior's positions into, each named as a document names
     *  it. */
    private static List<String> classes(String condition) {
        return measured(condition).axes().stream()
                .flatMap(each -> each.classes().stream()).toList();
    }

    /** How many borders the rules draw, which is what a rule placing no order across a value does
     *  not add to. */
    private static int borders(String condition) {
        return measured(condition).boundaries().size();
    }

    /** What the rules left unread, as the position and the reason. */
    private static List<String> notRead(String condition) {
        return measured(condition).notRead().stream()
                .map(each -> each.at() + ": " + each.reason()).toList();
    }

    /** An order across the value it names: the classes either side of it, and a border between
     *  them. */
    @Test
    void anOrderingComparisonDividesThePositionAndDrawsABorder() {
        assertEquals(List.of("r.cost/x <= 20", "r.cost/20 < x"), classes("r.cost <= 20"));
        assertEquals(1, borders("r.cost <= 20"));
    }

    /**
     * And an equality divides the position into the value and everything else.
     *
     * <p>One class of its own and one class of the rest, which is a partition and not an order: the
     * values either side of twenty are the same class, so nothing is owed away from a line between
     * them.
     */
    @Test
    void anEqualityPutsTheValueInAClassOfItsOwn() {
        assertEquals(List.of("r.cost/= 20", "r.cost//= 20"), classes("r.cost == 20"));
    }

    /**
     * So does a disequality, which places the same thing and selects the other class.
     *
     * <p>The two are one partition — {@code {c}} and everything else — and differ in which of the
     * two the comparison holds at. A vocabulary that told them apart here would be recording which
     * side a body took, which is the branch measure's and not this one's.
     */
    @Test
    void andSoDoesADisequality() {
        assertEquals(classes("r.cost == 20"), classes("r.cost /= 20"));
    }

    /**
     * An order the canonical comparison reads as one over two positions is a border and no classes.
     *
     * <p>The line is where the two sides hold one count, so it is on neither of them and divides
     * neither.
     */
    @Test
    void anOrderCanonicallyRelatingTwoPositionsIsABorderAndNoClasses() {
        assertEquals(List.of(), classes("r.a <= r.other"));
        assertEquals(1, borders("r.a <= r.other"));
    }

    /**
     * A comparison whose reading stopped relates nothing yet, so no border is built from how it was
     * spelled.
     *
     * <p>Both positions are named, as they are for a relation that was read. What is not known is
     * whether the rule divides one of them or relates the pair — the product is where the reading
     * stopped — so a border collected here would be one the spelling asked for.
     */
    @Test
    void anOrderTheReadingStoppedOnRelatesNothingYet() {
        assertEquals(List.of(), classes("r.a <= Int.multiply(r.other, r.other)"));
        assertEquals(0, borders("r.a <= Int.multiply(r.other, r.other)"));
        assertEquals(List.of("r.a: UNSUPPORTED_SYNTAX", "r.other: UNSUPPORTED_SYNTAX"),
                notRead("r.a <= Int.multiply(r.other, r.other)"));
    }

    /**
     * And one whose positions cancel relates nothing at all.
     *
     * <p>{@code r.a <= r.a + 1} puts a position on either side and is {@code 0 <= 1}: every row
     * satisfies it, and there is no second position for a class to be about. Counted by which sides
     * move with the row, it came back a relation and owed a row where two positions hold one count.
     */
    @Test
    void anOrderWhosePositionsCancelRelatesNothing() {
        assertEquals(List.of(), classes("r.a <= r.a + 1"));
        assertEquals(0, borders("r.a <= r.a + 1"));
        assertEquals(List.of("r.a: RULE_CUTS_NOTHING"), notRead("r.a <= r.a + 1"));
    }

    /**
     * An equality over two positions singles one out of neither, so nothing is drawn.
     *
     * <p>It puts the whole of one arm on the place the two meet, and that arm is a row the branch
     * measure already asks for. Read off the operator alone, {@code a == b} raised a question about
     * a value singled out at {@code a} that no rule wrote.
     */
    @Test
    void anEqualityBetweenTwoPositionsSinglesNothingOut() {
        assertEquals(List.of(), classes("r.a == r.other"));
        assertEquals(0, borders("r.a == r.other"));
        assertEquals(0, borders("r.a /= r.other"));
    }
}
