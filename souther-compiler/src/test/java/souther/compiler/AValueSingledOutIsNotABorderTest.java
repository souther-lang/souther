package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.check.CoverageObligation;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A value a rule singles out is not a border, and is not asked about as one.
 *
 * <p>A border has an order across it: rows are owed either side, and each side has a role a document
 * names ({@code ON} and {@code OFF}). {@code x == c} and {@code x /= c} place the same thing and it
 * is not that — what they tell apart is {@code c} from every other value, and the values either side
 * of {@code c} are one class. {@code ComparisonClaim.Singled} says as much: reading it as a place to
 * cut puts an order between the two sides that the model never drew.
 *
 * <p>So the question is its own. Raising {@code BOUNDARY} for it would bring the order the rule never
 * drew back in through the words a reader is given, which is the same fabrication one level up from
 * reading an equality as a cut.
 *
 * <p>Only a comparison nothing could read shows this: one the reading takes in leaves no question
 * standing, so what is asserted below is what a rule asks when nothing has answered.
 */
class AValueSingledOutIsNotABorderTest {

    /** The condition, with a bound this compiler cannot fold, so the questions survive. */
    private static Set<CoverageObligation> raisedBy(String condition) {
        Compilation compilation = Compilation.ofSource("""
                module m

                data R = { cost: Int, a: Int, other: Int }
                data A
                data B

                behavior b : (r: R) -> A | B
                    constructs A, B
                let b (r) = if %s then A else B

                example b
                    | "one" : (R { cost = 1, a = 1, other = 2 }) -> B
                """.formatted(condition), "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        PartitionEvidence partition = AdequacyReport.of(compilation)
                .modules().get(0).behaviors().get(0).partition();
        Set<CoverageObligation> out = new LinkedHashSet<>();
        partition.unanswered().forEach(each -> out.add(each.question()));
        return out;
    }

    /** An order across the value it names: a border, and the classes either side of it. */
    @Test
    void anOrderingComparisonAsksAboutABorder() {
        assertEquals(Set.of(CoverageObligation.BOUNDARY, CoverageObligation.PARTITION),
                raisedBy("r.cost <= 10 * 2"));
    }

    /** And an equality asks about the value it singles out, beside the same classes. */
    @Test
    void anEqualityAsksAboutTheValueItSinglesOut() {
        assertEquals(Set.of(CoverageObligation.SINGLETON, CoverageObligation.PARTITION),
                raisedBy("r.cost == 10 * 2"));
    }

    /**
     * Between two positions it singles nothing out, whatever the operator is.
     *
     * <p>What a comparison places is the operator's, and what it places it about is not: {@code x ==
     * 10} tells one value from every other and {@code a == b} says where one position stands against
     * another. Read off the operator alone, the second raised a question about a value singled out at
     * {@code a} that no rule wrote — and an equality between two positions is not even a line, since
     * it puts the whole of one arm on the place and that arm is a row the branch measure already
     * asks for.
     */
    @Test
    void anEqualityBetweenTwoPositionsSinglesNothingOut() {
        assertEquals(Set.of(), raisedBy("r.a == r.other"),
                "a rule about a pair, and no question about one of them");
        assertEquals(Set.of(), raisedBy("r.a /= r.other"));
    }

    /**
     * Both sides moving with the row is a relation, whatever names appear on them.
     *
     * <p>What decides it is not how many positions are named. {@code a <= a + 1} names one, twice,
     * and is a rule about how a position stands against itself; {@code a <= b + 1} names two and is
     * not a line between them that anything here draws. Counted by distinct names, the first came
     * back as a bound on {@code a} — a question about where {@code a} stops that no rule wrote.
     */
    @Test
    void bothSidesMovingWithTheRowIsARelation() {
        assertEquals(Set.of(), raisedBy("r.a <= r.other + 1"),
                "two positions, and no bound on either");
        assertEquals(Set.of(), raisedBy("r.a <= r.a + 1"),
                "one name twice is still both sides moving");
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
        assertEquals(Set.of(CoverageObligation.SINGLETON, CoverageObligation.PARTITION),
                raisedBy("r.cost /= 10 * 2"));
    }
}
