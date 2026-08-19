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

    /** The condition, with a bound this compiler cannot fold, so the questions survive. */
    private static Set<CoverageObligation> raisedBy(String condition) {
        Compilation compilation = Compilation.ofSource(
                SOURCE.formatted(condition), "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        PartitionEvidence partition = AdequacyReport.of(compilation)
                .modules().get(0).behaviors().get(0).partition();
        Set<CoverageObligation> out = new LinkedHashSet<>();
        partition.unanswered().forEach(each -> out.add(each.question()));
        return out;
    }

    /** The questions themselves, for a row that is about what they are about. */
    private static java.util.List<PartitionEvidence.Unanswered> raisedWith(String condition) {
        Compilation compilation = Compilation.ofSource(SOURCE.formatted(condition), "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .modules().get(0).behaviors().get(0).partition().unanswered();
    }

    /** What the questions of that condition are about, as a report names them. */
    private static Set<String> subjectsOf(String condition) {
        return raisedWith(condition).stream().map(each -> each.subject().toString())
                .collect(java.util.stream.Collectors.toCollection(LinkedHashSet::new));
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
     * Both sides moving with the row is a relation, and an order across it is still a line.
     *
     * <p>What decides which it is is not how many positions are named: {@code a <= a + 1} names one,
     * twice, and is a rule about how a position stands against itself. Counted by distinct names,
     * that came back as a bound on {@code a} — a question about where {@code a} stops that no rule
     * wrote.
     *
     * <p>The line is where the two sides hold one count, so it is on neither of them and divides
     * neither: a border, and no classes. Raised whether or not this compiler can find that place —
     * {@code a <= b} and {@code a <= b + 1} relate two positions alike (ADR-0090), and only one of
     * them is a place this can name today. Which is the whole of the difference between a question
     * and an answer.
     */
    @Test
    void anOrderBetweenTwoThingsThatMoveIsABorderAndNoClasses() {
        assertEquals(Set.of(CoverageObligation.BOUNDARY), raisedBy("r.a <= r.other + 1"));
        assertEquals(Set.of(CoverageObligation.BOUNDARY), raisedBy("r.a <= r.a + 1"),
                "one name twice is still both sides moving");
    }

    /**
     * And the place it names is the comparison that drew it, which tells two of them apart.
     *
     * <p>Writing the place out takes both sides in a vocabulary this compiler has, and it has none
     * for {@code r.other + 1}: the best it could print was {@code r.a = r.other}, a place that rule
     * never stopped, and {@code + 1} and {@code + 2} came out as one subject. Named by the
     * comparison, the subject is exact — which is only true while the comparison travels as itself,
     * so this asks what it is and not what it is called.
     */
    @Test
    void theBorderOfARelationIsNamedByTheComparisonThatDrewIt() {
        java.util.List<souther.compiler.diag.Citation> drawn =
                raisedWith("r.a <= r.other + 1 && r.a <= r.other + 2").stream()
                        .map(PartitionEvidence.Unanswered::subject)
                        .map(souther.compiler.check.Owed.Subject.OfComparison.class::cast)
                        .map(souther.compiler.check.Owed.Subject.OfComparison::at)
                        .toList();

        assertEquals(2, drawn.size(), () -> "one line each: " + drawn);
        assertEquals(2, Set.copyOf(drawn).size(),
                () -> "and two places, not one sentence twice: " + drawn);
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
