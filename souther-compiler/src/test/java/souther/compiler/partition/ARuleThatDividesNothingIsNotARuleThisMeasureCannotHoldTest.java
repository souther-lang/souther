package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.RuleWithoutALine;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * Two rules read from end to end that draw no line, and they are not the same news.
 *
 * <p>One of them divides nothing: {@code a - a > 0} names the position and states something about a
 * number the position does not appear in, so there is no class in it to have found. The other
 * divides the position in two — the strings a format accepts and the rest — and what is absent is
 * a line, because what this measure holds a class as is an interval on an order.
 *
 * <p>Neither is a position the model divides no way, and their verdicts do not tell them apart:
 * what a verdict says is how far the readings got, and these two got equally far. What differs is
 * why no line came of the rule, and the reason is where that lives — so the difference is held
 * there, which is the only place it can be held at all.
 *
 * <p><b>Which is what stops the next over-generalisation.</b> A reading that gave every rule
 * without a line the word for a division it cannot represent would say the model divides a position
 * that it does not, which is the mistake this pair was written after, made the other way round
 * (issue #1249).
 */
class ARuleThatDividesNothingIsNotARuleThisMeasureCannotHoldTest {

    /** A rule about a number the position cancels out of, which divides nothing. */
    private static final String DIVIDES_NOTHING = """
            module probe

            data Ok

            data N = Int
                invariant nothing = value - value > 0

            behavior read : (n: N) -> Ok
            let read (n) = Ok
            """;

    /** A rule that divides the position into strings, which no order holds. */
    private static final String DIVIDES_WITHOUT_AN_ORDER = """
            module probe

            data Ok

            data N = String
                invariant format = String.matches("T[0-9]{3}", value)

            behavior read : (n: N) -> Ok
            let read (n) = Ok
            """;

    /**
     * Neither is a position the model divides no way, which is the claim they were both filed under.
     *
     * <p>The one thing both have to have. Each states a rule about the position it is at, so a
     * verdict saying the model divides it no way denies the declaration two tokens away — and that
     * is what a format got, because nothing recorded it as a rule the reading had finished with
     * (issue #1249).
     */
    @Test
    void neitherIsAPositionTheModelDividesNoWay() {
        for (String source : List.of(DIVIDES_NOTHING, DIVIDES_WITHOUT_AN_ORDER)) {
            List<UndividedPosition> undivided = partitioningOf(source).undivided();
            assertEquals(1, undivided.size(), undivided.toString());
            assertFalse(undivided.get(0).why() instanceof UndividedPosition.Why.Absent, source);
        }
    }

    /**
     * And the format is a reading that finished, which is the half that moved.
     *
     * <p>Said of this one alone. What verdict the other comes to is a fact about which readings stop
     * on an arithmetic that cancels, and holding both to one answer here would be this test claiming
     * something it was not written to be about.
     */
    @Test
    void theFormatIsAReadingThatRanToTheEnd() {
        assertInstanceOf(UndividedPosition.Why.StatedWithoutALine.class,
                partitioningOf(DIVIDES_WITHOUT_AN_ORDER).undivided().get(0).why(),
                "the rule was taken in; what is absent is a line");
    }

    /** And what tells them apart is the reason, which is the only place the difference is. */
    @Test
    void whatTellsThemApartIsTheReason() {
        assertEquals(List.of(UndividedPosition.Reason.RULE_CUTS_NOTHING),
                reasonsOf(DIVIDES_NOTHING),
                "a rule about a number the position cancels out of divides nothing");
        assertEquals(List.of(UndividedPosition.Reason.PARTITION_NOT_REPRESENTABLE),
                reasonsOf(DIVIDES_WITHOUT_AN_ORDER),
                "a format divides the position, and no interval says which values are in");
    }

    /** The words the rules of one model come to, in the order they are held. */
    private static List<UndividedPosition.Reason> reasonsOf(String source) {
        return partitioningOf(source).rulesWithoutALine().stream()
                .map(RuleWithoutALine::why)
                .map(ReportedReason::of)
                .toList();
    }

    private static Partitions.Partitioning partitioningOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(each -> each.name().equals("read")).findFirst().orElseThrow();
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        return Partitions.of(spec.name(),
                InputDomain.of(spec, sigs.get("read"), symbols,
                        souther.compiler.query.ReadAs.THE_COMPILATION_DOES),
                symbols, souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
    }
}
