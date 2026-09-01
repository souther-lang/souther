package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * One model taken apart in the parameter's pattern and taken apart by a helper is one model.
 *
 * <p>A helper applied to an argument is left as the helper's body under a name bound to that
 * argument, and the names it binds are the helper's own. Where the reading stopped at that shape,
 * every claim written through a helper was about a position it could not name — so the same rule,
 * over the same values, was measured where an author had destructured in the parameter and silent
 * where they had written a function to do it.
 *
 * <p>Held as an equality between the two answers rather than as what each of them is. What either
 * one comes to is a question about the rules the models state and is answered where those rules are
 * read; what is here is that it is not a question about which of the two spellings was used.
 *
 * <p>And at four helpers as well as one, because a reading that stopped somewhere between them would
 * be reporting how far it got as what a model says.
 */
class HowAWrapperIsTakenApartDoesNotChangeWhatIsReadTest {

    private static final String TAKEN_APART_IN_THE_PARAMETER = """
            module example.apart

            data Line = { amount: Int }
            data Batch = List<Line>
            data Large
            data Small

            behavior judge : (batch: Batch) -> Large | Small
            let judge (Batch(lines)) =
                if List.sum(List.map(one -> one.amount, lines)) >= 100000
                then Large else Small
            """;

    private static final String TAKEN_APART_BY_A_HELPER = """
            module example.apart

            data Line = { amount: Int }
            data Batch = List<Line>
            data Large
            data Small

            behavior judge : (batch: Batch) -> Large | Small

            let opened (Batch(lines)): List<Line> = lines

            let judge (batch) =
                if List.sum(List.map(one -> one.amount, opened(batch))) >= 100000
                then Large else Small
            """;

    private static final String TAKEN_APART_BY_FOUR_HELPERS = """
            module example.apart

            data Line = { amount: Int }
            data Batch = List<Line>
            data Large
            data Small

            behavior judge : (batch: Batch) -> Large | Small

            let opened (Batch(lines)): List<Line> = lines
            let onceMore (b: Batch): List<Line> = opened(b)
            let twiceMore (b: Batch): List<Line> = onceMore(b)
            let thriceMore (b: Batch): List<Line> = twiceMore(b)

            let judge (batch) =
                if List.sum(List.map(one -> one.amount, thriceMore(batch))) >= 100000
                then Large else Small
            """;

    private static PartitionEvidence measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        PartitionEvidence judged = compilation.db()
                .ask(new Adequacy.Coverage("example.apart")).value().get("judge");
        assertNotNull(judged, "the model under test compiles");
        return judged;
    }

    /**
     * The positions the two are measured over are the same positions.
     *
     * <p>Which is the reading's own answer, held apart from what the rules over them come to: a
     * model whose wrapper a helper takes apart names the sequence and what its elements hold, as one
     * whose parameter takes it apart does.
     */
    @Test
    void aHelperAndAParameterPatternNameTheSamePositions() {
        assertEquals(positionsOf(TAKEN_APART_IN_THE_PARAMETER),
                positionsOf(TAKEN_APART_BY_A_HELPER),
                "the wrapper is taken apart either way, and the rule is about the same values");
    }

    /** And at four helpers, which is the same model again. */
    @Test
    void andAtFourHelpers() {
        assertEquals(positionsOf(TAKEN_APART_IN_THE_PARAMETER),
                positionsOf(TAKEN_APART_BY_FOUR_HELPERS),
                "how many names the reading passes through is not what the model says");
    }

    /**
     * And the rule is one this reading placed, in both.
     *
     * <p>What the equality above would not catch on its own: two readings that both said nothing
     * are equal. The threshold is over what a run of a sequence adds up to, so what is reported is
     * that the rule is about the total rather than about the elements — and reporting that at all
     * takes having read the run, which is the capability the helper used to hide.
     */
    @Test
    void andTheRuleIsPlacedInBoth() {
        assertTrue(measured(TAKEN_APART_BY_A_HELPER).rulesWithoutALine().stream()
                        .anyMatch(each -> each.at().toString().contains("amount")),
                () -> "the rule is over the sum of what the elements hold: "
                        + measured(TAKEN_APART_BY_A_HELPER).rulesWithoutALine());
    }

    /**
     * And the threshold on the total is asked for, at the number the model wrote.
     *
     * <p>What the equalities above hold is that the two spellings answer alike, and two silences
     * are alike. This says what the answer is: the model compares a total against a hundred
     * thousand, so the reading reaches that comparison, cuts there, and plans a row that puts the
     * total exactly on it.
     *
     * <p>Asserted of the model taken apart by a helper, which is the one that used to say nothing.
     * Read from what the measure carries rather than from the report's text, since what is being
     * held is that the question was asked and not how it is printed.
     */
    @Test
    void andTheThresholdOnTheTotalIsAskedForAtTheNumberTheModelWrote() {
        String said = whatWasMeasured(TAKEN_APART_BY_A_HELPER + ROWS);

        assertTrue(said.contains("QuantityCut[at=100000]"),
                () -> "the total is cut at the number the model compares against: " + said);
        assertTrue(said.contains("AtTheLevel[at=100000]"),
                () -> "and the point on the line is met by a total of exactly that: " + said);
        assertTrue(said.contains("List.sum(batch[*].amount) = 100000"),
                () -> "which is a point about the total of what the elements hold: " + said);
        assertTrue(said.contains("Line { amount = 100000 }"),
                () -> "and a row is planned that puts it there: " + said);
    }

    /** An example, so the offering is worked out and the row planned for the point is in it. */
    private static final String ROWS = """

            example judge
                | "small" : (Batch([ Line { amount = 1 } ])) -> Small
            """;

    /** The whole of what one behavior's measure came to, as it stands. */
    private static String whatWasMeasured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return souther.compiler.report.AdequacyReport.of(compilation)
                .modules().get(0).behaviors().get(0).evidence().toString();
    }

    /** Which positions a model is measured over, in the order the reading answers them. */
    private static java.util.List<String> positionsOf(String source) {
        return measured(source).notDerivable().stream()
                .map(each -> each.at() + " " + each.why()).sorted().toList();
    }
}
