package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertNotNull;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior comparing for equality distinguishes two things, and the rows are asked for two.
 *
 * <p>{@code retries == 3} tells the value from every other value. Written as three ranges — below,
 * at, above — the rows would be asked to cover a distinction the model does not draw, and two rows
 * that already exercise everything the behavior does would be reported one short. The second class
 * is not a range and does not have to be: what a class needs is a way to tell whether a value is in
 * it and a value that stands for it, and neither wants an interval.
 *
 * <p>Where the same position also carries an ordering comparison the ranges come back, and rightly:
 * the model has drawn the further distinction itself.
 */
class AnEqualityDividesTheValuesInTwoTest {

    private static final String MODEL = """
            module example.equal

            data GiveUp
            data Again

            behavior verdict : (retries: Int) -> GiveUp | Again
            let verdict (retries) = if retries == 3 then GiveUp else Again

            example verdict
                | "the last try" : (3) -> GiveUp
                | "not the last" : (2) -> Again
            """;

    private static final String ALSO_ORDERED = """
            module example.both

            data GiveUp
            data Again
            data Never

            behavior verdict : (retries: Int) -> GiveUp | Again | Never
            let verdict (retries) =
                if retries == 3 then GiveUp
                else if retries <= 0 then Never
                else Again

            example verdict
                | "the last try" : (3) -> GiveUp
            """;

    private static final String BOUNDED_DECIMAL = """
            module example.ratio

            data A
            data B

            data Ratio = Decimal
                invariant lo = value >= 0m
                invariant hi = value <= 1m

            behavior pick : (x: Ratio) -> A | B

            let pick (x) = if x.value == 0.5m then A else B

            example pick
                | "at the half" : (Ratio(0.5m)) -> A
            """;

    private static String reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).human(SourceNameResolver.identity());
    }

    /** The position is divided, and into the two classes the behavior tells apart. */
    @Test
    void theValueAndEverythingElseAreTheTwoClasses() {
        String human = reportOf(MODEL);

        assertTrue(human.contains("partition   axes 1"), human);
        assertFalse(notReadAbout(human, "retries"), human);
    }

    /** Two rows on either side of the equality cover it, with nothing left owed. */
    @Test
    void rowsOnEitherSideCoverIt() {
        String human = reportOf(MODEL);

        assertTrue(human.contains("equivalence partitions 2/2"), human);
        assertFalse(human.contains("no row is in"), human);
    }

    /**
     * The value itself is a row somebody owes; the value beside it is not.
     *
     * <p>A guard's line usually wants its neighbour, because the two are in different classes and an
     * off-by-one shows up between them. Here they are not: 2 and 4 are the same class, so asking for
     * 4 is asking for a row another row already stands for.
     */
    @Test
    void theValueIsOwedAndItsNeighbourIsNot() {
        String human = reportOf(MODEL);

        assertTrue(human.contains("border      borders 1   obligations 2/2"), human);
    }

    /**
     * The complement of a value in a bounded range has values, and stepping by one does not find them.
     *
     * <p>`0.5` in `[0, 1]` steps to `1.5` and `-0.5`, both outside. Neither is the answer to whether
     * the class has values — `0`, `0.1` and `1` are all in it — and a class reported as one nothing
     * can write a value for is the mistake this issue is about, one field over.
     */
    @Test
    void theComplementOfADecimalHasValuesTheStepDoesNotReach() {
        String block = generatedFor(BOUNDED_DECIMAL);

        assertFalse(block.contains("other than the ones singled out"), block);
        assertTrue(block.contains("example pick"), block);
    }

    private static String generatedFor(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> all = Adequacy.generatedOf(compilation.db(), compilation.modules().get(0));
        assertNotNull(all, "the model under test compiles");
        return GeneratedRows.of(Adequacy.offeredFor(compilation.db(),
                        souther.compiler.query.OfferingRequest.overTheModule(
                                "example.ratio", false)),
                Map.of(), SourceNameResolver.identity()).text();
    }

    /** An ordering comparison beside it is a distinction the model does draw, and is kept. */
    @Test
    void anOrderingComparisonBesideItStillDividesTheRanges() {
        String human = reportOf(ALSO_ORDERED);

        assertTrue(human.contains("partition   axes 1"), human);
        // The ordering line is still a line, so the ranges either side of it are still classes and
        // the equality's value is one more distinction on top of them rather than instead of them.
        assertTrue(human.contains("x <= 0"), human);
        assertTrue(human.contains("no row is in"), human);
    }

    /**
     * Whether any {@code not read} line of {@code block} is about {@code position}.
     *
     * <p>Asked as a line rather than as a prefix. A finding about a rule names the rule first and
     * the position after it, and one about a position names the position — so a test matching
     * `+not read: <position>+` stopped meaning anything for the first kind rather than failing,
     * which is a negative assertion that passes because the words moved.
     */
    private static boolean notReadAbout(String block, String position) {
        return block.lines().anyMatch(line -> line.contains("not read:")
                && (line.contains("not read: " + position + " ")
                        || line.contains("about `" + position + "`")));
    }
}
