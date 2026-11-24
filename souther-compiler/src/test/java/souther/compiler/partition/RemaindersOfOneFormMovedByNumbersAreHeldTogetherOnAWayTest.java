package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Quantity;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.WholeNumberRuns;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a division leaves of one form moved by a number is what it leaves of the form, moved round
 * the divisor: {@code floorMod(f + c, m)} is {@code r} exactly where {@code floorMod(f, m)} is
 * {@code floorMod(r - c, m)}. So statements of remainders of one form moved by different numbers
 * are statements of one remainder, and a way asking of it remainders that leave none in common is
 * a way no row takes.
 *
 * <p>Only a proof: remainders by another divisor, or of another form, are not read as one, and a
 * way of those is left open, which proves nothing about it either way.
 *
 * <p>Put to the way directly, with each statement written as the condition of a body leaves it.
 */
class RemaindersOfOneFormMovedByNumbersAreHeldTogetherOnAWayTest {

    private static final ConditionReportAnchor WHERE =
            new ConditionReportAnchor.WhereTheReadingMetIt("m",
                    new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, 0));

    private static final NumericTerm A = new NumericTerm.ValueOf(TermPath.of("r").then("a"));
    private static final NumericTerm D = new NumericTerm.ValueOf(TermPath.of("r").then("d"));
    private static final ValueName FLOOR_MOD = ValueName.Stdlib.operation("Int", "floorMod");

    /** Saturday on two days two apart: no remainder of the form leaves six at both. */
    @Test
    void remaindersOfAFormMovedApartThatLeaveNoneInCommonAreNoWay() {
        assertClosed(leaves(0, 7, 6, 6), leaves(2, 7, 6, 6));
    }

    /** Saturday and the Monday two days on are one remainder of the form, six. */
    @Test
    void remaindersOfAFormMovedApartThatLeaveOneInCommonAreAWay() {
        assertOpen(leaves(0, 7, 6, 6), leaves(2, 7, 1, 1));
    }

    /** A floor remainder moved below nought comes round: {@code floorMod(f - 1, 7) = 6} is
     *  {@code floorMod(f, 7) = 0}, so it holds beside that and not beside one. */
    @Test
    void aFormMovedBelowNoughtComesRoundTheDivisor() {
        assertOpen(leaves(-1, 7, 6, 6), leaves(0, 7, 0, 0));
        assertClosed(leaves(-1, 7, 6, 6), leaves(0, 7, 1, 1));
    }

    /** Runs of remainders turned round the divisor meet where some remainder is in each, and a
     *  run that crosses nought once moved is the two runs it comes to. */
    @Test
    void runsOfRemaindersMeetWhereTheyHaveOneInCommonOnceMoved() {
        assertOpen(leaves(0, 7, 1, 5), leaves(3, 7, 0, 1));
        assertClosed(leaves(0, 7, 1, 5), leaves(3, 7, 2, 3), leaves(5, 7, 0, 0));
    }

    /** By another divisor it is another remainder, which this does not read beside the first:
     *  the way is left open, which is no proof that a row takes it. */
    @Test
    void aRemainderByAnotherDivisorIsNotReadAsTheSame() {
        assertOpen(leaves(0, 7, 6, 6), leaves(0, 14, 0, 0));
    }

    /** Of the form scaled, it is a remainder of another form. */
    @Test
    void aRemainderOfAnotherFormIsNotReadAsTheSame() {
        Map<NumericTerm, ExactRatio> twice = new LinkedHashMap<>();
        twice.put(A, ExactRatio.of(2));
        twice.put(D, ExactRatio.of(-2));
        assertOpen(leaves(0, 7, 6, 6), leaves(twice, 0, 7, 6, 6));
    }

    /** A number inside a container may be of another element in each statement, so two that
     *  would leave none of one number are not read as one. */
    @Test
    void remaindersOfANumberInsideAContainerAreNotReadAsOne() {
        Map<NumericTerm, ExactRatio> element = Map.of(new NumericTerm.ValueOf(
                TermPath.of("r").then("xs").element()), ExactRatio.ONE);
        assertOpen(leaves(element, 0, 7, 6, 6), leaves(element, 2, 7, 6, 6));
    }

    /** A form weighed by a number that is not whole may stand between whole numbers, and a
     *  remainder of it moved is not shown to be the remainder of the form turned round: two such
     *  statements that would leave none of a whole form are not read as one. */
    @Test
    void aFormWeighedByWhatIsNotWholeIsNotReadAsOne() {
        Map<NumericTerm, ExactRatio> half = Map.of(A, ExactRatio.of(BigInteger.ONE,
                BigInteger.TWO));
        assertOpen(leaves(half, 0, 7, 6, 6), leaves(half, 2, 7, 6, 6));
    }

    /** Closed by the way's own reading and by the search for what no input takes alike, on the
     *  same statements. */
    private static void assertClosed(OnTheWay... onTheWay) {
        WayToTheBorder way = new WayToTheBorder(List.of(onTheWay));
        Reachability read = Reachability.of(way, region());
        Reachability.NumbersLeaveNone numbers = assertInstanceOf(
                Reachability.NumbersLeaveNone.class, read,
                () -> "remainders that leave none in common are a way no row takes: " + read);
        Optional<NoInputTakesIt> none = way.takenByNoInput(region(), () -> true);
        assertEquals(Optional.of(new NoInputTakesIt.TheConditionsClash(
                new NoInputTakesIt.Clash.RemaindersLeaveNone(numbers))), none);
    }

    private static void assertOpen(OnTheWay... onTheWay) {
        WayToTheBorder way = new WayToTheBorder(List.of(onTheWay));
        assertInstanceOf(Reachability.Reaching.class, Reachability.of(way, region()));
        assertEquals(Optional.empty(), way.takenByNoInput(region(), () -> true));
    }

    /** {@code floorMod(a - d + moved, divisor)} held to the remainders from {@code low} to
     *  {@code high}. */
    private static OnTheWay leaves(long moved, long divisor, long low, long high) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(A, ExactRatio.ONE);
        coefs.put(D, ExactRatio.of(-1));
        return leaves(coefs, moved, divisor, low, high);
    }

    private static OnTheWay leaves(Map<NumericTerm, ExactRatio> coefs, long moved, long divisor,
                                   long low, long high) {
        Quantity.RemainderOfADividend remainder = Quantity.RemainderOfADividend.ofTheInput(
                FLOOR_MOD, new LinearForm<>(ExactRatio.of(moved), coefs),
                BigInteger.valueOf(divisor));
        return new OnTheWay.TakenIn(WHERE, new RowDemand.OnARemainder(remainder,
                WholeNumberRuns.one(BigInteger.valueOf(low), BigInteger.valueOf(high))),
                NamedElements.NONE);
    }

    private static SearchRegion region() {
        Compilation compilation = ACompiledModel.answered("""
                module m

                data R = { a: Int, d: Int, xs: List<Int> }
                data Yes

                behavior f : (r: R) -> Yes
                let f (r) = Yes
                """);
        var inputs = compilation.db().ask(new Adequacy.Inputs("m")).value().get("f");
        assertNotNull(inputs, "the model under test compiles");
        return inputs.reading(RuleReadings.of(compilation, "m")).quantities().region();
    }
}
