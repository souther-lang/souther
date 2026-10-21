package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.types.ModelOccurrences;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many of some statements hold is judged on the way as a count: the statements are taken in
 * one at a time, holding and then failing, and a side is taken only where the statements after it
 * can still bring the count to one admitted. The ways a row takes through it are the assignments
 * that hold together with the rest of the way — as many as are looked along, and the figure that
 * left the rest — and a way is closed only where none of them does.
 *
 * <p>Put to the way directly, with the statements written as the conditions of a body leave them.
 */
class ACountOfStatementsIsJudgedAsACountTest {

    private static final ConditionReportAnchor WHERE =
            new ConditionReportAnchor.WhereTheReadingMetIt("m",
                    new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, 0));

    private static final int FIELDS = 20;

    private static NumericTerm term(int field) {
        return new NumericTerm.ValueOf(TermPath.of("r").then("x" + field));
    }

    /** {@code term > 0} when {@code holds}, and {@code term <= 0} when not. */
    private static OnTheWay positive(int field, boolean holds) {
        return new OnTheWay.TakenIn(WHERE, new RowDemand.Relational(
                new TakenConstraint.Affine(new LinearForm<>(ExactRatio.ZERO,
                        Map.of(term(field), ExactRatio.ONE)), holds ? Rel.GT : Rel.LE)));
    }

    /** The statement {@code x_field > 0}: what a row meets where it holds, and where it fails. */
    private static OnTheWay.Counted.Statement positiveStatement(int field) {
        return new OnTheWay.Counted.Statement(1, List.of(positive(field, true)),
                List.of(positive(field, false)));
    }

    /** The statement {@code x_field <= 0}. */
    private static OnTheWay.Counted.Statement nonPositiveStatement(int field) {
        return new OnTheWay.Counted.Statement(1, List.of(positive(field, false)),
                List.of(positive(field, true)));
    }

    private static OnTheWay.Counted counted(List<Integer> admitted,
                                            OnTheWay.Counted.Statement... statements) {
        return counted(admitted, List.of(statements));
    }

    private static OnTheWay.Counted counted(List<Integer> admitted,
                                            List<OnTheWay.Counted.Statement> statements) {
        List<Proposition> stated = IntStream.range(0, statements.size())
                .<Proposition>mapToObj(at -> new Proposition.Truth(new DecisionSubject.AnInput(
                        TermPath.of("r").then("t" + at)), true)).toList();
        return new OnTheWay.Counted(
                new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, 1), WHERE,
                statements, admitted, Proposition.SoManyHold.counting(stated,
                        statements.stream().map(_ -> 1).toList(),
                        admitted));
    }

    /** {@code count} of {@code x_0 > 0 .. x_(n-1) > 0} being {@code admitted}. */
    private static OnTheWay.Counted ofPositives(int n, int... admitted) {
        return counted(IntStream.of(admitted).boxed().toList(), IntStream.range(0, n)
                .mapToObj(ACountOfStatementsIsJudgedAsACountTest::positiveStatement).toList());
    }

    private static Reachability of(OnTheWay... onTheWay) {
        return Reachability.of(new WayToTheBorder(List.of(onTheWay)), region());
    }

    private static Reachability.Reaching reaching(Reachability reachability) {
        return assertInstanceOf(Reachability.Reaching.class, reachability,
                () -> "some way is open: " + reachability);
    }

    private static List<Reachability.Reaching> alongEach(Reachability reachability) {
        return assertInstanceOf(Reachability.Ways.Each.class, reaching(reachability).ways(),
                () -> "every way was looked along: " + reachability).along();
    }

    /**
     * Exactly one of {@code x > 0} and {@code x <= 0} holds, whatever {@code x} is: either the
     * first holds and the second fails, and then {@code x > 0} twice, or the other way round.
     */
    @Test
    void exactlyOneOfAStatementAndItsDenialIsTheTwoWaysEitherHolds() {
        List<Reachability.Reaching> ways = alongEach(of(counted(List.of(1),
                positiveStatement(0), nonPositiveStatement(0))));

        assertEquals(2, ways.size());
        assertEquals(Set.of(Rel.GT, Rel.LE), ways.stream()
                .flatMap(way -> way.boundedOnTheWay().stream())
                .map(taken -> ((TakenConstraint.Affine) ((RowDemand.Relational) taken.demand())
                        .constraint()).rel())
                .collect(Collectors.toSet()));
    }

    /**
     * Neither or both of them holding is a count no number comes to: {@code x > 0} and
     * {@code x <= 0} fail together only where {@code x} is above nought and at most nought.
     */
    @Test
    void noneAndBothOfAStatementAndItsDenialAreNoWay() {
        for (int count : new int[] {0, 2}) {
            Reachability reachability = of(counted(List.of(count),
                    positiveStatement(0), nonPositiveStatement(0)));

            assertInstanceOf(Reachability.NumbersLeaveNone.class, reachability,
                    () -> "a count of " + count + " leaves no number: " + reachability);
        }
    }

    /** The same for a truth: a value is true or false, and exactly one of the two holds. */
    @Test
    void exactlyOneOfATruthAndItsDenialIsOpenAndNoneOrBothIsNot() {
        TermPath at = TermPath.of("r").then("flag");
        OnTheWay.Counted.Statement truth = new OnTheWay.Counted.Statement(1,
                List.of(new OnTheWay.TakenIn(WHERE, new RowDemand.ATruth(at, true))),
                List.of(new OnTheWay.TakenIn(WHERE, new RowDemand.ATruth(at, false))));
        OnTheWay.Counted.Statement untrue = new OnTheWay.Counted.Statement(1,
                List.of(new OnTheWay.TakenIn(WHERE, new RowDemand.ATruth(at, false))),
                List.of(new OnTheWay.TakenIn(WHERE, new RowDemand.ATruth(at, true))));

        assertEquals(2, alongEach(of(counted(List.of(1), truth, untrue))).size());
        for (int count : new int[] {0, 2}) {
            Reachability reachability = of(counted(List.of(count), truth, untrue));

            assertInstanceOf(Reachability.NothingReaches.class, reachability,
                    () -> "a count of " + count + " leaves no value: " + reachability);
        }
    }

    /** Few enough statements for every assignment to be a way looked along: one of three. */
    @Test
    void exactlyOneOfThreeIsEachOfTheThreeWaysAndSaysNothingWasLeft() {
        List<Reachability.Reaching> ways = alongEach(of(ofPositives(3, 1)));

        assertEquals(3, ways.size());
        for (Reachability.Reaching way : ways) {
            assertEquals(1, positives(way, Rel.GT), () -> "one holds: " + way.boundedOnTheWay());
            assertEquals(2, positives(way, Rel.LE), () -> "two fail: " + way.boundedOnTheWay());
        }
    }

    private static long positives(Reachability.Reaching way, Rel rel) {
        return way.boundedOnTheWay().stream().filter(taken -> taken.demand()
                instanceof RowDemand.Relational(TakenConstraint.Affine affine)
                && affine.rel() == rel).count();
    }

    /**
     * Exactly four of eight, as many as the figure lets be looked along and the figure that left
     * the rest: a count whose assignments are past it is not said to be every way a row takes.
     * Each way holds four and fails four.
     */
    @Test
    void exactlyFourOfEightIsLookedAlongTheFirstWaysAndPastThemTheCountWhole() {
        OnTheWay.Counted counted = ofPositives(8, 4);

        Reachability.Reaching reaching = reaching(of(counted));

        Reachability.Ways.Whole whole = assertInstanceOf(Reachability.Ways.Whole.class,
                reaching.ways(), () -> "past the figure: " + reaching.ways());
        assertEquals(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG, whole.figure());
        assertEquals(List.of(counted), whole.unsplit());
        assertEquals(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum(), whole.along().size());
        for (Reachability.Reaching way : whole.along()) {
            assertEquals(4, positives(way, Rel.GT));
            assertEquals(4, positives(way, Rel.LE));
        }
    }

    /**
     * The counts either side of the figure a count was once written out at, and a count past
     * every figure there is: each is looked along the same sixteen ways, with the count whole
     * past them.
     */
    @Test
    void theNumberOfChoicesAStatementWouldWriteOutIsNoPartOfWhatIsLookedAlong() {
        for (int[] nk : new int[][] {{10, 5}, {11, 5}, {13, 6}, {20, 10}}) {
            Reachability.Reaching reaching = reaching(of(ofPositives(nk[0], nk[1])));

            Reachability.Ways.Whole whole = assertInstanceOf(Reachability.Ways.Whole.class,
                    reaching.ways(), () -> nk[0] + "," + nk[1] + ": " + reaching.ways());
            assertEquals(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum(),
                    whole.along().size(), () -> nk[0] + "," + nk[1]);
            for (Reachability.Reaching way : whole.along()) {
                assertEquals(nk[1], positives(way, Rel.GT), () -> nk[0] + "," + nk[1]);
            }
        }
    }

    /**
     * What it costs to find the ways: the statements are asked of the vocabulary once for each
     * step of each way found, and not once for each set of statements that comes to the count.
     * Twenty statements, ten of them holding, are a hundred and eighty thousand sets.
     */
    @Test
    void theStepsToFindTheWaysAreTheStatementsTimesTheWaysAndNotTheChoices() {
        Counting counting = new Counting();
        int most = CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum();

        CountedWays.Found<String> found = CountedWays.of(counting, 0, ofPositives(20, 10), most,
                true, CountedWays.Steps.ofAWay());

        if (!(found instanceof CountedWays.Found.Some<String> some)) {
            throw new AssertionError("assignments are found: " + found);
        }
        assertEquals(most, some.assignments().size());
        assertEquals(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG, some.stoppedBy());
        // One more than is handed on is looked for, and each of those shares its first steps with
        // the one before it.
        assertTrue(counting.asked <= (most + 1) * 20, "asked " + counting.asked + " times");
    }

    /** A vocabulary that holds every entry and counts how often it was asked. */
    private static final class Counting implements OneOfEach.Vocabulary<OnTheWay, Integer, String> {

        int asked;

        @Override
        public List<List<OnTheWay>> alternatives(OnTheWay entry) {
            return entry.ofSeveralWays() ? entry.alternatives() : null;
        }

        @Override
        public Set<TermPath> positions(OnTheWay entry) {
            return Set.of();
        }

        @Override
        public Integer nothing() {
            return 0;
        }

        @Override
        public OneOfEach.Step<Integer, String> with(Integer so, OnTheWay entry) {
            asked++;
            return new OneOfEach.Step.Held<>(so + 1);
        }
    }

    /**
     * Counts and choices nested in each other cost no more than a way's figure together: three
     * counts, each with more assignments than are looked along, beside a choice, are walked again
     * under every assignment of the one before, and the steps of all of them are the one figure's.
     */
    @Test
    void countsAndChoicesNestedInEachOtherAreHeldToOneFigureTogether() {
        Counting counting = new Counting();
        OnTheWay.OneOf choice = new OnTheWay.OneOf(
                new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, 2), WHERE,
                List.of(List.of(ofPositives(14, 7)), List.of(ofPositives(14, 6))),
                Optional.empty());
        List<OnTheWay> entries = List.of(ofPositives(14, 7), ofPositives(14, 5), choice);
        BiFunction<List<OnTheWay>,
                OneOfEach.Vocabulary<OnTheWay, Integer, String>,
                OneOfEach.Walked<OnTheWay, String>> walk = (each, vocabulary) -> OneOfEach.walk(
                each, vocabulary, CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT,
                CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG);

        OneOfEach.Walked<OnTheWay, String> expanded = CountedWays.walkedWithCounts(entries,
                counting, walk);

        if (!(expanded instanceof OneOfEach.Walked.Open<OnTheWay, String> open)) {
            throw new AssertionError("some ways are open: " + expanded);
        }
        assertTrue(open.stoppedBy() != null, "not every way is said to be looked at");
        assertTrue(counting.asked <= CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT.maximum(),
                "asked " + counting.asked + " times");
    }

    /**
     * A walk looks at alternatives by a figure of its own, which the steps cannot see; so each
     * walk of an assignment is charged a way's share of them, and a way is walked again no more
     * often than ways are looked along.
     */
    @Test
    void aWayIsWalkedAgainNoMoreOftenThanWaysAreLookedAlong() {
        CountedWays.Steps steps = CountedWays.Steps.ofAWay();
        int walks = 0;
        while (steps.takeAWalk()) {
            walks++;
        }

        assertEquals(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum(), walks);
        assertTrue(steps.ranOut());
    }

    /**
     * The steps are one figure for everything asked of a way: once a search has taken them, the
     * next one is handed none and says so, and neither claims a way is closed, and neither takes
     * a step more than there were.
     */
    @Test
    void theStepsOfOneSearchAreNoneLeftForTheNext() {
        Counting counting = new Counting();
        CountedWays.Steps steps = new CountedWays.Steps(30);

        CountedWays.Found<String> first = CountedWays.of(counting, 0, ofPositives(20, 10), 16,
                true, steps);
        int afterTheFirst = counting.asked;
        CountedWays.Found<String> second = CountedWays.of(counting, 0, ofPositives(20, 10), 16,
                true, steps);

        assertTrue(steps.ranOut());
        assertTrue(afterTheFirst <= 30, "asked " + afterTheFirst + " times");
        assertEquals(afterTheFirst, counting.asked, "the second takes no step");
        assertInstanceOf(CountedWays.Found.Unknown.class, second);
        assertTrue(!(first instanceof CountedWays.Found.None<String>), first::toString);
    }

    /**
     * Statements weighing two each come to an even number however they come out, so a count
     * admitting one of them admits nothing. That is the same for every row and is settled where
     * the count is read, and a way is never left open on it.
     */
    @Test
    void aCountTheWeightsAloneSettleIsNoCountOnTheWay() {
        assertThrows(IllegalArgumentException.class, () -> counted(List.of(1),
                new OnTheWay.Counted.Statement(2, List.of(positive(0, true)),
                        List.of(positive(0, false))),
                new OnTheWay.Counted.Statement(2, List.of(positive(1, true)),
                        List.of(positive(1, false)))));

        List<Proposition> two = List.of(
                new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("r").then("a")), true),
                new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("r").then("b")), true));
        Proposition.SoManyHold odd = new Proposition.SoManyHold(two, List.of(2, 2), List.of(1));

        assertEquals(Boolean.FALSE, Proposition.SoManyHold.settledByTheWeights(odd.weights(),
                odd.admitted()));
        assertEquals(new DemandReading.Read.Settled(false), DemandReading.projectedOff(null, odd,
                inputReading(), ModelOccurrences.NONE).reads().getFirst());
    }

    /**
     * A choice beside the count that no assignment survives closes the way: the walk takes the
     * count in before the alternatives are chosen, and the ways it hands on are judged whole.
     */
    @Test
    void aChoiceBesideACountThatNoAssignmentSurvivesLeavesNothing() {
        // Both of two statements hold, so x_0 > 0 and x_1 > 0 — and each alternative of the choice
        // denies one of them.
        OnTheWay.Counted both = counted(List.of(2), positiveStatement(0), positiveStatement(1));
        OnTheWay.OneOf denies = new OnTheWay.OneOf(
                new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, 2), WHERE,
                List.of(List.of(positive(0, false)), List.of(positive(1, false))),
                Optional.empty());

        Reachability reachability = of(both, denies);

        assertInstanceOf(Reachability.NumbersLeaveNone.class, reachability,
                () -> "no way is open: " + reachability);
    }

    /** And one alternative of it that some assignment survives leaves that alternative's way. */
    @Test
    void aChoiceBesideACountThatOneAssignmentSurvivesLeavesOneWay() {
        // One of two holds: x_0 > 0 and x_1 <= 0, or the other way round. The alternatives say
        // x_0 > 0 or x_1 > 0, and each fits one assignment.
        OnTheWay.Counted one = counted(List.of(1), positiveStatement(0), positiveStatement(1));
        OnTheWay.OneOf choice = new OnTheWay.OneOf(
                new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, 2), WHERE,
                List.of(List.of(positive(0, true)), List.of(positive(1, true))),
                Optional.empty());

        assertEquals(2, alongEach(of(one, choice)).size());
    }

    private static SearchRegion region() {
        return inputReading().quantities().region();
    }

    private static InputReading inputReading() {
        String fields = IntStream.range(0, FIELDS).mapToObj(at -> "x" + at + ": Int")
                .collect(Collectors.joining(", "));
        Compilation compilation = Compilation.ofSource("""
                module m

                data R = { %s, flag: Bool }
                data Yes

                behavior f : (r: R) -> Yes
                let f (r) = Yes
                """.formatted(fields), "Main");
        var inputs = compilation.db().ask(new Adequacy.Inputs("m")).value().get("f");
        assertNotNull(inputs, "the model under test compiles");
        return inputs.reading(RuleReadings.of(compilation, "m"));
    }
}
