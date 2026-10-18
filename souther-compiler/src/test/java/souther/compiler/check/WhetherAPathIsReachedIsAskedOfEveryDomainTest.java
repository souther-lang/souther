package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.collect.AppendOnly;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Severity;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.OrderedIntervals;
import souther.compiler.numeric.Text;
import souther.compiler.numeric.WholeNumberRuns;
import souther.compiler.values.AdmittedPlan;
import souther.compiler.values.Allowance;
import souther.compiler.values.AsACompilationAllows;
import souther.compiler.values.PlannedValues;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import org.junit.jupiter.api.Test;
import java.math.BigInteger;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A construction under guards that cannot all hold is not reported, whichever domain holds the
 * contradiction.
 *
 * <p>A guard reaches whatever domain has a word for what it says. A comparison reaches the numbers;
 * a predicate about a list reaches the facts and says nothing to the numbers. So the conditions on
 * a path can come to contradict in one domain while every other is untouched, and a reader asking
 * a single domain whether the path is reached walks it whenever it asked the domain that had never
 * heard of the guards. What it then reports is a violation on a path the program never takes.
 *
 * <p>Which domain is not something the author chose, so the programs below are the same program
 * twice with the contradiction moved. What made the difference visible is a clause that only the
 * numbers have a word for: a state at bottom proves everything, so a clause the contradicted domain
 * can read comes out discharged by that alone, and the two readings agree for a reason that has
 * nothing to do with the path. {@code List.length(value) >= 1} over a container built by
 * {@code List.append} is such a clause — no guard could be written about the built container, so it
 * is owed as a number and as nothing else.
 */
class WhetherAPathIsReachedIsAskedOfEveryDomainTest {

    private static final String NEL = """
            module demo
            data Bad
            data NEL = List<Int>
                invariant nonEmpty = List.length(value) >= 1
            behavior f : (a: List<Int>, b: List<Int>) -> NEL | Bad constructs NEL
            """;

    /** What this compile warns about, as the codes it says it under. The codes and not how many
     * there are: a path that is walked and a path that is not differ by one warning either way, and
     * a count would be answered the same by a compile that lost the report and by one that swapped
     * it for another. */
    private static List<String> warnedAbout(String source) {
        return Compiler.compileWithWarnings(source).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING)
                .map(Diagnostic::code)
                .toList();
    }

    /**
     * Guards that cannot both hold as a comparison, which is the domain the reading always asked.
     *
     * <p>This one holds whether or not the walk asks anything: a numeric clause under numbers that
     * contradict is proved by the contradiction itself. So it is here to say what the answer is and
     * not to catch a walk that stopped asking — the case below is the one that does that.
     */
    @Test
    void aPathTheNumbersRuleOutIsNotWalked() {
        // The construction is said nothing about; the branch holding it is said to be one nothing
        // reaches, which is the same contradiction read for the other question.
        assertEquals(List.of("E1327"), warnedAbout(NEL + """
                let f (a, b) =
                    if List.length(a) >= 5 then
                        Bad
                    else
                        (if List.length(a) >= 10 then NEL(List.append(a, b)) else Bad)
                """),
                "nothing of length under five is of length ten, so nothing builds this");
    }

    /** The same guards as a predicate, which reaches no number at all. */
    @Test
    void aPathThePredicatesRuleOutIsNotWalked() {
        assertEquals(List.of("E1327"), warnedAbout(NEL + """
                let f (a, b) =
                    if List.contains(1, a) then
                        Bad
                    else
                        (if List.contains(1, a) then NEL(List.append(a, b)) else Bad)
                """),
                "a list both holding and not holding one is no list, so nothing builds this");
    }

    /**
     * And the construction is still reported where the guards can hold.
     *
     * <p>Without this the two above are passed by a check that stopped reading conditionals
     * altogether: what they say is that these constructions go unreported, and going unreported is
     * what a walk that reads nothing does everywhere.
     */
    @Test
    void aPathThatIsReachedIsWalkedAndWhatStandsOnItIsReported() {
        assertEquals(List.of("E2011"), warnedAbout(NEL + """
                let f (a, b) =
                    if List.contains(1, a) then
                        Bad
                    else
                        (if List.contains(2, a) then NEL(List.append(a, b)) else Bad)
                """),
                "a list may hold two and not one, and nothing there says the built list is not empty");
    }

    // --- the question itself -------------------------------------------------------------------

    private static final Term.Interner NAMES = new Term.Interner();
    private static final FactSubject A_PREDICATE = FactSubject.of(NAMES.written("some predicate"));
    private static final FactSubject A_POSITION = FactSubject.of(NAMES.written("some position"));

    /**
     * Each domain at its own bottom, asked of the walk's own question.
     *
     * <p>Written here as well as over the programs above because a program can only reach the
     * domains the walk refines today — the guards settle numbers and predicates, and nothing on a
     * path names a value or moves an end. A domain that cannot hold a path's contradiction this year
     * can hold one the year a guard learns to speak to it, and the question has to be right before
     * then rather than after.
     */
    @Test
    void aPathIsReachedOnlyWhereEveryDomainLeavesSomething() {
        assertFalse(Known.top().reachesNothing(), "nothing taken in leaves the path as it was");
        assertTrue(reaching(numbersAtBottom()).reachesNothing());
        assertTrue(reaching(factsAtBottom()).reachesNothing());
        assertTrue(reaching(valuesAtBottom()).reachesNothing());
        assertTrue(reaching(orderedAtBottom()).reachesNothing());
    }

    /**
     * What the walk says of a path it has been told is not taken, and of the values there.
     *
     * <p>The saying reaches the state and no domain of it. Written into the numbers, as
     * {@code 1 <= 0}, it read as an arithmetic claim the model never made — so a reader asking why
     * nothing satisfies the state was told the rules about numbers conflict, and a reader asking
     * whether the path is reached was answered by {@code numbers.isBottom()}, which is the reading
     * that walked a path the predicates alone ruled out.
     */
    @Test
    void aPathSaidNotToBeTakenIsNotTakenAndNoDomainIsMadeToSaySo() {
        Known nothing = Known.top().reachingNothing();
        assertTrue(nothing.reachesNothing());
        assertFalse(nothing.numbers().isBottom(), "no domain was made to carry the argument");
        assertFalse(nothing.facts().isBottom());
        assertFalse(nothing.constraints().confinement().holdsNothing());
        assertFalse(nothing.unguarded().constraints().isBottom(),
                "it is the guards that cannot all hold, not the values that fail");
    }

    /**
     * The values a position's rules name, beside a range the path took in about the same position.
     *
     * <p>Two domains holding halves of one contradiction. The range {@code 2 <= x < 3} has values in
     * it and the set {@code {1, 3, 7}} has values in it; that none of the set is in the range is
     * found only where the two are put to one position, which is what the state does with a range
     * the numbers leave and the values a reading holds.
     */
    @Test
    void aRangeOnThePathBetweenTheValuesTheRulesNameLeavesNothing() {
        Known odd = admittingOdd(Known.top());
        assertFalse(odd.reachesNothing(), "the values alone leave three");

        assertTrue(between(odd, 2, 3).reachesNothing(),
                "no value of 1, 3 and 7 lies at or above 2 and below 3");
        assertFalse(between(odd, 2, 4).reachesNothing(), "3 lies at or above 2 and below 4");
        assertFalse(between(Known.top(), 2, 3).reachesNothing(),
                "and without the values, the range alone holds 2");
    }

    /** The same on an order with no arithmetic, where the path holds the range on the order. */
    @Test
    void aRangeOnAnOrderBetweenTheStringsTheRulesNameLeavesNothing() {
        Allowance<FactSubject> sets = AsACompilationAllows.forAdmittedValues();
        Known code = Known.top().admitting(new Confinement.Planned<>(
                PlannedValues.at(A_POSITION, AdmittedPlan.of(new ValueSet.Finite(Set.of(
                        Value.text("a"), Value.text("c"), Value.text("e"))))),
                OrderedIntervals.top(), Map.of(A_POSITION, Carrier.TEXT)).resolve(sets), sets);

        assertTrue(code.bounding(OrderedIntervals.at(A_POSITION, new OrderedInterval(
                        Endpoint.inclusive(new Text("b")), Endpoint.exclusive(new Text("c")))),
                Map.of(A_POSITION, Carrier.TEXT)).reachesNothing(),
                "no string of a, c and e lies at or after b and before c");
        assertFalse(code.bounding(OrderedIntervals.at(A_POSITION, new OrderedInterval(
                        Endpoint.inclusive(new Text("b")), Endpoint.inclusive(new Text("c")))),
                Map.of(A_POSITION, Carrier.TEXT)).reachesNothing(),
                "c lies at or after b and at or before c");
    }

    /**
     * The same values, left by a condition on the path rather than by the position's rules.
     *
     * <p>What they rule out with a range is ruled out on the path and not of the value: the
     * reading that ignores the path is left as it was, where the declaration's values reach it.
     */
    @Test
    void theValuesAConditionLeavesAreKnownOnThePathAndNotOfTheValue() {
        Known guarded = range(holdingOdd(Known.top()), 2, 3, Known.Held.OF_THE_VALUE);
        assertTrue(guarded.reachesNothing(), "no value of 1, 3 and 7 lies at or above 2 and below 3");
        assertFalse(guarded.unguarded().constraints().isBottom(),
                "it is the condition that leaves only those, not the value");

        Known declared = range(admittingOdd(Known.top()), 2, 3, Known.Held.OF_THE_VALUE);
        assertTrue(declared.unguarded().constraints().isBottom(),
                "where the rules leave only those, the value does");
    }

    /**
     * Runs of whole numbers a condition leaves, each too long to write out, beside a range on the
     * path: the two leave nothing where the range falls between the runs, and something where it
     * reaches into one, which is read off the ends and not the numbers.
     */
    @Test
    void aRangeBetweenTheRunsAConditionLeavesLeavesNothing() {
        WholeNumberRuns runs = WholeNumberRuns.one(BigInteger.ZERO, BigInteger.valueOf(499_999_998))
                .or(WholeNumberRuns.one(BigInteger.valueOf(1_000_000_006), null));
        Allowance<FactSubject> sets = AsACompilationAllows.forAdmittedValues();
        Known held = Known.top().holdingOnThePath(new Confinement.Planned<>(
                PlannedValues.at(A_POSITION, AdmittedPlan.of(ValueSet.wholeNumbers(runs))),
                OrderedIntervals.top(), Map.of(A_POSITION, Carrier.WHOLE)).resolve(sets), sets);
        assertInstanceOf(ValueSet.WholeRuns.class, ValueSet.wholeNumbers(runs));

        assertTrue(range(held, 600_000_000, 1_000_000_006, Known.Held.ON_THE_PATH).reachesNothing(),
                "no number of the runs lies between them");
        assertFalse(range(held, 400_000_000, 1_000_000_006, Known.Held.ON_THE_PATH)
                .reachesNothing(), "the first run reaches four hundred million");
        assertFalse(range(held, 600_000_000, 1_000_000_007, Known.Held.ON_THE_PATH)
                .reachesNothing(), "the second run begins below the range's end");
    }

    /** {@code known} with the position held to 1, 3 and 7 on the path, as a condition says. */
    private static Known holdingOdd(Known known) {
        Allowance<FactSubject> sets = AsACompilationAllows.forAdmittedValues();
        return known.holdingOnThePath(odd().resolve(sets), sets);
    }

    /** {@code known} with the position held to 1, 3 and 7, as a reading of its rules says. */
    private static Known admittingOdd(Known known) {
        Allowance<FactSubject> sets = AsACompilationAllows.forAdmittedValues();
        return known.admitting(odd().resolve(sets), sets);
    }

    private static Confinement.Planned<FactSubject> odd() {
        return new Confinement.Planned<>(
                PlannedValues.at(A_POSITION, AdmittedPlan.of(new ValueSet.Finite(Set.of(
                        Value.number(1), Value.number(3), Value.number(7))))),
                OrderedIntervals.top(), Map.of(A_POSITION, Carrier.WHOLE));
    }

    /** {@code known} with the position at or above {@code low} and below {@code high}, as far as
     *  {@code held} reaches. */
    private static Known range(Known known, long low, long high, Known.Held held) {
        Map<FactSubject, Granularity> whole = Map.of(A_POSITION, Granularity.DISCRETE);
        return known
                .taking(LinearForm.atomMinusConstant(A_POSITION, ExactRatio.of(low)), Rel.GE,
                        held, whole)
                .taking(LinearForm.atomMinusConstant(A_POSITION, ExactRatio.of(high)), Rel.LT,
                        held, whole);
    }

    /** {@code known} with the position taken on the path to lie at or above {@code low} and below
     *  {@code high}. */
    private static Known between(Known known, long low, long high) {
        return range(known, low, high, Known.Held.ON_THE_PATH);
    }

    private static Known reaching(ConstraintState<FactSubject> constraints) {
        return new Known(constraints, List.of(), AppendOnly.empty(),
                new Known.Unguarded(ConstraintState.top(FactSubject.inOneOrder())), Map.of(),
                List.of());
    }

    private static ConstraintState<FactSubject> numbersAtBottom() {
        return ConstraintState.top(FactSubject.inOneOrder())
                .taking(LinearForm.constant(ExactRatio.ONE), Rel.LE, Map.of());
    }

    private static ConstraintState<FactSubject> factsAtBottom() {
        return ConstraintState.top(FactSubject.inOneOrder()).taking(A_PREDICATE, true).taking(A_PREDICATE, false);
    }

    private static ConstraintState<FactSubject> valuesAtBottom() {
        // Met as one reading and handed over as one. Two readings are combined where the
        // clauses of a declaration are read, and never at the state's boundary.
        Allowance<FactSubject> sets = AsACompilationAllows.forAdmittedValues();
        return ConstraintState.top(FactSubject.inOneOrder()).takingRead(
                new Confinement.Planned<>(says("A").meet(says("B")), OrderedIntervals.top(),
                        Map.<FactSubject, Carrier>of()).resolve(sets), sets);
    }

    /** One rule about the position. */
    private static PlannedValues<FactSubject> says(String text) {
        return PlannedValues.at(A_POSITION, AdmittedPlan.of(ValueSet.just(Value.text(text))));
    }

    private static ConstraintState<FactSubject> orderedAtBottom() {
        return ConstraintState.top(FactSubject.inOneOrder())
                .taking(OrderedIntervals.at(A_POSITION,
                        new OrderedInterval(Endpoint.inclusive(Count.of(6)), null)), Map.of())
                .taking(OrderedIntervals.at(A_POSITION,
                        new OrderedInterval(null, Endpoint.inclusive(Count.of(2)))), Map.of());
    }
}
