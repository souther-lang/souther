package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a {@code List.fold} answers, read by proposing a range from the seed and checking one step
 * (spec §invariant-discharge-reduction).
 *
 * <p>The answer of a walk used to be an atom nothing was recorded against, so a construction over one
 * was owed whatever the walk was — a step that answered its accumulator unchanged answers the seed
 * written on the line, and that was owed too. What is checked here is that the rule fires for the
 * walks it states and for no others: a step that lowers its accumulator, a seed below the clause, an
 * element nothing bounds, and a step outside the arithmetic the procedure reads all stay reported.
 *
 * <p>Both directions, because a rule that only ever discharges is a rule that stopped reading. Every
 * silent case here has a neighbour differing in one thing that is not silent.
 */
class AWalkFromASeedIsBoundedByCheckingOneStepTest {

    private static final String TYPES = """
            module demo

            data Money = Int
                invariant nonNeg = value >= 0

            data NonNegInt = Int
                invariant nn = value >= 0

            data Line =
                { amount: NonNegInt
                }

            data AtLeastTen = Int
                invariant tenUp = value >= 10
            """;

    private static Compiler.Compiled compiled(String body) {
        return Compiler.compileWithWarnings(TYPES + "\n" + body);
    }

    private static boolean owed(Compiler.Compiled c) {
        return c.warnings().stream()
                .anyMatch(d -> d.severity() == Severity.WARNING && "E2011".equals(d.code()));
    }

    /** The case an author writes: a total over a list of amounts, seeded at zero. */
    @Test
    void aSumOfNonNegativeAmountsFromAZeroSeedDischarges() {
        assertFalse(owed(compiled("""
                behavior total : (xs: List<Line>) -> Money
                    constructs Money

                let total (xs) = Money(List.fold((sum, x) -> sum + x.amount.value, 0, xs))
                """)), "an accumulator at or above zero plus an amount at or above zero stays there");
    }

    /**
     * A step that answers its accumulator unchanged answers the seed, and the seed is written on the
     * line. No induction over the container is needed to know where that value is, which is what made
     * this the case that said the answer was being read as an atom nothing was recorded against.
     */
    @Test
    void aStepThatAnswersItsAccumulatorAnswersTheSeed() {
        assertFalse(owed(compiled("""
                behavior total : (xs: List<Int>) -> AtLeastTen
                    constructs AtLeastTen

                let total (xs) = AtLeastTen(List.fold((acc, x) -> acc, 10, xs))
                """)), "the answer is the seed, which is written above the clause's own end");
    }

    /** A step that does not read its accumulator answers the seed or answers what it answers, and
     * both are written out. */
    @Test
    void aStepThatIgnoresItsAccumulatorIsTheSeedJoinedWithWhatItAnswers() {
        assertFalse(owed(compiled("""
                behavior total : (xs: List<Line>) -> Money
                    constructs Money

                let total (xs) = Money(List.fold((sum, x) -> 7, 0, xs))
                """)), "zero or seven, and neither is below zero");
    }

    /** The accumulator arrives on the second parameter here, which is read off the declaration and
     * not written down anywhere. */
    @Test
    void aFoldRightIsReadWithItsAccumulatorOnTheSecondParameter() {
        assertFalse(owed(compiled("""
                behavior total : (xs: List<Line>) -> Money
                    constructs Money

                let total (xs) = Money(List.foldRight((x, acc) -> acc + x.amount.value, 0, xs))
                """)), "which parameter carries the accumulator is read off the signature");
    }

    /** And the same walk with a step that lowers the accumulator is reported, so what discharged the
     * one above was the step and not the shape of the call. */
    @Test
    void aFoldRightWhoseStepLowersItsAccumulatorIsOwed() {
        assertTrue(owed(compiled("""
                behavior total : (xs: List<Line>) -> Money
                    constructs Money

                let total (xs) = Money(List.foldRight((x, acc) -> acc - x.amount.value, 0, xs))
                """)), "an accumulator an amount is taken off may go below zero");
    }

    @Test
    void aStepThatLowersItsAccumulatorIsOwed() {
        assertTrue(owed(compiled("""
                behavior total : (xs: List<Line>) -> Money
                    constructs Money

                let total (xs) = Money(List.fold((sum, x) -> sum - 1, 0, xs))
                """)), "a walk that subtracts on every element leaves no range the seed sits in");
    }

    /** The seed decides the range, so a clause the seed does not meet is not established by a step
     * that only ever adds. */
    @Test
    void aSeedBelowTheClauseIsOwedHoweverTheStepRuns() {
        assertTrue(owed(compiled("""
                behavior total : (xs: List<Line>) -> AtLeastTen
                    constructs AtLeastTen

                let total (xs) = AtLeastTen(List.fold((acc, x) -> acc + x.amount.value, 0, xs))
                """)), "a walk over an empty list answers the seed, which is below ten");
    }

    /** The same walk seeded at ten discharges, so what decided the one above was the seed. */
    @Test
    void theSameWalkSeededAtTheClausesEndDischarges() {
        assertFalse(owed(compiled("""
                behavior total : (xs: List<Line>) -> AtLeastTen
                    constructs AtLeastTen

                let total (xs) = AtLeastTen(List.fold((acc, x) -> acc + x.amount.value, 10, xs))
                """)), "ten, and every step only adds something at or above zero");
    }

    /** What holds of the element is what its type says. An {@code Int} says nothing, so a sum of
     * them is not bounded by the seed. */
    @Test
    void anElementWhoseTypeBoundsNothingLeavesTheWalkOwed() {
        assertTrue(owed(compiled("""
                behavior total : (xs: List<Int>) -> Money
                    constructs Money

                let total (xs) = Money(List.fold((sum, x) -> sum + x, 0, xs))
                """)), "an Int element may be negative, so the accumulator may leave the range");
    }

    /** A container written out holds the elements written there and no others, so what every one of
     * them is above is what every element is above. */
    @Test
    void aContainerWrittenOutBoundsItsOwnElements() {
        assertFalse(owed(compiled("""
                behavior total : () -> Money
                    constructs Money

                let total = Money(List.fold((sum, x) -> sum + x, 0, [1, 2]))
                """)), "the only elements there are are one and two");
    }

    /** And the same list with a negative in it is reported, so what discharged the one above was the
     * elements and not the container being written out. */
    @Test
    void aContainerWrittenOutHoldingANegativeIsOwed() {
        assertTrue(owed(compiled("""
                behavior total : () -> Money
                    constructs Money

                let total = Money(List.fold((sum, x) -> sum + x, 0, [1, 0 - 2]))
                """)), "an element written there is below zero, so the answer may be");
    }

    /** The fragment the step is read in, stated by a step outside it: a choice is not arithmetic
     * this derives in, so the walk is left where it was. */
    @Test
    void aStepThatChoosesBetweenTwoAnswersIsNotReadAtAll() {
        assertTrue(owed(compiled("""
                behavior total : (xs: List<Line>) -> Money
                    constructs Money

                let total (xs) =
                    Money(List.fold((sum, x) -> if x.amount.value > 0 then sum else 0 - 1, 0, xs))
                """)), "a step that is a choice is outside the arithmetic the walk is read in");
    }

    /**
     * What a record's own invariant says about its fields bounds a walk over one, and it is the
     * canonical reading that says so.
     *
     * <p>The rule that established the sum above is written on a newtype the field wears. This one is
     * written on the record and bounds a field of a bare {@code Int}, so nothing about the type at
     * the place the step reads says it — only the reading that seeds a value of {@code Line}. The
     * same fact is what a construction inside a {@code List.map} closure is already read against, and
     * a walk that could not see it would be a second answer to what a type guarantees.
     */
    @Test
    void aRecordsOwnInvariantBoundsTheFieldAWalkReads() {
        assertFalse(owed(Compiler.compileWithWarnings("""
                module demo

                data Money = Int
                    invariant nonNeg = value >= 0

                data Row =
                    { amount: Int
                    }
                    invariant amountNonNeg = amount >= 0

                behavior total : (xs: List<Row>) -> Money
                    constructs Money

                let total (xs) = Money(List.fold((sum, x) -> sum + x.amount, 0, xs))
                """)), "the record's own invariant bounds the field the step reads");
    }

    /**
     * A step whose answer is arithmetic the fragment cannot carry is read under the range being
     * assumed of the accumulator, not before it.
     *
     * <p>A product is one value the domain holds nothing about until its factors are read, and one of
     * its factors here is the accumulator. Read against what was known before the candidate, both
     * factors are unknown and no product is ever bounded, so a walk that multiplies could never be
     * proved however plainly its factors are bounded.
     */
    @Test
    void aProductInsideTheStepIsReadUnderTheInductionHypothesis() {
        assertFalse(owed(Compiler.compileWithWarnings("""
                module demo

                data Positive = Int
                    invariant atLeastOne = value >= 1

                data AtLeastOne = Int
                    invariant atLeastOne = value >= 1

                behavior product : (xs: List<Positive>) -> AtLeastOne
                    constructs AtLeastOne

                let product (xs) = AtLeastOne(List.fold((acc, x) -> acc * x.value, 1, xs))
                """)), "one times something at or above one is at or above one");
    }

    /**
     * The same walk seeded at zero is refused outright, and that is the rule working rather than a
     * stronger claim than it makes.
     *
     * <p>Zero times anything is zero, so {@code [0, 0]} is a range the step never leaves and the walk
     * answers zero however long the container is. A clause wanting one is one that value fails, which
     * is an error and not a warning — the rule refuses as readily as it discharges, and a walk is not
     * a place where that stops being so.
     */
    @Test
    void aProductInsideTheStepSeededBelowTheClauseIsRefused() {
        CompileException refused = assertThrows(CompileException.class, () ->
                Compiler.compileWithWarnings("""
                        module demo

                        data Positive = Int
                            invariant atLeastOne = value >= 1

                        data AtLeastOne = Int
                            invariant atLeastOne = value >= 1

                        behavior product : (xs: List<Positive>) -> AtLeastOne
                            constructs AtLeastOne

                        let product (xs) = AtLeastOne(List.fold((acc, x) -> acc * x.value, 0, xs))
                        """));
        assertTrue(refused.getMessage().contains("E2010"), refused.getMessage());
    }

    /** A walk over a container with no order, whose element carries its type's rule. */
    @Test
    void aSetFoldIsReadTheSameWay() {
        assertFalse(owed(compiled("""
                behavior total : (s: Set<NonNegInt>) -> Money
                    constructs Money

                let total (s) = Money(Set.fold((acc, x) -> acc + x.value, 0, s))
                """)), "a walk over a set is the same rule; order is not part of it");
    }

    /** A walk whose step takes three parameters: the accumulator, a key, and a value. Which of them
     * is the accumulator is read off the declaration, and the other two are both read for what their
     * types guarantee. */
    @Test
    void aMapFoldIsReadOverTheValueItHandsItsStep() {
        assertFalse(owed(compiled("""
                behavior total : (m: Map<String, NonNegInt>) -> Money
                    constructs Money

                let total (m) = Money(Map.fold((acc, k, v) -> acc + v.value, 0, m))
                """)), "the value the map holds carries its type's rule");
    }

    @Test
    void aMapFoldOverAnUnboundedValueIsOwed() {
        assertTrue(owed(compiled("""
                behavior total : (m: Map<String, Int>) -> Money
                    constructs Money

                let total (m) = Money(Map.fold((acc, k, v) -> acc + v, 0, m))
                """)), "an Int the map holds may be negative");
    }

    /**
     * One walk read twice is one atom, and what is filed against that atom is one thing.
     *
     * <p>A walk's atom normalises the bindings its step was written with, so the same walk reached
     * through two readings is one atom however the bindings differ. What is filed against it has to
     * normalise them too: named by the binding, the accumulator was two values under one name and the
     * check refused its own naming. Two readings is what a walk inside a closure gets, and the
     * construction over the walk's answer is judged under both.
     */
    @Test
    void oneWalkReadTwiceCarriesOneAccumulator() {
        assertFalse(owed(compiled("""
                behavior each : (rows: List<List<Line>>) -> List<Money>
                    constructs Money

                let each (rows) =
                    List.map((xs) -> {
                        let sum = List.fold((acc, x) -> acc + x.amount.value, 0, xs)
                        Money(sum)
                    }, rows)
                """)), "one walk, one accumulator, and no disagreement about which value it is");
    }

    /** A walk whose answer a guard settles is discharged by the guard, as it was before any of this:
     * naming the walk did not take the other way of establishing it away. */
    @Test
    void aGuardOnTheAnswerStillDischargesIt() {
        assertFalse(owed(compiled("""
                data Bad

                behavior total : (xs: List<Int>) -> Money | Bad
                    constructs Money, Bad

                let total (xs) = {
                    let sum = List.fold((acc, x) -> acc + x, 0, xs)
                    guard sum >= 0
                        else Bad
                    Money(sum)
                }
                """)), "the guard states the clause of the value the construction is given");
    }
}
