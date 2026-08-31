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

            data UpToAHundred = Int
                invariant nonNeg = value >= 0
                invariant hundred = value <= 100

            data Flagged =
                { on: Bool
                , amount: NonNegInt
                }

            data Kind = Counted | Skipped

            data Small = Int
                invariant nn = value >= 0
                invariant cap = value <= 5

            data Held =
                { amount: NonNegInt
                }

            data Holding = Held | Empty

            data Boxed =
                { held: Holding
                }

            data Inner =
                { amount: NonNegInt
                }

            data Middle =
                { inner: Inner
                }

            data Deeper =
                { mid: Middle
                }

            data DeepHolding = Deeper | Missing

            data DeepBoxed =
                { held: DeepHolding
                }

            data Classed =
                { kind: Kind
                , amount: NonNegInt
                }

            let fee   (l: Line): NonNegInt = l.amount
            let seven (l: Line): Int = 7
            let twice (n: Int): Int = n * 2
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

    /**
     * A step that answers one of the values it was handed, written as the operation the library
     * defines by cases.
     *
     * <p>The smaller of two values at or above zero is at or above zero. Written as an {@code if}
     * this discharged; written as {@code Int.min} the same value came out of the walk with no range
     * at all, because what the library's definition says was read only where a clause stood over the
     * call itself and never where a value's range was asked for (#974).
     */
    @Test
    void aStepThatAnswersTheSmallerOfTwoAmountsStaysWhereBothAre() {
        assertFalse(owed(compiled("""
                behavior total : (xs: List<Line>) -> Money
                    constructs Money

                let total (xs) = Money(List.fold((sum, x) -> Int.min(sum, x.amount.value), 0, xs))
                """)), "the smaller of two values at or above zero is at or above zero");
    }

    /** And the same step over elements nothing bounds is reported, so what discharged the one above
     * was what the cases say and not the operation's name. */
    @Test
    void aStepThatAnswersTheSmallerOfTheAccumulatorAndAnythingIsOwed() {
        assertTrue(owed(compiled("""
                behavior total : (xs: List<Int>) -> Money
                    constructs Money

                let total (xs) = Money(List.fold((sum, x) -> Int.min(sum, x), 0, xs))
                """)), "an element below zero is what the smaller of the two is");
    }

    /** The other way round: the larger of the accumulator and anything is no lower than the
     * accumulator, so a seed above the clause carries it whatever the elements are. */
    @Test
    void aStepThatAnswersTheLargerOfTheAccumulatorAndAnythingKeepsTheSeed() {
        assertFalse(owed(compiled("""
                behavior total : (xs: List<Int>) -> AtLeastTen
                    constructs AtLeastTen

                let total (xs) = AtLeastTen(List.fold((acc, x) -> Int.max(acc, x), 10, xs))
                """)), "the larger of ten and anything is at least ten");
    }

    /**
     * A definition written in three cases, two of which are reached under two conditions each.
     *
     * <p>Which is what a reading over the arms alone would not carry: the value {@code clamp}
     * answers is one of three, and only the conditions say that the one it answers where the third
     * case is reached lies between the other two.
     */
    @Test
    void aStepThatHoldsItsAnswerBetweenTwoWrittenEndsLandsBetweenThem() {
        assertFalse(owed(compiled("""
                behavior total : (xs: List<Line>) -> UpToAHundred
                    constructs UpToAHundred

                let total (xs) = UpToAHundred(
                    List.fold((acc, x) -> Int.clamp(0, 100, acc + x.amount.value), 0, xs))
                """)), "a value held between nought and a hundred is within a hundred");
    }

    /** And held between ends the clause does not cover it is reported, so what discharged the one
     * above was the ends the call was given. */
    @Test
    void aStepHeldBetweenEndsWiderThanTheClauseIsOwed() {
        assertTrue(owed(compiled("""
                behavior total : (xs: List<Line>) -> UpToAHundred
                    constructs UpToAHundred

                let total (xs) = UpToAHundred(
                    List.fold((acc, x) -> Int.clamp(0, 200, acc + x.amount.value), 0, xs))
                """)), "a value held below two hundred is not thereby below a hundred");
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
                    constructs Money

                let total (xs) = {
                    let sum = List.fold((acc, x) -> acc + x, 0, xs)
                    guard sum >= 0
                        else Bad
                    Money(sum)
                }
                """)), "the guard states the clause of the value the construction is given");
    }

    /**
     * A step calling a helper that takes a record, which is where the walk read the expansion the
     * inlining left and stopped at the binding it made.
     *
     * <p>The binding holds a {@code Line}, which is no number, and the reading of the arithmetic gave
     * the whole expansion up over that — so the step was one atom and the walk was owed whatever it
     * did. What the binding holds decides what can be said about it and not whether it may be read
     * through: it denotes the element, so the place under it is the element's field, which is the
     * place the walk wrote {@code NonNegInt}'s rule about (#867).
     */
    @Test
    void aStepCallingAHelperThatTakesARecordReadsTheElementTheBindingDenotes() {
        assertFalse(owed(compiled("""
                behavior total : (xs: List<Line>) -> Money
                    constructs Money

                let total (xs) = Money(List.fold((acc, x) -> acc + fee(x).value, 0, xs))
                """)), "the binding the expansion made denotes the element, so `x.amount` is bounded");
    }

    /** The same helper written with an argument the arithmetic reads: what the two differ in is the
     * parameter's type and nothing else, so the one above is not about what a helper answers. */
    @Test
    void aStepCallingAHelperThatTakesANumberIsReadTheSameWay() {
        assertFalse(owed(compiled("""
                behavior total : (xs: List<Line>) -> Money
                    constructs Money

                let total (xs) = Money(List.fold((acc, x) -> acc + twice(x.amount.value), 0, xs))
                """)), "a helper over a number was always read through, and a record is read the same");
    }

    /** And the helper's body is a written number here, which the rule discharges where it is written
     * at the call — so what was reported was the binding standing in front of it and not the step. */
    @Test
    void aStepCallingAHelperThatAnswersAWrittenNumberAnswersThatNumber() {
        assertFalse(owed(compiled("""
                behavior total : (xs: List<Line>) -> AtLeastTen
                    constructs AtLeastTen

                let total (xs) = AtLeastTen(List.fold((acc, x) -> seven(x) + 10, 10, xs))
                """)), "the step answers seventeen whatever the accumulator was");
    }

    /** The neighbour that stays reported: the same helper, subtracted. Reading through the binding is
     * what lets the step be read at all, and reading it is not discharging it. */
    @Test
    void aStepSubtractingWhatSuchAHelperAnswersIsOwed() {
        assertTrue(owed(compiled("""
                behavior total : (xs: List<Line>) -> Money
                    constructs Money

                let total (xs) = Money(List.fold((acc, x) -> acc - fee(x).value, 0, xs))
                """)), "an accumulator at or above zero less an amount at or above zero may go below");
    }

    /**
     * A step that chooses between two answers is read, and it is read by reading the arms. The
     * accumulator is what both arms answer here, so nothing either arm says can be what settles it —
     * which is what says the choice itself was what stopped the reading and not the arithmetic in it
     * (#964).
     */
    @Test
    void aStepWhoseArmsBothAnswerTheAccumulatorAnswersTheAccumulator() {
        assertFalse(owed(compiled("""
                behavior total : (xs: List<Flagged>) -> AtLeastTen
                    constructs AtLeastTen

                let total (xs) = AtLeastTen(List.fold((acc, x) -> if x.on then acc else acc, 10, xs))
                """)), "both arms are the accumulator, so the answer is the seed");
    }

    /** The case an author writes: a total over the rows of one class, with the condition and the
     * addition left as the one sentence the source document states them in. */
    @Test
    void aConditionalTotalIsReadOnBothArms() {
        assertFalse(owed(compiled("""
                behavior total : (xs: List<Flagged>) -> Money
                    constructs Money

                let total (xs) = Money(List.fold((sum, x) -> if x.on then sum + x.amount.value
                    else sum, 0, xs))
                """)), "one arm adds an amount at or above zero and the other adds nothing");
    }

    /** A {@code match} is read the same way, since what is read is that the value is one of several
     * and not which form was written to choose between them. */
    @Test
    void aMatchInAStepIsReadTheSameWay() {
        assertFalse(owed(compiled("""
                behavior total : (xs: List<Classed>) -> Money
                    constructs Money

                let total (xs) = Money(List.fold((sum, x) -> match x.kind with
                    | Counted -> sum + x.amount.value
                    | Skipped -> sum, 0, xs))
                """)), "every arm takes an accumulator at or above zero there and leaves it there");
    }

    /** The neighbour that stays reported: one arm of the same shape lowers the accumulator. Every
     * arm is held to the range, so one that leaves it is the walk unproven however the others go. */
    @Test
    void aStepOneArmOfWhichLowersTheAccumulatorIsOwed() {
        assertTrue(owed(compiled("""
                behavior total : (xs: List<Flagged>) -> Money
                    constructs Money

                let total (xs) = Money(List.fold((sum, x) -> if x.on then sum + x.amount.value
                    else sum - 1, 0, xs))
                """)), "the other arm takes an accumulator at zero to below it");
    }

    /**
     * A step whose arm stays inside the range only because of its condition is read, because the arm
     * is read under what chose it.
     *
     * <p>The clause has an end above it and the arm reaches that end by the test beside it. Read on
     * the arms alone that arm answers anything at all, which is what this was owed for until the
     * relations a condition states stood beside the arms ({@link
     * souther.compiler.check.Derivation.Chosen.Arm#settles}). A clamp written this way is the shape
     * an author reaches for first, and the rewrite that made it read — lifting the condition into a
     * {@code List.filter} — was a change to the model made to satisfy the checker.
     */
    @Test
    void aStepWhoseArmIsInRangeByItsConditionIsRead() {
        assertFalse(owed(compiled("""
                behavior total : (xs: List<Flagged>) -> UpToAHundred
                    constructs UpToAHundred

                let total (xs) = UpToAHundred(List.fold((sum, x) ->
                    if sum + x.amount.value < 100 then sum + x.amount.value else 100, 0, xs))
                """)), "the condition holds the first arm below a hundred and the arm is read under it");
    }

    /**
     * And it is still read under four conditions that say nothing about a number.
     *
     * <p>What a split costs is what it copies a reading into, and a reader is copied only where its
     * arms are read against different domains. A condition on a flag gives this reader the domain it
     * already had, so it is one reading and not two, and however many of them stand around a clamp
     * the clamp is opened on its own terms. Counted by the arms instead, four of them spend the
     * whole of what splits may compound to, and a value the reading was about to hold below a
     * hundred goes back to being owed because something numerically silent was written around it.
     */
    @Test
    void aClampInsideConditionsThatSayNothingAboutANumberIsStillRead() {
        assertFalse(owed(compiled("""
                behavior total : (xs: List<Flagged>) -> UpToAHundred
                    constructs UpToAHundred

                let total (xs) = UpToAHundred(List.fold((sum, x) ->
                    if x.on then
                        (if x.on then
                            (if x.on then
                                (if x.on then
                                    (if sum + x.amount.value < 100 then sum + x.amount.value
                                        else 100)
                                    else 100)
                                else 100)
                            else 100)
                        else 100, 0, xs))
                """)), "a flag says nothing about a number, so none of those four is a split here");
    }

    /** And the same step with the condition saying nothing about what the arm answers is owed, so
     * what discharged the one above was the condition and not the shape of a clamp. */
    @Test
    void aStepWhoseConditionSaysNothingAboutItsArmIsOwed() {
        assertTrue(owed(compiled("""
                behavior total : (xs: List<Flagged>) -> UpToAHundred
                    constructs UpToAHundred

                let total (xs) = UpToAHundred(List.fold((sum, x) ->
                    if x.on then sum + x.amount.value else 100, 0, xs))
                """)), "nothing here holds the first arm below a hundred");
    }

    /**
     * An attempted construction answers one of several as plainly as an {@code if} does — what it
     * built where the invariant held, and what it departs with where it did not — and it is read the
     * same way.
     *
     * <p>Here because it is where the reading was missing. Three spellings of "which nodes answer
     * one of several" all said {@code if} and {@code match}, so an attempt was named and nothing was
     * recorded about the values it is one of, which is what this test's subject was under a third
     * spelling.
     */
    @Test
    void aStepWhoseArmsAreAnAttemptsBranchesIsReadTheSameWay() {
        assertFalse(owed(compiled("""
                behavior total : (xs: List<Flagged>) -> AtLeastTen
                    constructs AtLeastTen, NonNegInt

                let total (xs) = AtLeastTen(List.fold((acc, x) ->
                    if NonNegInt(x.amount.value) as n then acc else acc, 10, xs))
                """)), "both branches of the attempt are the accumulator, so the answer is the seed");
    }

    /**
     * An attempt departs once per clause it names, and every departure is one of the values it
     * answers.
     *
     * <p>Both directions over the same two-armed departure, differing in which arm is below the
     * seed. A reading that took the built value and one departure would discharge whichever of these
     * puts the low value in the arm it dropped — so the pair says every arm was read and not that
     * some were.
     */
    @Test
    void everyDepartureAnAttemptNamesIsOneOfTheValuesItAnswers() {
        String walk = """
                behavior total : (xs: List<Flagged>) -> AtLeastTen
                    constructs AtLeastTen, Small

                let total (xs) = AtLeastTen(List.fold((acc, x) ->
                    if Small(x.amount.value) as s then acc
                    else | nn -> %s | cap -> %s, 10, xs))
                """;
        assertFalse(owed(compiled(walk.formatted("acc", "acc"))),
                "every arm is the accumulator, so the answer is the seed");
        assertTrue(owed(compiled(walk.formatted("0", "acc"))),
                "the first departure answers nought, which is below ten");
        assertTrue(owed(compiled(walk.formatted("acc", "0"))),
                "and so does the second, which a reading that stopped at the first would miss");
    }

    /** The neighbour that stays reported: a departure below the seed. So what discharged the one
     * above was the branches and not the shape of the attempt. */
    @Test
    void anAttemptWhoseDepartureIsBelowTheSeedIsOwed() {
        assertTrue(owed(compiled("""
                behavior total : (xs: List<Flagged>) -> AtLeastTen
                    constructs AtLeastTen, NonNegInt

                let total (xs) = AtLeastTen(List.fold((acc, x) ->
                    if NonNegInt(x.amount.value) as n then acc else 0, 10, xs))
                """)), "where the invariant does not hold the walk answers nought, which is below ten");
    }

    /**
     * What choosing an arm settles has two sources.
     *
     * <p>What a condition states is the condition's ({@link souther.compiler.check.Conditions});
     * what being a value of a type guarantees is the declaration's, and is the same answer a seeding
     * reads of a parameter ({@link souther.compiler.check.TypeGuarantees}). A {@code match} arm
     * binds the scrutinee refined to the case it names and an attempt binds what it built, so both
     * were built through their type's checked constructor and both carry what that type states.
     * Stated under the arm and not beside it: the value only exists because that arm was chosen.
     *
     * <p>One fact per test below. Written as one method, the first that failed hid the rest — which
     * it did, and a reading of what the other two were doing was made from assertions that never
     * ran.
     */
    @Test
    void anArmReadingTheElementIsTheNeighbourThatWasAlwaysRead() {
        assertFalse(owed(compiled("""
                behavior total : (xs: List<Flagged>) -> Money
                    constructs Money, NonNegInt

                let total (xs) = Money(List.fold((sum, x) ->
                    if NonNegInt(x.amount.value) as n then sum + x.amount.value else sum, 0, xs))
                """)), "this arm reads the element, which the walk entered, so the step is read");
    }

    @Test
    void anArmReadingWhatAnAttemptBuiltIsReadByWhatItsTypeGuarantees() {
        assertFalse(owed(compiled("""
                behavior total : (xs: List<Flagged>) -> Money
                    constructs Money, NonNegInt

                let total (xs) = Money(List.fold((sum, x) ->
                    if NonNegInt(x.amount.value) as n then sum + n.value else sum, 0, xs))
                """)), "this one reads what the attempt built, which its own type speaks for");
    }

    @Test
    void anArmReadingWhatAMatchBoundIsReadByWhatItsTypeGuarantees() {
        assertFalse(owed(compiled("""
                behavior total : (xs: List<Boxed>) -> Money
                    constructs Money

                let total (xs) = Money(List.fold((sum, x) -> match x.held with
                    | Held as h -> sum + h.amount.value
                    | Empty -> sum, 0, xs))
                """)), "and this one reads what a `match` arm bound, which is the same thing again");
    }

    /**
     * What an arm bound guarantees is read wherever the rule is written under it.
     *
     * <p>The neighbour above reads a rule one position under what the arm bound, and a reading that
     * stopped where a seeding stops would still have found it. This one is three under it, which is
     * past what a walk over a body can afford — and the model says the same thing about both: a rule
     * four records down refuses a value exactly as one on the top does.
     *
     * <p>Written down because the reading did borrow that number, and the borrowing was invisible
     * from either side. The walk's own tests pass with a bound in place, since they say what a bound
     * does; the recipe's tests pass, since a rule a position or two down is inside any of them. This
     * is the case that fails the moment
     * {@link souther.compiler.check.GuaranteeWalk.Scope#everyName} here becomes a number.
     */
    @Test
    void whatAnArmBoundGuaranteesIsReadHoweverDeepTheRuleIsWritten() {
        assertFalse(owed(compiled("""
                behavior total : (xs: List<DeepBoxed>) -> Money
                    constructs Money

                let total (xs) = Money(List.fold((sum, x) -> match x.held with
                    | Deeper as d -> sum + d.mid.inner.amount.value
                    | Missing -> sum, 0, xs))
                """)), "the rule is three positions under what the arm bound, and it is read");
    }

}
