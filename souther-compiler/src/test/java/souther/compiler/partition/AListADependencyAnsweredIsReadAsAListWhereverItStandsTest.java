package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadings;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.RuleRequirement;
import souther.compiler.query.RuleSettlement;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an operation means of a list does not turn on where the list stands.
 *
 * <p>A list a dependency answered is read as the list it is: its count is a number the library
 * takes of it, its elements are what a closure is handed, and what a way asks of it is composed
 * into the value a row stands the dependency in with. Where a statement is also about the input,
 * which the value composed here cannot meet without the row, it is declined and says so.
 */
class AListADependencyAnsweredIsReadAsAListWhereverItStandsTest {

    private static final String MODEL = """
            module p

            data Cat = A | B
            data Sched = List<Int>
            data Yes
            data No
            data Answer = Yes | No

            behavior sched1 : (c: Cat) -> Sched

            behavior f : (c: Cat, on: Int) -> Answer
                depends on sched1
            let f (c, on, sched1) = if BODY then Yes else No

            behavior holds : (s: Sched) -> Bool
            let holds (s) = true
            """;

    /** Every element the dependency answers is at least ten. */
    private static final String STAMPS = """
            module p

            data Cat = A | B
            data Stamp = Int invariant value >= 10
            data Sched = List<Stamp>
            data Yes
            data No
            data Answer = Yes | No

            behavior sched1 : (c: Cat) -> Sched

            behavior f : (c: Cat, on: Int) -> Answer
                depends on sched1

            let f (c, on, sched1) = if List.any(x -> BODY, sched1(c).value) then Yes else No
            """;

    private static final String MODEL_OF_TWO = """
            module p

            data Cat = A | B
            data Sched = List<Int>
            data Yes
            data No
            data Answer = Yes | No

            behavior sched1 : (c: Cat) -> Sched
            behavior sched2 : (c: Cat) -> Sched

            behavior f : (c: Cat, on: Int) -> Answer
                depends on sched1, sched2
            let f (c, on, sched1, sched2) = if BODY then Yes else No
            """;

    private static final Pattern NUMBER = Pattern.compile("-?\\d+");

    /** The count of what a dependency answered is a column, whichever way it comes out. */
    @Test
    void theCountOfAnAnswerIsAStatedComparison() {
        List<AnswersDemanded> ways = waysOf("List.length(sched1(c).value) >= 1");

        assertEquals(2, ways.size());
        for (AnswersDemanded each : ways) {
            assertTrue(each.declined().isEmpty(), () -> "nothing was left unstated: " + each);
            AnswerDemand.AComparison comparison = assertInstanceOf(
                    AnswerDemand.AComparison.class, each.stated().getFirst());
            assertInstanceOf(DecisionAtom.TakenOfAnAnswer.class,
                    comparison.form().coefs().keySet().iterator().next(),
                    "the count is the one the library takes of a list");
        }
    }

    /** What a closure states of each element of the answer is a statement of the answer. */
    @Test
    void aClosureOverTheElementsOfAnAnswerIsAStatedStatement() {
        for (String body : List.of("List.any(x -> x <= 5, sched1(c).value)",
                "List.length(List.filter(x -> x > 5, sched1(c).value)) >= 2")) {
            for (AnswersDemanded each : waysOf(body)) {
                assertTrue(each.declined().isEmpty(), () -> body + " left unstated: " + each);
                assertInstanceOf(AnswerDemand.AStatement.class, each.stated().getFirst(),
                        () -> body + " is a statement about the answer: " + each);
            }
        }
    }

    /** And a value is composed that meets it, one for each way, and no two ways share one. */
    @Test
    void aValueIsComposedForEachWayOfSomeElementMeetingAComparison() {
        List<List<Long>> values = composedForEachWay("List.any(x -> x <= 5, sched1(c).value)");

        assertEquals(List.of(true, false), values.stream()
                .map(elements -> elements.stream().anyMatch(each -> each <= 5))
                .sorted((a, b) -> Boolean.compare(b, a)).toList(),
                () -> "one value has an element at most five and the other has none: " + values);
        assertTrue(values.stream().noneMatch(elements ->
                        elements.isEmpty() && values.size() == 1),
                "an empty list is not what meets some element");
        assertTrue(values.stream().filter(elements -> elements.stream().anyMatch(e -> e <= 5))
                .noneMatch(List::isEmpty), () -> "the value that has one is not empty: " + values);
    }

    @Test
    void aValueIsComposedForEachWayOfACountOfTheElementsMeetingAComparison() {
        List<List<Long>> values = composedForEachWay(
                "List.length(List.filter(x -> x > 5, sched1(c).value)) >= 2");

        Predicate<List<Long>> twoAboveFive =
                elements -> elements.stream().filter(each -> each > 5).count() >= 2;
        assertEquals(1, values.stream().filter(twoAboveFive).count(),
                () -> "one way is two elements above five: " + values);
        assertEquals(1, values.stream().filter(twoAboveFive.negate()).count(),
                () -> "and the other is fewer than two of them: " + values);
    }

    /** A count of the answer itself is composed to, as a count of the input's own list is. */
    @Test
    void aValueIsComposedForEachWayOfTheLengthOfTheAnswer() {
        List<List<Long>> values = composedForEachWay("List.length(sched1(c).value) >= 2");

        assertEquals(1, values.stream().filter(elements -> elements.size() >= 2).count(),
                () -> "one way holds two or more: " + values);
        assertEquals(1, values.stream().filter(elements -> elements.size() < 2).count(),
                () -> "and the other holds fewer: " + values);
    }

    /**
     * What an element is is what the closure is handed, and not what the answer holds: a closure
     * over a mapped list is asked of the mapped values, so the value that meets it holds the
     * element the map was applied to.
     */
    @Test
    void aMappedElementIsNotTakenForTheElementItCameFrom() {
        List<List<Long>> values = composedForEachWay(
                "List.any(x -> x <= 5, List.map(y -> y + 10, sched1(c).value))");

        Predicate<List<Long>> someMappedAtMostFive =
                elements -> elements.stream().anyMatch(each -> each + 10 <= 5);
        assertEquals(1, values.stream().filter(someMappedAtMostFive).count(),
                () -> "one way is an element whose mapped value is at most five: " + values);
        assertEquals(1, values.stream().filter(someMappedAtMostFive.negate()).count(),
                () -> "and in the other none is: " + values);
    }

    /** Two askings that read one place of what a dependency answered read one value against itself. */
    @Test
    void twoCallsReadingOnePlaceAreNotTwoAnswers() {
        for (AnswersDemanded each : waysOf(
                "List.length(sched1(c).value) >= List.length(sched1(c).value) + 1")) {
            assertEquals(List.of(new DemandGap.WhyNotStated.AFormOverMoreThanOneAnswer()),
                    each.declined().stream().map(DemandGap.Unstated::why).toList(),
                    () -> "a form over what two calls answered is one value held against itself: "
                            + each);
            assertTrue(each.stated().isEmpty(), () -> "and nothing is composed to it: " + each);
        }
    }

    /** A statement that is also about a number of the input is still a statement of the answer. */
    @Test
    void aStatementAlsoAboutANumberOfTheInputIsStated() {
        for (AnswersDemanded each : waysOf("List.any(x -> x <= on, sched1(c).value)")) {
            assertTrue(each.declined().isEmpty(), () -> "nothing was left unstated: " + each);
            assertInstanceOf(AnswerDemand.AStatement.class, each.stated().getFirst());
        }
    }

    /**
     * A statement that is also about the input is met by the pair: the number of the input is put at
     * a value, the answer is composed for it, and the row carries both. A row the run takes the rule
     * with is what says the pair meets it, and the two rules of the way are taken by two rows.
     */
    @Test
    void aRowIsFoundForEachWayOfAStatementAboutTheAnswerAndTheInput() {
        for (String body : List.of("List.any(x -> x <= on, sched1(c).value)",
                "List.length(List.filter(x -> x <= on, sched1(c).value)) >= 1")) {
            List<RowToRun> rows = rowsFoundFor(body);

            assertEquals(2, rows.size(), () -> body + " owes a row for each of its two rules");
            List<Boolean> someElementAtMostOn = new ArrayList<>();
            for (RowToRun row : rows) {
                long on = Long.parseLong(row.inputs().get(1).text().trim());
                List<Long> held = elementsOf(
                        ((StoodInAnswer.OnTheRow) row.answers().getFirst()).value().text());
                someElementAtMostOn.add(held.stream().anyMatch(each -> each <= on));
            }
            assertEquals(List.of(false, true), someElementAtMostOn.stream().sorted().toList(),
                    () -> body + ": one row has an element the number reaches and the other has"
                            + " none, whichever number the row holds: " + rows);
        }
    }

    /**
     * One value of the dependency answers every call a row makes, so what two calls ask is asked of
     * that one value together. Two askings that each have a value, and no value in common, may still
     * have a value that meets both: the value composed for "some element is at most five" is five
     * and for "at most eight" is eight, and five meets both.
     */
    @Test
    void twoCallsAskingDifferentThingsOfOnePlaceAreMetByOneValue() {
        List<RowToRun> rows = rowsFoundFor("List.any(x -> x <= 5, sched1(c).value)"
                + " && List.any(x -> x <= 8, sched1(c).value)");

        assertTrue(rows.stream().anyMatch(row -> {
                    List<Long> held = elementsOf(
                            ((StoodInAnswer.OnTheRow) row.answers().getFirst()).value().text());
                    return held.stream().anyMatch(each -> each <= 5)
                            && held.stream().anyMatch(each -> each <= 8);
                }),
                () -> "a row stands the one dependency in with a value that meets both: " + rows);
    }

    /**
     * The same for a comparison, which asked of two calls composed a boundary value apiece: one
     * above four and one below seven have the value five in common, and the two boundaries that
     * were composed have none.
     */
    @Test
    void twoCallsComparingOnePlaceAreMetByOneValue() {
        List<RowToRun> rows = rowsFoundFor("List.length(sched1(c).value) >= 4"
                + " && List.length(sched1(c).value) <= 5");

        assertTrue(rows.stream().anyMatch(row -> {
                    long size = elementsOf(
                            ((StoodInAnswer.OnTheRow) row.answers().getFirst()).value().text())
                            .size();
                    return size >= 4 && size <= 5;
                }),
                () -> "a row carries a value of the length both ask for: " + rows);
    }

    /**
     * The number is put where the way leaves it. A way that asks the number to be above a hundred is
     * a way the row reaches only with one, so the answer is composed for such a number and not for
     * the first one that came to mind.
     */
    @Test
    void theNumberOfTheInputIsPutWhereTheWayLeavesIt() {
        List<RowToRun> rows = rowsFoundFor("on > 100 && List.any(x -> x <= on, sched1(c).value)");

        assertFalse(rows.isEmpty(), "a row reaches the way");
        for (RowToRun row : rows) {
            long on = Long.parseLong(row.inputs().get(1).text().trim());
            if (on > 100) {
                List<Long> held = elementsOf(
                        ((StoodInAnswer.OnTheRow) row.answers().getFirst()).value().text());
                assertTrue(held.stream().anyMatch(each -> each <= on),
                        () -> "an element the number reaches: " + row);
                return;
            }
        }
        throw new AssertionError("no row carries a number above a hundred: " + rows);
    }

    /**
     * The number is put where the answer can reach it, and not at the first value the way allows.
     * Every element the dependency answers is at least ten, so "some element is at most the number"
     * has no value at all for a number below ten — the number has to be put at ten or above before
     * the answer can be composed for it.
     */
    @Test
    void theNumberOfTheInputIsPutWhereTheTypeOfTheAnswerCanReachIt() {
        List<RowToRun> rows = rowsFoundIn(STAMPS.replace("BODY", "x.value <= on"));

        assertTrue(rows.stream().anyMatch(row -> someElementMeets(row, (element, on) ->
                        on >= 10 && element <= on)),
                () -> "a row reaches the way with a number the elements can be at most: " + rows);
    }

    /**
     * And where the value the bounds first suggest is one the statement does not hold at, the next
     * is tried. "Strictly below" is not met at ten by elements of at least ten, so the number is put
     * at eleven, which the pair has to move to once the answer has failed to compose for ten.
     */
    @Test
    void aNumberTheAnswerCannotBeComposedForIsFollowedByTheNext() {
        List<RowToRun> rows = rowsFoundIn(STAMPS.replace("BODY", "x.value < on"));

        assertTrue(rows.stream().anyMatch(row -> someElementMeets(row, (element, on) ->
                        on > 10 && element < on)),
                () -> "a row reaches the way with a number above every element's least: " + rows);
    }

    private static boolean someElementMeets(RowToRun row,
                                            java.util.function.BiPredicate<Long, Long> holding) {
        long on = Long.parseLong(row.inputs().get(1).text().trim());
        return elementsOf(((StoodInAnswer.OnTheRow) row.answers().getFirst()).value().text())
                .stream().anyMatch(each -> holding.test(each, on));
    }

    /**
     * Past the figure the pairs are not looked at, and the search says that was why. Four numbers
     * of the input are each offered at several values, and every element is at least ten, so no
     * pair of the first few composes — and the search that stopped is told apart from one that tried
     * every pair and found none.
     */
    @Test
    void pairsPastTheFigureAreSaidToHaveBeenLeftUntried() {
        String source = """
                module p

                data Cat = A | B
                data Stamp = Int invariant value >= 10
                data Sched = List<Stamp>
                data Yes
                data No
                data Answer = Yes | No

                behavior sched1 : (c: Cat) -> Sched

                behavior f : (c: Cat, a: Int, b: Int, d: Int, e: Int) -> Answer
                    depends on sched1

                let f (c, a, b, d, e, sched1) =
                    if List.any(x -> x.value <= a + b + d + e, sched1(c).value) then Yes else No
                """;
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();

        Set<CompositionBudget> said = new HashSet<>();
        for (RuleSettlement each : compilation.db()
                .ask(new Adequacy.DecisionSearch(module, "f")).value().values().stream()
                .map(each -> each.answer().settlement()).toList()) {
            for (DemandGap gap : each.account().onAnAnswer()) {
                if (gap instanceof DemandGap.Uncomposed(var _,
                        DemandGap.WhyNotComposed.NoPairComposedBeforeAFigureEnded(var figures))) {
                    said.addAll(figures.written());
                }
            }
        }

        assertEquals(Set.of(CompositionBudget.PAIRS_OF_INPUT_NUMBERS_AND_AN_ANSWER_TRIED), said,
                "a figure ended the search, which the demand not composed against says — and is not"
                        + " that every pair was tried and none met it");
    }

    /**
     * A statement of more ways than are looked along is composed along the ones that are: any one
     * is enough for it to hold, so the ways past the figure are not a reason to give up the ways
     * before it. Past the figure for splitting a way at five choices, and past what a reading of one
     * condition makes at ten.
     */
    @Test
    void aStatementOfManyChoicesIsComposedAlongTheWaysLookedAt() {
        for (int choices : new int[] {5, 10}) {
            List<String> parts = new ArrayList<>();
            for (int each = 0; each < choices; each++) {
                parts.add("(x <= " + (100 + each) + " || x >= " + each + ")");
            }
            List<RowToRun> rows = rowsFoundFor(
                    "List.any(x -> " + String.join(" && ", parts) + ", sched1(c).value)");

            assertEquals(2, rows.size(), () -> "a row for each rule: " + rows);
        }
    }

    /**
     * Some element of what a dependency answered meeting one of two things, one of which comes to
     * more ways than are read, is composed along what was read — whichever of the two is written
     * first.
     */
    @Test
    void aChoiceOneSideOfWhichPassesTheFigureIsComposedAlongWhatWasRead() {
        String past = TheWaysAnElementMayMeetAStatementLeaveOutTheOnesNoElementMeetsTest
                .pastTheFigure();
        for (String body : List.of("x.a == 357 || " + past, past + " || x.a == 357")) {
            List<RowToRun> rows = rowsFoundIn(PAIRS.replace("BODY",
                    "List.any(x -> " + body + ", sched1(c).value)"));

            assertEquals(2, rows.size(), () -> "a row for each rule of " + body + ": " + rows);
        }
    }

    /**
     * Ways the truths asked of the answer close are not looked along, however many come first,
     * and the way left is composed along: the statement is met and nothing is said of it.
     *
     * <p>The answer is asked to be {@code ok}, and the statement beside it to meet one of more
     * things than a way is looked along. The first of them each ask it not to be — two truths
     * asked of one place, which no value is — and the last does not.
     */
    @Test
    void waysTheTruthsAskedCloseAreNotLookedAlongAndTheOneLeftIsComposed() {
        List<String> alternatives = new ArrayList<>();
        for (int each = 0; each < CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum(); each++) {
            alternatives.add("(Bool.not(v.ok) && v.n == " + each + ")");
        }
        alternatives.add("(v.ok && v.n >= 100)");
        Compilation compilation = Compilation.ofSource("""
                module p

                data Cat = A | B
                data Reply = { ok: Bool, n: Int }
                data Yes
                data No
                data Answer = Yes | No

                behavior r : (c: Cat) -> Reply

                behavior f : (c: Cat) -> Answer
                    depends on r
                let f (c, r) = {
                    let v = r(c)
                    if v.ok && (ALTERNATIVES) then Yes else No
                }
                """.replace("ALTERNATIVES", String.join(" || ", alternatives)), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();

        List<DemandGap.WhyNotComposed> said = new ArrayList<>();
        Collection<RuleSettlement> rules = compilation.db()
                .ask(new Adequacy.DecisionSearch(module, "f")).value().values().stream()
                .map(each -> each.answer().settlement()).toList();
        for (RuleSettlement each : rules) {
            for (DemandGap gap : each.account().onAnAnswer()) {
                if (gap instanceof DemandGap.Uncomposed(AnswerDemand.AStatement _, var why)) {
                    said.add(why);
                }
            }
        }

        assertTrue(rules.stream().allMatch(each ->
                        each.requirement() instanceof RuleRequirement.Required),
                () -> "a row stands in each rule: " + rules);
        assertEquals(List.of(), said, "and nothing is said of the statement");
    }

    /**
     * A count of statements about the answer held against a number of the input is two numbers,
     * and the reading of what the comparison means has nothing to hold to a figure; put at the
     * value the way leaves the input's number at, it is a count alone against a constant, which is
     * as many choices of which statements hold as there are ways of picking that many. Past the
     * readings of one condition, which is as many choices as are handed to a reader of them, the
     * statement is said to be one that figure stopped the composing of — and not one nothing
     * composes for, or one about something other than the answer.
     */
    @Test
    void aCountLeftAloneByANumberPutAtAValueIsHeldToTheFigure() {
        List<String> written = new ArrayList<>();
        for (int each = 0; each < 18; each++) {
            written.add("v.n + " + each);
        }
        Compilation compilation = Compilation.ofSource("""
                module p

                data Cat = A | B
                data Reply = { n: Int }
                data Yes
                data No
                data Answer = Yes | No

                behavior r : (c: Cat) -> Reply

                behavior f : (c: Cat, on: Int) -> Answer
                    depends on r
                let f (c, on, r) = {
                    let v = r(c)
                    if on == 9 && List.length(List.filter(x -> x > 0, [WRITTEN])) == on
                    then Yes
                    else No
                }
                """.replace("WRITTEN", String.join(", ", written)), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();

        List<DemandGap.WhyNotComposed> said = new ArrayList<>();
        for (RuleSettlement each : compilation.db()
                .ask(new Adequacy.DecisionSearch(module, "f")).value().values().stream()
                .map(each -> each.answer().settlement()).toList()) {
            for (DemandGap gap : each.account().onAnAnswer()) {
                if (gap instanceof DemandGap.Uncomposed(AnswerDemand.AStatement _, var why)) {
                    said.add(why);
                }
            }
        }

        assertTrue(said.stream().anyMatch(why ->
                        why instanceof DemandGap.WhyNotComposed.NoWayComposedBeforeAFigureEnded(
                                var figures)
                                && figures.written().contains(
                                        CompositionBudget.READINGS_OF_ONE_CONDITION)),
                () -> "the statement is said to be one the figure stopped: " + said);
    }

    /** What the dependency answers is a list of elements of two numbers. */
    private static final String PAIRS = """
            module p

            data Cat = A | B
            data P = { a: Int, b: Int }
            data Sched = List<P>
            data Yes
            data No
            data Answer = Yes | No

            behavior sched1 : (c: Cat) -> Sched

            behavior f : (c: Cat) -> Answer
                depends on sched1
            let f (c, sched1) = if BODY then Yes else No
            """;

    /**
     * A choice between relations of one number written as a conjunction of disjunctions is, taken
     * apart, mostly choices no element meets: an element at most nought is never at least a
     * hundred and one. Those are not looked at, and what is left is few enough to compose along.
     *
     * <p>As many choices as a way is looked along, so the other side — no element meeting it,
     * which is every element meeting one of that many ranges — has as many ways for an element as
     * well.
     */
    @Test
    void aStatementOfManyChoicesNoElementMeetsTogetherIsComposed() {
        List<String> parts = new ArrayList<>();
        for (int each = 0; each < CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum(); each++) {
            parts.add("(x <= " + each + " || x >= " + (100 + each) + ")");
        }
        List<RowToRun> rows = rowsFoundFor(
                "List.any(x -> " + String.join(" && ", parts) + ", sched1(c).value)");

        assertEquals(2, rows.size(), () -> "a row for each rule: " + rows);
    }

    /**
     * A count of an answer's list held against a number of the input is the answer's to compose,
     * and the way the input is read does not say it is a count nothing composes.
     */
    @Test
    void aCountOfAnAnswersListIsNotAlsoLeftOnTheWay() {
        Compilation compilation = Compilation.ofSource(MODEL.replace("BODY",
                "List.length(List.filter(x -> x <= on, sched1(c).value)) >= on"), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();

        for (RuleSettlement each : compilation.db()
                .ask(new Adequacy.DecisionSearch(module, "f")).value().values().stream()
                .map(each -> each.answer().settlement()).toList()) {
            assertInstanceOf(RuleRequirement.Required.class, each.requirement(),
                    () -> "a row for each rule: " + each);
            assertEquals(List.of(), each.account().onTheWay(),
                    () -> "and nothing of the input is said to have gone without: " + each);
        }
    }

    /** A number of the answer compared with one of the input is met by the same pair. */
    @Test
    void aNumberOfTheAnswerComparedWithOneOfTheInputIsMetByThePair() {
        List<RowToRun> rows = rowsFoundFor("List.length(sched1(c).value) >= on");

        assertEquals(List.of(false, true), rows.stream().map(row -> {
                    long on = Long.parseLong(row.inputs().get(1).text().trim());
                    return elementsOf(((StoodInAnswer.OnTheRow) row.answers().getFirst())
                            .value().text()).size() >= on;
                }).sorted().toList(),
                () -> "one row holds as many as the number and the other holds fewer: " + rows);
    }

    /**
     * And what is about two answers is not composed for, which says so. Which value either may be
     * turns on the other, and nothing here composes two of them together.
     */
    @Test
    void aStatementAboutTwoAnswersIsDeclinedAndSaysSo() {
        String source = MODEL_OF_TWO.replace("BODY",
                "List.any(x -> List.any(y -> x <= y, sched2(c).value), sched1(c).value)");
        for (DecisionReading.Ruled each : DecisionReadings.of(source, "f").found()) {
            assertEquals(List.of(new DemandGap.WhyNotStated.AStatementOfSeveralParts()),
                    each.demands().declined().stream().map(DemandGap.Unstated::why).toList(),
                    () -> "it is about the pair: " + each.demands());
            assertTrue(each.demands().stated().isEmpty(),
                    () -> "and nothing is composed to it: " + each.demands());
        }
    }

    /**
     * What the issue wrote, as it wrote it: a count over a filter handed back as the answer, with no
     * decision in the body at all, and a count held against a number beside it.
     */
    @Test
    void theIssuesOwnModelIsNoLongerReportedAsUnread() {
        String json = reportOfSource("""
                module p

                data Cat = A | B
                data Sched = List<Int>

                behavior sched1 : (c: Cat) -> Sched

                behavior f : (c: Cat, on: Int) -> Int
                    depends on sched1

                let f (c, on, sched1) = List.length(List.filter(x -> x <= on, sched1(c).value))

                behavior g : (c: Cat) -> Bool
                    depends on sched1

                let g (c, sched1) = List.length(sched1(c).value) >= 1
                """);

        assertFalse(json.contains("unsupported_syntax"), "no rule is left as a form nobody reads");
        assertFalse(json.contains("rule_unread"), "and none weakens what the report claims");
        assertFalse(json.contains("rule_about_a_derived_value"),
                "and none is about a value made from another one");
    }

    /**
     * What is held of a container is wider than what is read of an answer. How many different values
     * the elements come to is a number of the input's own places, which an answer has none of, so
     * it is said to be unread — a quantity that can be written is not thereby one that is composed.
     */
    @Test
    void aNumberOverTheElementsOfAnAnswerIsSaidToBeUnreadAndNotThrown() {
        String json = reportOf("List.length(List.distinct(sched1(c).value)) >= 2");

        assertTrue(json.contains("container_at_no_position"),
                "the container is said to stand at no position a row writes");
    }

    /** What the issue wrote is read: no rule of it is left as one nothing read. */
    @Test
    void whatTheIssueWroteIsNoLongerReportedAsUnread() {
        String json = reportOf("List.length(List.filter(x -> x <= on, sched1(c).value)) >= 1");

        assertFalse(json.contains("unsupported_syntax"), "no rule is left as a form nobody reads");
        assertFalse(json.contains("rule_unread"), "and none weakens what the report claims");
    }

    /** The row the search stood each rule of the way in with. */
    private static List<RowToRun> rowsFoundFor(String body) {
        return rowsFoundIn(MODEL.replace("BODY", body));
    }

    private static List<RowToRun> rowsFoundIn(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        List<RowToRun> rows = new ArrayList<>();
        for (RuleSettlement each : compilation.db()
                .ask(new Adequacy.DecisionSearch(module, "f")).value().values().stream()
                .map(each -> each.answer().settlement()).toList()) {
            if (each.requirement() instanceof RuleRequirement.Required(RowToRun row)) {
                rows.add(row);
            }
        }
        return rows;
    }

    private static List<AnswersDemanded> waysOf(String body) {
        return DecisionReadings.of(MODEL.replace("BODY", body), "f").found().stream()
                .map(DecisionReading.Ruled::demands).toList();
    }

    /** The elements of the value composed for each way of {@code body}, in the order of the ways. */
    private static List<List<Long>> composedForEachWay(String body) {
        String source = MODEL.replace("BODY", body);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        InputDomain domain = compilation.db().ask(new Adequacy.Inputs(module)).value().get("holds");
        Partitions.Partitioning divided =
                compilation.db().ask(new Adequacy.Divided(module, "holds")).value();
        InputReading reading = domain.reading(RuleReadings.of(compilation, module));
        MeasuredInput subject = MeasuredInput.of("holds", reading, divided);
        List<List<Long>> out = new ArrayList<>();
        for (AnswersDemanded each : waysOf(body)) {
            AnAnswerComposed.Attempt attempt = AnAnswerComposed.of(subject,
                    StatementsOfAnInput.of(reading), each.stated());
            AnAnswerComposed.Outcome.Composed composed = assertInstanceOf(
                    AnAnswerComposed.Outcome.Composed.class, attempt.outcome(),
                    () -> "a value is composed for " + each + ": " + attempt);
            assertTrue(attempt.unaccounted().isEmpty(),
                    () -> "and it meets every demand: " + attempt.unaccounted());
            out.add(elementsOf(composed.value().text()));
        }
        return out;
    }

    private static List<Long> elementsOf(String written) {
        List<Long> out = new ArrayList<>();
        Matcher found = NUMBER.matcher(written.substring(written.indexOf('[')));
        while (found.find()) {
            out.add(Long.parseLong(found.group()));
        }
        return out;
    }

    private static String reportOf(String body) {
        return reportOfSource(MODEL.replace("BODY", body));
    }

    private static String reportOfSource(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }
}
