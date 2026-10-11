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
import java.util.List;
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

    /** What the issue wrote is read: no rule of it is left as one nothing read. */
    @Test
    void whatTheIssueWroteIsNoLongerReportedAsUnread() {
        String json = reportOf("List.length(List.filter(x -> x <= on, sched1(c).value)) >= 1");

        assertFalse(json.contains("unsupported_syntax"), "no rule is left as a form nobody reads");
        assertFalse(json.contains("rule_unread"), "and none weakens what the report claims");
    }

    /** The row the search stood each rule of the way in with. */
    private static List<RowToRun> rowsFoundFor(String body) {
        Compilation compilation = Compilation.ofSource(MODEL.replace("BODY", body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        List<RowToRun> rows = new ArrayList<>();
        for (RuleSettlement each : compilation.db()
                .ask(new Adequacy.DecisionSearch(module, "f")).value().values()) {
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
                    AnswerStatements.of(reading), each.stated());
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
        Compilation compilation = Compilation.ofSource(MODEL.replace("BODY", body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }
}
