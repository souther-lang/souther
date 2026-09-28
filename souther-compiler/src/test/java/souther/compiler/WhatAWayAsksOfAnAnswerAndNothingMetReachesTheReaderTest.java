package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.RuleRequirement;
import souther.compiler.query.RuleSearch;
import souther.compiler.query.RuleSettlement;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A condition about what a dependency answers that nothing composed a value against reaches a
 * reader, at the place it was written and in the words of the stage that let it go.
 *
 * <p><b>Both stages, and the same reader.</b> A condition the demand reading has no way of stating
 * and one it stated that no value could be composed under are different facts to act on and are
 * owed to the same person. Told apart only by which word the search came back with, an author was
 * shown two sentences that name neither the condition nor where it is, and which of the two they
 * got followed from which stage happened to refuse.
 *
 * <p><b>And a condition the answer side did take up is not one of them.</b> The reading of the way
 * over the input declines every condition about an answer — the region a row is searched in is over
 * the input's positions, and an answer stands at none of them — so a reader given both accounts as
 * they stand would be told a condition this compiler composed a value against was left out.
 */
class WhatAWayAsksOfAnAnswerAndNothingMetReachesTheReaderTest {

    /** A demand the reading states and the answer's own region cannot carry. */
    private static final String RECORDS_COMPARED = """
            module example.records

            data K = { id: Int }
            data R = { k: K, j: K }
            data Yes
            data No
            data Answer = Yes | No

            behavior look : (at: Int) -> R

            behavior decides : (at: Int) -> Answer
                depends on look
            let decides (at, look) = if look(at).k == look(at).j then Yes else No
            """;

    /** And one the reading has no way of stating at all. */
    private static final String A_TRUTH_INSIDE_THE_ANSWER = """
            module example.inside

            data Reading = { ok: Bool, at: Int }
            data Yes
            data No
            data Answer = Yes | No

            behavior look : (at: Int) -> Reading

            behavior decides : (at: Int) -> Answer
                depends on look
            let decides (at, look) = if look(at).ok then Yes else No
            """;

    /**
     * The control: the same shape of condition, where the answer side states it and composes a
     * value for it.
     *
     * <p>Numbers, because a difference between two of them stands on an order the region measures.
     * The way over the input declines this comparison exactly as it declines the two above, so a
     * page naming it here would be naming a condition nothing was short of.
     */
    private static final String NUMBERS_COMPARED = """
            module example.numbers

            data Reading = { n: Int, m: Int }
            data Yes
            data No
            data Answer = Yes | No

            behavior look : (at: Int) -> Reading

            behavior decides : (at: Int) -> Answer
                depends on look
            let decides (at, look) = if look(at).n < look(at).m then Yes else No
            """;

    /**
     * The same condition the answer side takes up, under a rule nothing composed a row for.
     *
     * <p>Where the control above has a row at every rule, this one has none: the input's own rules
     * leave no value, so every way of the decision comes back with nothing composed. Which is what
     * puts the way's account in front of a reader — and the comparison over what the dependency
     * answers is in that way, declined by the reading over the input like any other condition about
     * an answer.
     */
    private static final String NUMBERS_COMPARED_WHERE_NO_INPUT_COMPOSES = """
            module example.neither

            data Amount = Int
                invariant range = value >= 0 && value <= 3

            data R = { a1: Amount, a2: Amount }
                invariant rule = a1.value * a2.value >= 100

            data Reading = { n: Int, m: Int }
            data Yes
            data No
            data Answer = Yes | No

            behavior look : (at: Int) -> Reading

            behavior decides : (r: R, at: Int) -> Answer
                depends on look
            let decides (r, at, look) = if look(at).n < look(at).m then Yes else No
            """;

    private static final String LEFT_OUT =
            "not every condition on the way to the rule is one the row was composed against";

    /** What the composer could not carry is named, and where it is written. */
    @Test
    void aDemandTheAnswersRegionCannotCarryIsNamedWhereItIsWritten() {
        String said = whereNothingCouldShowARow(RECORDS_COMPARED);

        assertTrue(said.contains(LEFT_OUT), () -> said);
        assertTrue(said.contains("a comparison of places inside an answer whose values stand on no"
                        + " order this measures them on"),
                () -> "in the words of the stage that let it go: " + said);
        assertTrue(said.contains("13:40"),
                () -> "and at the place the condition is written: " + said);
    }

    /** And so is what the reading could not state. */
    @Test
    void aDemandTheReadingCannotStateIsNamedWhereItIsWritten() {
        String said = whereNothingCouldShowARow(A_TRUTH_INSIDE_THE_ANSWER);

        assertTrue(said.contains(LEFT_OUT), () -> said);
        assertTrue(said.contains("a truth read off a place inside what a dependency answers"),
                () -> "in the words of the stage that let it go: " + said);
        assertTrue(said.contains("12:38"),
                () -> "and at the place the condition is written: " + said);
    }

    /**
     * A condition the answer side answered for is named by neither account.
     *
     * <p>The other half of the sentence above. Without it, the clause could be one every body that
     * decides on what a dependency answers carries, which says nothing about the ones that are
     * short of something.
     */
    @Test
    void aConditionTheAnswerSideTookUpIsNotReportedAsLeftOut() {
        String page = human(NUMBERS_COMPARED);

        assertFalse(page.contains(LEFT_OUT),
                () -> "the demand was stated and a value was composed against it: " + page);
    }

    /**
     * And not where the rules of the input leave nothing either, which is where the way's own
     * account is put in front of a reader.
     *
     * <p>The case that makes the one above worth reading. There the clause is absent because no
     * rule of the body is one nothing composed a row for; here every rule is, the line carries what
     * the way was composed without, and the condition about what the dependency answers is still
     * not among them.
     */
    @Test
    void norWhereTheWaysOwnAccountIsShown() {
        String said = whereNothingCouldShowARow(NUMBERS_COMPARED_WHERE_NO_INPUT_COMPOSES);

        assertFalse(said.contains("a comparison this reading could not turn into a cut"),
                () -> "the reading over the input declines it and the answer side took it up: "
                        + said);
    }

    /**
     * A row that leaned on the module's table without meeting the demand settles nothing about the
     * rule it went past.
     *
     * <p>The table answers every call, so a value for the dependency exists and the row runs. What
     * it does not do is meet what the way asks, so where it went is what a row composed against
     * less than the way asks does — and the rule it did not take is left where it was rather than
     * reported as one nothing takes.
     */
    @Test
    void aRowComposedWithoutTheDemandDoesNotRefuteTheRuleItWentPast() {
        AdequacyReport.BehaviorReport behavior = reportOf(RECORDS_COMPARED + """

                let same = R { k = K { id = 1 }, j = K { id = 1 } }

                fake look
                    | _ -> same
                """);

        List<RuleSettlement> unsettled = behavior.ruleSettlements().values().stream()
                .filter(each -> !(each.requirement() instanceof RuleRequirement.Required))
                .toList();
        assertFalse(unsettled.isEmpty(), "a rule of this body is one no row was seen taking");
        for (RuleSettlement each : unsettled) {
            assertInstanceOf(RuleRequirement.Unsettled.AComposedRowWasShortOfTheWay.class,
                    each.requirement(),
                    () -> "a row meeting less than the way asks settles nothing about it: " + each);
            // And the row it was is not denied. What was composed and run is what the search says
            // it did, so a reader is not told that nothing was composed to try the rule with.
            assertInstanceOf(RuleSearch.Composed.class, each.search(),
                    () -> "a row was composed and tried all the same: " + each);
            assertFalse(each.account().onAnAnswer().isEmpty(),
                    () -> "and which demand it was composed without: " + each);
        }
    }

    /** The line of the page that says nothing could show a row can be written at the rules. */
    private static String whereNothingCouldShowARow(String model) {
        for (String line : human(model).split("\n")) {
            if (line.contains("nothing could show a row can be written at")
                    && line.contains("decision rule")) {
                return line;
            }
        }
        throw new AssertionError("this model has rules nothing composed a row for:\n"
                + human(model));
    }

    private static AdequacyReport.BehaviorReport reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).modules().stream()
                .flatMap(module -> module.behaviors().stream())
                .filter(each -> "decides".equals(each.name()))
                .findFirst().orElseThrow(
                        () -> new AssertionError("the model under test writes `decides`"));
    }

    private static String human(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
