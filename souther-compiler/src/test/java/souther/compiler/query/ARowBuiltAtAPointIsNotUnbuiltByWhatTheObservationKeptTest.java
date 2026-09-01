package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.Limits;
import souther.compiler.partition.PointRole;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a search composed stays composed, whatever an observation of it kept.
 *
 * <p>A value built for a point goes through the module's own decoders and is then read back, to see
 * that it landed where it was built for. That reading is walked under the limits an observation is
 * held to, so a value the limits stop is a value nothing can place — and the row is as built as it
 * ever was. What the search may report is that it could not confirm the row; what it may not report
 * is that it composed nothing, which is the sentence an author reads as the model refusing a row.
 *
 * <p><b>The pair is the measurement, and it is one character wide.</b> Both models ask for a row at
 * a length; they differ in whether that length is one an observation keeps. Held on the far side
 * alone, a reading that never composes anything at all passes.
 *
 * <p>And what fired is asserted beside what came of it. The same two words come back whichever
 * budget an observation ran out of, so a test reading the outcome alone would go green on a model
 * that crossed some other limit — or on one that this compiler declined to compose a value for at
 * all, which is a different thing to fix.
 */
class ARowBuiltAtAPointIsNotUnbuiltByWhatTheObservationKeptTest {

    /**
     * A rule on the length of a text, with one short row written.
     *
     * <p>The text budget and no other. A row at the point is one string, so nothing here composes a
     * collection, nests anything, or holds more than a handful of nodes — the other three limits
     * are nowhere near, and the one being measured is crossed by the value the point asks for.
     */
    private static String model(int length) {
        return """
                module example.text

                data 長い
                data 短い

                behavior 判定する : (文字: String) -> 長い | 短い

                let 判定する (文字) =
                    if String.length(文字) >= %d
                    then 長い else 短い

                example 判定する
                    | "短いなら短い" : ("abc") -> 短い
                """.formatted(length);
    }

    /**
     * A point at exactly what the limits keep is confirmed, which is the near side of the pair.
     *
     * <p>{@link Limits#DEFAULT} keeps a text of {@code maxText} characters and stops at one more, so
     * this is the longest row the reading back can place.
     */
    @Test
    void aRowTheObservationKeepsIsConfirmedWhereItWasBuilt() {
        ItemAssessment.Attempt at = attemptAt(Limits.DEFAULT.maxText(), PointRole.ON);

        assertInstanceOf(ItemAssessment.Attempt.Certified.class, at,
                "a row of exactly what the limits keep is read back where it was built for");
    }

    /**
     * One character more, and the row is built and unconfirmed rather than never composed.
     *
     * <p>The whole of the difference between the two is the limit. The search did the same work,
     * the decoders took the same kind of value, and what changed is that the walk that reads it
     * back stopped.
     */
    @Test
    void oneCharacterMoreLeavesTheRowBuiltAndUnconfirmed() {
        ItemAssessment.Attempt at = attemptAt(Limits.DEFAULT.maxText() + 1, PointRole.ON);

        ItemAssessment.Attempt.Unverified unverified = assertInstanceOf(
                ItemAssessment.Attempt.Unverified.class, at,
                "a value the limits stopped is a row this compiler could not place, not one it"
                        + " never composed");
        assertNotNull(unverified.row(),
                "and the row is offered, since composing it is what happened");
        assertEquals(new EstablishmentGap.Observation(
                        Set.of(Incompleteness.Code.VALUE_TRUNCATED)),
                unverified.why(),
                "what stopped the placing is the observation, and it says which way");
    }

    /**
     * And the point beside it in the same model is confirmed.
     *
     * <p>The control that says the model is not simply broken past the threshold: the row for the
     * point one below the line is a text of {@code maxText} characters, and it is placed.
     */
    @Test
    void thePointBesideItInTheSameModelIsStillConfirmed() {
        assertInstanceOf(ItemAssessment.Attempt.Certified.class,
                attemptAt(Limits.DEFAULT.maxText() + 1, PointRole.OFF),
                "the row one character shorter is the one the limits keep, and it is placed");
    }

    /**
     * And nothing about the point's grounds is invented from the row that was not placed.
     *
     * <p>A row built and not read back has shown nothing about the model. Counted as though it
     * had, the account would say a row can be written here because an observation was cut short,
     * which is this reading's own mistake made the other way round.
     */
    @Test
    void aRowNothingPlacedIsNotGroundsForAnything() {
        assertEquals(Set.of(ItemAssessment.WritabilityEvidence.Ground.THE_RULES_PROVE_IT),
                line(Limits.DEFAULT.maxText() + 1).owedAt(PointRole.ON)
                        .writabilityEvidence().grounds(),
                "the rules still prove it; the row that was not placed adds nothing");
    }

    private static ItemAssessment.Attempt attemptAt(int length, PointRole role) {
        return line(length).owedAt(role).searches().only();
    }

    private static BorderAssessment line(int length) {
        Compilation compilation = Compilation.ofSource(model(length), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(each -> each.diagnostic().code()).toList(),
                () -> "the model under test compiles at " + length);
        List<BorderAssessment> lines =
                Adequacy.readingsOf(compilation.db(), "example.text").get("判定する");
        assertNotNull(lines, () -> "the threshold draws a line at " + length);
        assertEquals(1, lines.size(), () -> "one line at " + length + ": " + lines);
        return lines.get(0);
    }
}
