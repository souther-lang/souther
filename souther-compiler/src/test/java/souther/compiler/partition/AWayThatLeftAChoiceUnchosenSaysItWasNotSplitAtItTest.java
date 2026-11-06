package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.StringJoiner;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A way the looking left a choice of unchosen on is said to be one not split at that choice past
 * the figure, so that a row composed along it is not taken to have met what the choice asks.
 *
 * <p>The choices on {@code p} are walked to the figure: each asks {@code q} of its own or {@code p},
 * and the last asks {@code p} not to hold, so only the way that chose every {@code q} is open, and
 * it is the first found. The choice on {@code b} turns on no position of theirs and is in a group
 * of its own, which the figure leaves nothing to look with.
 */
class AWayThatLeftAChoiceUnchosenSaysItWasNotSplitAtItTest {

    private static final int ASKED_OF_Q = 12;

    private static final ConditionReportAnchor WHERE =
            new ConditionReportAnchor.WhereTheReadingMetIt("m",
                    new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, 0));

    @Test
    void eachWayLookedAlongIsNotSplitAtTheChoiceLeft() {
        List<OnTheWay> onTheWay = new ArrayList<>();
        for (int each = 1; each <= ASKED_OF_Q; each++) {
            onTheWay.add(oneOf(each, List.of(truth("q" + each, true)), List.of(truth("p", true))));
        }
        onTheWay.add(oneOf(ASKED_OF_Q + 1, List.of(truth("p", false)),
                List.of(truth("p", false), truth("q1", true))));
        OnTheWay.OneOf onB = oneOf(ASKED_OF_Q + 2, List.of(truth("b", true)),
                List.of(truth("b", false)));
        onTheWay.add(onB);

        Reachability.Reaching reaching = assertInstanceOf(Reachability.Reaching.class,
                Reachability.of(new WayToTheBorder(onTheWay), reading().quantities().region()));
        Reachability.Ways.Whole whole = assertInstanceOf(Reachability.Ways.Whole.class,
                reaching.ways(), "not every way a row takes was looked at");
        assertEquals(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT, whole.figure());
        assertFalse(whole.along().isEmpty(), () -> "the open way found is looked along: " + whole);
        for (Reachability.Reaching along : whole.along()) {
            Reachability.Ways.Whole left = assertInstanceOf(Reachability.Ways.Whole.class,
                    along.ways(), "the choice left is one the way was not split at");
            assertEquals(List.of(onB), left.unsplit());
            assertEquals(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT, left.figure());
            assertEquals(List.of(), left.along());
        }
        assertEquals(whole.along().stream().map(_ -> Optional.<List<OnTheWay>>empty()).toList(),
                whole.chosenAs(), "a way a choice was left on was chosen as no conditions");
    }

    /** Each way a way is split into is the one the conditions beside it were chosen as: read
     *  again from them, it is that way, at the same place. */
    @Test
    void eachWayItIsSplitIntoIsWhatItWasChosenAs() {
        InputReading reading = reading();
        List<OnTheWay> onTheWay = List.of(
                oneOf(1, List.of(truth("q1", true)), List.of(truth("q2", true))),
                oneOf(2, List.of(truth("q3", true)), List.of(truth("q1", false))));
        Reachability.Reaching reaching = assertInstanceOf(Reachability.Reaching.class,
                Reachability.of(new WayToTheBorder(onTheWay), reading.quantities().region()));
        Reachability.Ways.Each each = assertInstanceOf(Reachability.Ways.Each.class,
                reaching.ways());
        assertEquals(3, each.along().size(), () -> "q1 asked both ways closes one: " + each);
        for (int at = 0; at < each.along().size(); at++) {
            List<OnTheWay> chosen = each.chosenAs().get(at).orElseThrow();
            assertEquals(each.along().get(at), Reachability.of(new WayToTheBorder(chosen),
                    reading.quantities().region()), "way " + at);
        }
    }

    @Test
    void aRowIsTriedAlongEachWayPastTheFigureAndThenAlongTheWayWhole() {
        List<OnTheWay> onTheWay = new ArrayList<>();
        for (int each = 1; each <= ASKED_OF_Q; each++) {
            onTheWay.add(oneOf(each, List.of(truth("q" + each, true)), List.of(truth("p", true))));
        }
        onTheWay.add(oneOf(ASKED_OF_Q + 1, List.of(truth("p", false)),
                List.of(truth("p", false), truth("q1", true))));
        onTheWay.add(oneOf(ASKED_OF_Q + 2, List.of(truth("b", true)), List.of(truth("b", false))));

        Reachability.Reaching reaching = assertInstanceOf(Reachability.Reaching.class,
                Reachability.of(new WayToTheBorder(onTheWay), reading().quantities().region()));

        List<Reachability.Reaching> tried = reaching.waysToTryForARow();
        List<Reachability.Reaching> expected = new ArrayList<>();
        for (Reachability.Reaching along : reaching.along()) {
            expected.addAll(along.waysToTryForARow());
        }
        expected.add(reaching);
        assertEquals(expected, tried);
        assertFalse(reaching.along().contains(tried.getLast()),
                "the way whole is tried past the ways it is split into");
    }

    @Test
    void aWayThatIsNotSplitIsTriedWhole() {
        Reachability.Reaching reaching = assertInstanceOf(Reachability.Reaching.class,
                Reachability.of(new WayToTheBorder(List.of()), reading().quantities().region()));

        assertInstanceOf(Reachability.Ways.One.class, reaching.ways());
        assertEquals(List.of(), reaching.along());
        assertEquals(List.of(reaching), reaching.waysToTryForARow());
    }

    private static OnTheWay.OneOf oneOf(int occurrence, List<OnTheWay> one,
                                        List<OnTheWay> other) {
        return OnTheWay.OneOf.of(
                new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, occurrence),
                WHERE, List.of(one, other), Optional.empty());
    }

    private static OnTheWay truth(String field, boolean held) {
        return new OnTheWay.TakenIn(WHERE,
                new RowDemand.ATruth(TermPath.of("r").then(field), held), NamedElements.NONE);
    }

    private static InputReading reading() {
        StringJoiner fields = new StringJoiner(", ");
        fields.add("p: Bool").add("b: Bool");
        for (int each = 1; each <= ASKED_OF_Q; each++) {
            fields.add("q" + each + ": Bool");
        }
        Compilation compilation = Compilation.ofSource("""
                module m

                data R = { %s }
                data Yes

                behavior f : (r: R) -> Yes
                let f (r) = Yes
                """.formatted(fields), "Main");
        var inputs = compilation.db().ask(new Adequacy.Inputs("m")).value().get("f");
        assertNotNull(inputs, "the model under test compiles");
        return inputs.reading(RuleReadings.of(compilation, "m"));
    }
}
