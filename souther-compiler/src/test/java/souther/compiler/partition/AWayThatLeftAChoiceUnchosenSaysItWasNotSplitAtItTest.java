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
            new ConditionReportAnchor.WhereTheReadingMetIt("m", new ConditionOccurrence("f", 0));

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
            assertEquals(new Reachability.Ways.Whole(List.of(onB),
                            CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT, List.of()),
                    along.ways(), "the choice left is one the way was not split at");
        }
    }

    private static OnTheWay.OneOf oneOf(int occurrence, List<OnTheWay> one,
                                        List<OnTheWay> other) {
        return new OnTheWay.OneOf(new ConditionOccurrence("f", occurrence), WHERE,
                List.of(one, other), Optional.empty());
    }

    private static OnTheWay truth(String field, boolean held) {
        return new OnTheWay.TakenIn(WHERE,
                new RowDemand.ATruth(TermPath.of("r").then(field), held));
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
        compilation.answerEverything();
        var inputs = compilation.db().ask(new Adequacy.Inputs("m")).value().get("f");
        assertNotNull(inputs, "the model under test compiles");
        return inputs.reading(RuleReadings.of(compilation, "m"));
    }
}
