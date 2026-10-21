package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.StringJoiner;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A way of writing the elements alike that the looking left a demand of unchosen keeps the demand
 * as it was asked, and the figure that left it, so that a row composed along the way says it was
 * composed without it rather than having met it.
 *
 * <p>What the elements of {@code xs} are asked is walked to the figure: each demand asks {@code q}
 * of its own or {@code p}, and the last asks {@code p} not to hold, so only the way that chose
 * every {@code q} is open, and it is the first found. What the elements of {@code ys} are asked
 * turns on none of their positions, and the figure leaves nothing to look at it with.
 */
class AWayWrittenAlikeThatLeftADemandUnchosenSaysWhyTest {

    private static final int ASKED_OF_Q = 12;

    private static final ConditionReportAnchor WHERE =
            new ConditionReportAnchor.WhereTheReadingMetIt("m",
                    new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, 0));

    private static final TermPath XS = TermPath.of("xs");

    private static final TermPath YS = TermPath.of("ys");

    @Test
    void theDemandLeftStandsAsItWasAskedWithTheFigure() {
        List<OnTheWay.TakenIn> asked = new ArrayList<>();
        for (int each = 1; each <= ASKED_OF_Q; each++) {
            asked.add(someElement(XS, List.of(truth(XS, "q" + each, true)),
                    List.of(truth(XS, "p", true))));
        }
        asked.add(someElement(XS, List.of(truth(XS, "p", false)),
                List.of(truth(XS, "p", false), truth(XS, "q1", true))));
        OnTheWay.TakenIn ofYs = someElement(YS, List.of(truth(YS, "b", true)),
                List.of(truth(YS, "b", false)));
        asked.add(ofYs);

        ElementsWrittenAlike.Choices choices = ElementsWrittenAlike.of(new Reachability.Reaching(
                reading().quantities().region(), Requirements.NONE, TruthsAsked.NONE, asked,
                Reachability.Ways.ONE, List.of()));

        assertEquals(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT, choices.stoppedBy());
        assertFalse(choices.ways().isEmpty(), () -> "the open way found: " + choices);
        for (ElementsWrittenAlike.Alike each : choices.ways()) {
            assertEquals(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT, each.leftBy(),
                    () -> "the figure that left a demand of it: " + each);
            assertTrue(each.reaching().boundedOnTheWay().contains(ofYs),
                    () -> "the demand left, as it was asked: " + each);
        }
    }

    private static OnTheWay.TakenIn someElement(TermPath container,
                                                List<RowDemand.OfAnElement> one,
                                                List<RowDemand.OfAnElement> other) {
        return new OnTheWay.TakenIn(WHERE, new RowDemand.Exists(container,
                new RowDemand.AnElementMeets(List.of(one, other)),
                new RowDemand.Relational(new TakenConstraint.Affine(
                        LinearForm.atom(new NumericTerm.ValueOf(container.then("n"))), Rel.GE)),
                Optional.empty()));
    }

    private static RowDemand.ATruth truth(TermPath container, String field, boolean held) {
        return new RowDemand.ATruth(container.element().then(field), held);
    }

    private static InputReading reading() {
        StringJoiner fields = new StringJoiner(", ");
        fields.add("p: Bool");
        for (int each = 1; each <= ASKED_OF_Q; each++) {
            fields.add("q" + each + ": Bool");
        }
        Compilation compilation = Compilation.ofSource("""
                module m

                data E = { %s }
                data F = { b: Bool }
                data Yes

                behavior f : (xs: List<E>, ys: List<F>) -> Yes
                let f (xs, ys) = Yes
                """.formatted(fields), "Main");
        var inputs = compilation.db().ask(new Adequacy.Inputs("m")).value().get("f");
        assertNotNull(inputs, "the model under test compiles");
        return inputs.reading(RuleReadings.of(compilation, "m"));
    }
}
