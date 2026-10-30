package souther.compiler.inputs;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.QuotedFrom;
import souther.compiler.diag.SourceProvenance;
import souther.compiler.observe.Figure;
import souther.compiler.partition.ClassOfAPosition;
import souther.compiler.partition.ReportedReason;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;
import souther.compiler.values.StoppedReading;
import souther.test.Nightly;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The values the orders are asked over leave out no value of a component that some combination of
 * the others takes.
 *
 * <p>Each value of a component is put beside the nearest values of the others ({@link ValuesOfAType}),
 * because asked over every combination a value none of them takes cost the better part of a million
 * constructions to refuse. What the nearest values could leave out is a value a constructor takes
 * only beside more of the others moved — an absence meant only beside two other components, say —
 * and an order is owed an answer for it as for any value. So the values are made both ways here,
 * over the types the orders are asked of and every type those reach, and each value of each
 * component every combination makes is held to be in some value the nearest ones make.
 *
 * <p>Nightly, for what it costs: it is the one place every combination is asked, and what it guards
 * is a record that comes to tie a value to more than one other component, which is a change to the
 * record and not to anything a change elsewhere would move.
 */
@Nightly
class TheNearestValuesOfATypeAreTheValuesEveryCombinationMakesTest {

    /**
     * The types a steady order is asked over ({@code ASteadyOrderTellsApartWhateverEqualityTellsApartTest},
     * {@code ReasonsComeOutInASteadyOrderWhicheverWayTheyWereMetTest}), but {@link ReportedReason.Stop}.
     *
     * <p>Stop's constructor refuses a null and nothing else, so there is no value that only some
     * combination of its components takes, and every combination of them is the product of what
     * they are offered. {@code ReportedReasonStopRefusesANullAndNothingElseTest} holds that on every
     * run.
     */
    private static final List<Class<?>> ASKED = List.of(BlockReason.RuleReadingStopped.class,
            RuleReasons.Said.class, RuleSite.class, WrittenOwner.class, SourceConstructOrigin.class,
            QuotedFrom.class, SourceProvenance.class, StoppedReading.class,
            ClassOfAPosition.class, Figure.class);

    @Test
    void everyValueOfAComponentAnyCombinationTakesIsInSomeValueTheNearestMake() {
        ValuesOfAType nearest = new ValuesOfAType();
        ValuesOfAType every = ValuesOfAType.everyCombination();
        for (Class<?> type : ASKED) {
            nearest.of(type);
            every.of(type);
        }
        assertEquals(List.of(), ValuesOfAType.valuesLeftOut(nearest, every),
                "values a constructor takes only beside more of the others moved than the nearest"
                        + " values move, which no order is asked over");
    }
}
