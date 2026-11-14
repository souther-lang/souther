package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.Allowances;
import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * What a count of statements is written out as depends on the figure its compilation holds the
 * readings of one condition to, and what is kept of it is kept for that figure: a statement
 * written out where the figure was wide is not handed to a compilation held to a narrow one, which
 * would give it up, and one given up at a narrow figure is not handed to a wide one.
 *
 * <p>Asked in both orders, each over statements no other test writes out, since what is kept is
 * kept by the statement.
 */
class TheChoicesOfACountWrittenOutAtOneFigureAreNotHandedToAnotherFigureTest {

    private static final int FEW = 4;

    private static final Allowances NARROW =
            Allowances.DECLARED.with(CompositionBudget.READINGS_OF_ONE_CONDITION, FEW);

    /** Exactly one of {@code count} statements, each about a position of its own named from
     *  {@code named}: {@code count} choices. */
    private static Proposition exactlyOneOf(String named, int count) {
        List<Proposition> each = new ArrayList<>();
        for (int i = 0; i < count; i++) {
            each.add(new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(named + i)),
                    true));
        }
        return Proposition.compared(new Relation.Affine(new LinearForm<>(ExactRatio.of(-1),
                Map.of(new Quantity.HowManyHold(each), ExactRatio.ONE)), Rel.EQ), true);
    }

    @Test
    void whatWasWrittenOutAtTheDeclaredFigureIsGivenUpAtANarrowOne() {
        Proposition stated = exactlyOneOf("declaredFirst", FEW + 1);

        assertInstanceOf(CountsWrittenOut.Written.class,
                Allowances.DECLARED.over(() -> CountsWrittenOut.of(stated)));
        assertInstanceOf(CountsWrittenOut.PastAFigure.class,
                NARROW.over(() -> CountsWrittenOut.of(stated)));
    }

    @Test
    void whatWasGivenUpAtANarrowFigureIsWrittenOutAtTheDeclaredOne() {
        Proposition stated = exactlyOneOf("narrowFirst", FEW + 1);

        assertInstanceOf(CountsWrittenOut.PastAFigure.class,
                NARROW.over(() -> CountsWrittenOut.of(stated)));
        assertInstanceOf(CountsWrittenOut.Written.class,
                Allowances.DECLARED.over(() -> CountsWrittenOut.of(stated)));
    }

    @Test
    void theStopNamesTheFigureTheCountWasHeldTo() {
        Proposition stated = exactlyOneOf("named", FEW + 1);

        CountsWrittenOut.Handed handed = NARROW.over(() -> CountsWrittenOut.of(stated));

        assertEquals(CompositionBudget.READINGS_OF_ONE_CONDITION.reachedAShareOf(FEW),
                assertInstanceOf(CountsWrittenOut.PastAFigure.class, handed).stoppedAt());
    }
}
