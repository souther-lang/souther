package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A row holding the condition a line's cases were said as, where which of them the line decides in
 * was more than was taken apart, is not told to be where the line decides: it may be in a case the
 * line turns nothing in, standing at the line's point on the one side that case's rows are on. One
 * failing the condition is in none of the cases, taken apart or not.
 */
class ARowInCasesNobodyTookApartIsNotToldToBeWhereTheLineDecidesTest {

    private static final TermPath STAGE = TermPath.of("s");

    private static final TypeSymbol HOT = TypeSymbols.declared(new TypeKey("probe", "Hot"));

    private static final CasesLeft ONLY_HOT =
            CasesLeft.ofEach(List.of(Refinement.of(new Case.SumCase(HOT, true))));

    private static final Proposition HOT_HOLDS =
            new Proposition.InCases(new DecisionSubject.AnInput(STAGE), ONLY_HOT, true);

    private static final ObservedValue A_VALUE = new ObservedValue.Unit(HOT);

    /** A row whose value at the position is the case, as the walk into it reaches it. */
    private static final Map<TermPath, ObservationAtPoint> IN_THE_CASE = Map.of(
            STAGE, new ObservationAtPoint.Value(A_VALUE),
            STAGE.refine(ONLY_HOT), new ObservationAtPoint.Value(A_VALUE));

    @Test
    void aRowHoldingTheConditionIsWhereTheLineDecidesOnlyWhereTheCasesWereTakenApart() {
        assertEquals(WhereAPartDecides.AtARow.DECIDES, at(HOT_HOLDS, true, IN_THE_CASE),
                "in a case the line was shown to decide in");
        assertEquals(new WhereAPartDecides.AtARow.CouldNotTell(
                        Set.of(ReadingGap.CASES_NOT_TAKEN_APART)),
                at(HOT_HOLDS, false, IN_THE_CASE),
                "in the condition cases nobody took apart were said as");
    }

    @Test
    void aRowFailingTheConditionIsInNoneOfTheCasesEitherWay() {
        for (boolean takenApart : List.of(true, false)) {
            assertEquals(WhereAPartDecides.AtARow.DECIDES_NOTHING,
                    at(HOT_HOLDS.denied(), takenApart, IN_THE_CASE),
                    () -> "taken apart: " + takenApart);
        }
    }

    private static WhereAPartDecides.AtARow at(Proposition decides, boolean takenApart,
                                               Map<TermPath, ObservationAtPoint> walked) {
        return new WhereAPartDecides.AskedOfRows(AStatementAtARow.of(decides, "f", null),
                Optional.empty(), takenApart).at(new AnObservationOfAForm() {

                    @Override
                    public WalkResult<ObservationAtPoint> at(TermPath path) {
                        ObservationAtPoint there = walked.get(path);
                        return there == null ? WalkResult.couldNotWalk()
                                : WalkResult.reached(there);
                    }

                    @Override
                    public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
                        throw new AssertionError("a case of one position is not read over a run");
                    }
                });
    }
}
