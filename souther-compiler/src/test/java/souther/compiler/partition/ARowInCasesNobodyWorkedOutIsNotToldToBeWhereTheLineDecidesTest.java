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

import java.util.EnumSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A row holding the condition where cases nobody worked out are is not told to be where the line
 * decides: it may be in a case the line turns nothing in, standing at the line's point on the one
 * side that case's rows are on, and what it is not told says every figure that stopped them. One
 * failing the condition is in none of the cases, worked out or not.
 */
class ARowInCasesNobodyWorkedOutIsNotToldToBeWhereTheLineDecidesTest {

    private static final CasesWorkedOut STOPPED = CasesWorkedOut.Stopped.at(EnumSet.of(
            CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO,
            CompositionBudget.CASES_A_LINE_IS_ASKED_IN));

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
    void aRowHoldingTheConditionIsWhereTheLineDecidesOnlyWhereTheCasesWereShownToBe() {
        assertEquals(WhereAPartDecides.AtARow.DECIDES,
                at(HOT_HOLDS, CasesWorkedOut.SHOWN, IN_THE_CASE),
                "in a case the line was shown to decide in");
        assertEquals(new WhereAPartDecides.AtARow.CouldNotTell(Set.of(
                        new ReadingGap.CasesNotWorkedOut(List.of(
                                CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.figure(),
                                CompositionBudget.CASES_A_LINE_IS_ASKED_IN.figure())))),
                at(HOT_HOLDS, STOPPED, IN_THE_CASE),
                "where cases nobody worked out are, naming what stopped them");
    }

    @Test
    void aRowFailingTheConditionIsInNoneOfTheCasesEitherWay() {
        for (CasesWorkedOut workedOut : List.of(CasesWorkedOut.SHOWN, STOPPED)) {
            assertEquals(WhereAPartDecides.AtARow.DECIDES_NOTHING,
                    at(HOT_HOLDS.denied(), workedOut, IN_THE_CASE),
                    () -> "worked out: " + workedOut);
        }
    }

    private static WhereAPartDecides.AtARow at(Proposition decides, CasesWorkedOut workedOut,
                                               Map<TermPath, ObservationAtPoint> walked) {
        return new WhereAPartDecides.AskedOfRows(AStatementAtARow.of(decides, "f", null),
                Optional.empty(), workedOut).at(new AnObservationOfAForm() {

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
