package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.partition.ConditionOccurrence;
import souther.compiler.partition.ConditionReportAnchor;
import souther.compiler.partition.OnTheWay;
import souther.compiler.partition.TakenConstraint;
import souther.compiler.partition.WayToTheBorder;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.ResolvedCase;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A step that moves an enumeration's value onto a case the way left out does not arrive.
 *
 * <p>The number at such a position is the case's place on its declaration's order, so a step moves
 * it from one case to another. A fork on the way that left the value {@code Low} or {@code Mid}
 * left it away from {@code High}'s place, and a step landing there is a row past a fork it does not
 * take — while one landing on the other case it left is a row that still arrives.
 */
class AStepOntoACaseTheWayLeftOutDoesNotArriveTest {

    private static final ConditionOccurrence MET = new ConditionOccurrence("b", 0);

    private static final TermPath LEVEL = TermPath.of("r").then("level");

    private static final NumericTerm.ValueOf THE_LEVEL = new NumericTerm.ValueOf(LEVEL);

    private static final Place LOW = Count.of(0);
    private static final Place MID = Count.of(1);
    private static final Place HIGH = Count.of(2);

    /** The way past an arm leaving the level `Low` or `Mid`, which leaves out `High`'s place. */
    private static WayToTheBorder lowish() {
        CasesLeft lowish = CasesLeft.of(ResolvedCase.of(CaseSelector.direct(leaf("Lowish")),
                List.of(leaf("Low"), leaf("Mid"))));
        return new WayToTheBorder(List.of(new OnTheWay.Narrowed(
                new ConditionReportAnchor.WhereTheReadingMetIt("m", MET), LEVEL.refine(lowish),
                List.of(new TakenConstraint.AwayFrom(THE_LEVEL, HIGH)))));
    }

    @Test
    void aStepOntoACaseLeftOutDoesNotArrive() {
        AnotherLineTheRowsAllow.Reaches reaches =
                new AnotherLineTheRowsAllow.Reaches(lowish(), Set.of(THE_LEVEL));
        assertFalse(reaches.stillArrives(Map.of(THE_LEVEL, MID), Map.of(THE_LEVEL, HIGH)),
                "a step onto High is past a fork that left the value Low or Mid");
    }

    @Test
    void aStepOntoACaseLeftInStillArrives() {
        AnotherLineTheRowsAllow.Reaches reaches =
                new AnotherLineTheRowsAllow.Reaches(lowish(), Set.of(THE_LEVEL));
        assertTrue(reaches.stillArrives(Map.of(THE_LEVEL, MID), Map.of(THE_LEVEL, LOW)),
                "a step onto Low is still a row the fork leaves");
    }

    private static TypeSymbol leaf(String name) {
        return TypeSymbols.declared(new TypeKey("m", name));
    }
}
