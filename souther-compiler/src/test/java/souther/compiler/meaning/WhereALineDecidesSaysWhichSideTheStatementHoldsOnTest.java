package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Each case of where a line decides says which side of the line the statement holds on there, and
 * a case is said over the ways the statement's parts can come out together.
 *
 * <p>A line is a relation held, and the statement may hold where it fails. {@code month.value <=
 * minimum(term)} is {@code OneYear} and the month not above 12, or {@code TwoYear} and the month
 * not above 24: its lines are {@code month > 12} and {@code month > 24}, and the statement holds
 * below each of them. A reader taking the line's side for the statement's names every point of
 * such a line the other way round from the same comparison against a fixed number.
 *
 * <p>And {@code term} is never both cases. Read as two parts free of each other, the table has a
 * way where it is, and the line at 12 comes out deciding only where the month is not above 24 as
 * well — so a one-year row with a month of 30 was no row at that line.
 */
class WhereALineDecidesSaysWhichSideTheStatementHoldsOnTest {

    private static final TypeSymbol ONE_YEAR = TypeSymbols.declared(new TypeKey("probe", "OneYear"));
    private static final TypeSymbol TWO_YEAR = TypeSymbols.declared(new TypeKey("probe", "TwoYear"));
    private static final TermPath TERM = TermPath.of("term");
    private static final TermPath MONTH = TermPath.of("month");
    private static final TermPath FLAG = TermPath.of("flag");

    /** The comparison of a month against the minimum of the term, as the statement it reads as. */
    private static final Proposition WITHIN_THE_MINIMUM = Proposition.any(List.of(
            Proposition.all(List.of(inCase(ONE_YEAR), above(12).denied())),
            Proposition.all(List.of(inCase(TWO_YEAR), above(24).denied()))));

    @Test
    void aLineTheStatementStatesTheDenialOfHoldsWhereItFails() {
        assertEquals(List.of(new WhereEachLineDecides.Case(inCase(ONE_YEAR), false)),
                casesOf(WITHIN_THE_MINIMUM, above(12)));
        assertEquals(List.of(new WhereEachLineDecides.Case(inCase(TWO_YEAR), false)),
                casesOf(WITHIN_THE_MINIMUM, above(24)));
    }

    @Test
    void aLineTheStatementStatesHoldsWhereItHolds() {
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(inCase(ONE_YEAR), above(12))),
                Proposition.all(List.of(inCase(TWO_YEAR), above(24)))));
        assertEquals(List.of(new WhereEachLineDecides.Case(inCase(ONE_YEAR), true)),
                casesOf(stated, above(12)));
    }

    /**
     * The line held where a truth holds and failing where it does not is the statement turning
     * one way round in one case and the other in the other, and the two are two cases.
     */
    @Test
    void aStatementTurningEachWayIsTwoCasesOneOnEachSide() {
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(above(12), truth())),
                Proposition.all(List.of(above(12).denied(), truth().denied()))));
        assertEquals(List.of(new WhereEachLineDecides.Case(truth(), true),
                        new WhereEachLineDecides.Case(truth().denied(), false)),
                casesOf(stated, above(12)));
    }

    /** Where {@code line} decides in {@code stated}. */
    private static List<WhereEachLineDecides.Case> casesOf(Proposition stated,
                                                           Proposition.Compared line) {
        for (WhereEachLineDecides.Decides each : WhereEachLineDecides.in(stated)) {
            if (each.line().key().equals(line.key())) {
                return each.cases();
            }
        }
        throw new AssertionError(line + " is a line of " + stated);
    }

    /** The month above {@code value}, held. */
    private static Proposition.Compared above(long value) {
        return new Proposition.Compared(new Relation.Affine(new LinearForm<>(
                ExactRatio.of(-value), Map.of(new DecisionAtom.OfTheInput(
                        new NumericTerm.ValueOf(MONTH)), ExactRatio.ONE)), Rel.GT), true);
    }

    private static Proposition inCase(TypeSymbol leaf) {
        return new Proposition.InCases(new DecisionSubject.AnInput(TERM),
                CasesLeft.of(Refinement.of(new Case.SumCase(leaf, true))), true);
    }

    private static Proposition truth() {
        return new Proposition.Truth(new DecisionSubject.AnInput(FLAG), true);
    }
}
