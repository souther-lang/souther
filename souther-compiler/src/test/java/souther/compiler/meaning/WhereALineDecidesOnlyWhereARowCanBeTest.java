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

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a line decides is said over the ways a row can be: a value of the input is one case, so a
 * way where it is two at once, or where none of the cases held is the one it is, is no way at all.
 *
 * <p>{@code month.value <= minimum(term)} is {@code OneYear} and the month not above 12, or
 * {@code TwoYear} and the month not above 24. Read with a way where {@code term} is both, the line
 * at 12 came out deciding only where the month is not above 24 as well, so a one-year row with a
 * month of 30 was no row at that line.
 */
class WhereALineDecidesOnlyWhereARowCanBeTest {

    private static final TermPath TERM = TermPath.of("term");
    private static final TermPath MONTH = TermPath.of("month");

    @Test
    void aLineOfOneCaseDecidesInThatCaseAlone() {
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(inCases("OneYear"), above(12).denied())),
                Proposition.all(List.of(inCases("TwoYear"), above(24).denied()))));
        assertEquals(List.of(inCases("OneYear")), casesOf(stated, above(12)));
        assertEquals(List.of(inCases("TwoYear")), casesOf(stated, above(24)));
    }

    /**
     * Three sets of cases any two of which share one, and all three none: the value is in all of
     * them nowhere, so a line that decides only there decides nowhere.
     */
    @Test
    void aWayNoOneCaseIsInIsNoWay() {
        Proposition stated = Proposition.all(List.of(inCases("A", "B"), inCases("B", "C"),
                inCases("A", "C"), above(12)));
        assertEquals(List.of(), casesOf(stated, above(12)));
    }

    /**
     * Read in each case of a value past the parts a table holds, a case the statement asks only
     * denied is one of the cases it is read in: where the term is the last one, the last arm says
     * nothing, and the line at ninety decides nowhere.
     */
    @Test
    void aCaseAskedOnlyDeniedIsReadAsOneOfTheCases() {
        List<Proposition> arms = new ArrayList<>();
        for (int i = 0; i < 6; i++) {
            arms.add(Proposition.all(List.of(inCases("T" + i), above(12 + 6 * i).denied())));
        }
        arms.add(Proposition.all(List.of(inCases("T6").denied(), above(90).denied())));
        List<Proposition> cases = casesOf(Proposition.any(arms), above(90));
        assertEquals(7, cases.size(), cases::toString);
        assertTrue(cases.stream().noneMatch(each -> each instanceof Proposition.All all
                        && all.parts().contains(inCases("T6"))),
                () -> "the last term is no case the line decides in: " + cases);
    }

    /** Where {@code line} decides in {@code stated}. */
    private static List<Proposition> casesOf(Proposition stated, Proposition.Compared line) {
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

    /** The term being one of {@code leaves}. */
    private static Proposition inCases(String... leaves) {
        List<Refinement> atoms = new ArrayList<>();
        for (String leaf : leaves) {
            TypeSymbol symbol = TypeSymbols.declared(new TypeKey("probe", leaf));
            atoms.add(Refinement.of(new Case.SumCase(symbol, true)));
        }
        return new Proposition.InCases(new DecisionSubject.AnInput(TERM), CasesLeft.ofEach(atoms),
                true);
    }
}
