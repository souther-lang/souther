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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A product of two numbers of the input is about the places both factors are read off, whichever
 * of them it is filed under.
 *
 * <p>A product is filed under the factor its order puts first, so which one that is follows from
 * the names. Each question here is asked with the other factor named before the one that matters
 * and after it, and is answered as it is for that factor alone: a line on a field of one case of
 * a value decides in that case, and a line on an element of a list may turn on the element.
 */
class AProductIsAboutEachPlaceItsFactorsAreReadOffTest {

    private static final TermPath TERM = TermPath.of("term");

    private static final TermPath XS = TermPath.of("xs");

    /** Named before every place a factor is read off here, and after. */
    private static final List<String> OTHER_FACTORS = List.of("a", "zz");

    @Test
    void aLineOnAProductDecidesInTheCaseEitherFactorIsNarrowedTo() {
        NumericTerm underOneYear = new NumericTerm.ValueOf(TERM.refine(cases("OneYear")).then("y"));
        Map<String, List<Proposition>> expected = new LinkedHashMap<>();
        Map<String, List<Proposition>> actual = new LinkedHashMap<>();
        List<Proposition> alone = casesOf(underOneYear);
        for (String other : OTHER_FACTORS) {
            expected.put(other, alone);
            actual.put(other, casesOf(product(other, underOneYear)));
        }
        assertEquals(expected, actual);
        assertEquals(List.of(Proposition.all(List.of(inCases("OneYear"),
                inCases("OneYear", "TwoYear")))), alone, "the line decides in the one case");
    }

    @Test
    void aLineOnAProductMayTurnOnAnElementEitherFactorIsReadOff() {
        NumericTerm ofTheElement = new NumericTerm.ValueOf(XS.element().then("p"));
        DecisionSubject list = new DecisionSubject.AnInput(XS);
        Map<String, Boolean> expected = new LinkedHashMap<>();
        Map<String, Boolean> actual = new LinkedHashMap<>();
        expected.put("alone", true);
        actual.put("alone", above(ofTheElement).mayTurnOnAnElementOf(list));
        for (String other : OTHER_FACTORS) {
            expected.put(other, true);
            actual.put(other, above(product(other, ofTheElement)).mayTurnOnAnElementOf(list));
        }
        expected.put("apart", false);
        actual.put("apart", above(product("a", new NumericTerm.ValueOf(TermPath.of("b"))))
                .mayTurnOnAnElementOf(list));
        assertEquals(expected, actual);
    }

    /** {@code factor} times the number at {@code other}. */
    private static NumericTerm product(String other, NumericTerm factor) {
        return NumericTerm.ProductOf.of(LinearForm.atom(new NumericTerm.ValueOf(TermPath.of(other))),
                LinearForm.atom(factor));
    }

    /** Where the line {@code number > 12} decides, written in each of two cases of the term. */
    private static List<Proposition> casesOf(NumericTerm number) {
        Proposition.Compared line = above(number);
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(inCases("TwoYear"), line)),
                Proposition.all(List.of(inCases("OneYear"), line))));
        for (WhereEachLineDecides.Decides each : WhereEachLineDecides.in(stated, term -> false)) {
            if (each.line().spelledOut().equals(line.spelledOut())) {
                return each.cases().stream().map(DecidingCase::condition).toList();
            }
        }
        throw new AssertionError(line + " is a line of " + stated);
    }

    private static Proposition.Compared above(NumericTerm number) {
        return new Proposition.Compared(new Relation.Affine(new LinearForm<>(ExactRatio.of(-12),
                Map.of(new DecisionAtom.OfTheInput(number), ExactRatio.ONE)), Rel.GT), true);
    }

    private static Proposition inCases(String... leaves) {
        return new Proposition.InCases(new DecisionSubject.AnInput(TERM), cases(leaves), true);
    }

    private static CasesLeft cases(String... leaves) {
        List<Refinement> atoms = new ArrayList<>();
        for (String leaf : leaves) {
            TypeSymbol symbol = TypeSymbols.declared(new TypeKey("probe", leaf));
            atoms.add(Refinement.of(new Case.SumCase(symbol, true)));
        }
        return CasesLeft.ofEach(atoms);
    }
}
