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
 * Exactly one of the numbers 2 and 3 is the field of some element of a list that is one case of a
 * sum: the line at the field of the case, read for the number 2, decides where the element is that
 * case and where the count of the statements about the other numbers comes to what the count
 * admits with the line holding and with it failing.
 *
 * <p>That count is the statement for 3, about an element of its own: it is kept whole, with its
 * quantifier, and nothing of it is said of the element the line is at.
 */
class WhereALineAtAFieldOfACaseKeepsTheCountBesideItWholeTest {

    private static final TermPath CLUES = TermPath.of("clues");
    private static final DecisionSubject CONTAINER = new DecisionSubject.AnInput(CLUES);
    private static final DecisionSubject ELEMENT = new DecisionSubject.AnInput(CLUES.element());

    private static final CasesLeft IS = caseOf("Is");

    private static CasesLeft caseOf(String leaf) {
        TypeSymbol symbol = TypeSymbols.declared(new TypeKey("probe", leaf));
        return CasesLeft.ofEach(List.of(Refinement.of(new Case.SumCase(symbol, true))));
    }

    /** {@code clues[*]@Is.n == number}, held. */
    private static Proposition.Compared fieldIs(long number) {
        TermPath at = CLUES.element().refine(IS).then("n");
        return new Proposition.Compared(new Relation.Affine(new LinearForm<>(
                ExactRatio.of(-number), Map.of(new DecisionAtom.OfTheInput(
                        new NumericTerm.ValueOf(at)), ExactRatio.ONE)), Rel.EQ), true);
    }

    /** Some element is the case {@code Is} with its field at {@code number}. */
    private static Proposition.Some someIsAt(long number) {
        return new Proposition.Some(CONTAINER, Proposition.all(List.of(fieldIs(number),
                new Proposition.InCases(ELEMENT, IS, true))), true);
    }

    private static Proposition count(List<Proposition> statements, int admitted) {
        return Proposition.SoManyHold.counting(statements,
                statements.stream().map(_ -> 1).toList(), List.of(admitted));
    }

    @Test
    void theLineIsInTheCaseWithTheCountOfTheOtherNumbersKeptWhole() {
        Proposition.Some two = someIsAt(2);
        Proposition.Some three = someIsAt(3);
        Proposition stated = count(List.of(two, three), 1);

        List<WhereEachLineDecides.Decides> lines = WhereEachLineDecides.in(stated, term -> false);
        WhereEachLineDecides.Decides forTwo = lines.stream()
                .filter(each -> each.line().spelledOut().equals(fieldIs(2).spelledOut()))
                .findFirst().orElseThrow();

        Proposition isIs = new Proposition.InCases(ELEMENT, IS, true);
        assertEquals(List.of(Proposition.all(List.of(isIs, count(List.of(three), 0))),
                        Proposition.all(List.of(isIs, count(List.of(three), 1)))),
                forTwo.cases().stream().map(DecidingCase::condition).toList(),
                () -> "in the case Is, with 3 not held where 2 is, and held where it is not: "
                        + forTwo);
    }
}
