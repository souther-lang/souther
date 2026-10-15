package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A relation inside a quantifier is a line where the element the quantifier chose crosses it, and
 * where it decides is said of that element and of every other quantifier whole.
 *
 * <p>Two quantifiers over one container choose an element each, and the two may be different
 * elements. Where a line inside one of them decides is where the other holds of an element of its
 * own; said of the line's element, it would ask one element to be what two are.
 */
class WhereALineInsideAQuantifierDecidesTest {

    private static final TermPath XS = TermPath.of("xs");
    private static final DecisionSubject CONTAINER = new DecisionSubject.AnInput(XS);
    private static final TermPath N = XS.element().then("n");
    private static final TermPath A = TermPath.of("a");

    /**
     * Some element above nought and some element below it: the line at nought on the first
     * decides where some element is below nought, which is the other quantifier and not the
     * element at the line.
     */
    @Test
    void besideAnotherQuantifierOverTheSameContainerTheOtherStaysAQuantifier() {
        Proposition above = new Proposition.Some(CONTAINER, compared(N, 0, Rel.GT), true);
        Proposition below = new Proposition.Some(CONTAINER, compared(N, 0, Rel.GE).denied(),
                true);
        List<Proposition> cases = casesOf(Proposition.all(List.of(above, below)),
                compared(N, 0, Rel.GT));
        assertFalse(cases.isEmpty(), "the line decides somewhere");
        for (Proposition each : cases) {
            assertTrue(unquantified(each).stream().noneMatch(atom -> atom.equals(
                            compared(N, 0, Rel.GE).key())),
                    () -> "the element below nought is the other quantifier's: " + each);
        }
    }

    /**
     * A relation about the row inside a quantifier is the same relation wherever the quantifier
     * looks: it decides where some element meets the rest, and asks nothing of one element.
     */
    @Test
    void aRelationOfTheRowInsideAQuantifierDecidesWhereSomeElementMeetsTheRest() {
        Proposition some = new Proposition.Some(CONTAINER,
                Proposition.all(List.of(compared(N, 0, Rel.GT), compared(A, 5, Rel.GT))), true);
        List<Proposition> cases = casesOf(some, compared(A, 5, Rel.GT));
        assertFalse(cases.isEmpty() || cases.equals(List.of(new Proposition.Always(false))),
                () -> "the line on a decides somewhere: " + cases);
        for (Proposition each : cases) {
            assertTrue(unquantified(each).stream().noneMatch(atom -> atom.contains("xs")),
                    () -> "nothing of an element is asked outside the quantifier: " + each);
        }
    }

    /** The relation {@code at} against {@code value} as {@code rel}, held. */
    private static Proposition.Compared compared(TermPath at, long value, Rel rel) {
        return new Proposition.Compared(new Relation.Affine(new LinearForm<>(
                ExactRatio.of(-value), Map.of(new DecisionAtom.OfTheInput(
                        new NumericTerm.ValueOf(at)), ExactRatio.ONE)), rel), true);
    }

    /** Where {@code line} decides in {@code stated}. */
    private static List<Proposition> casesOf(Proposition stated, Proposition.Compared line) {
        List<WhereEachLineDecides.Decides> lines = WhereEachLineDecides.in(stated);
        for (WhereEachLineDecides.Decides each : lines) {
            if (each.line().key().equals(line.key())) {
                return each.cases();
            }
        }
        throw new AssertionError(line + " is a line of " + stated + ": " + lines);
    }

    /** The spellings of the parts of {@code stated} no quantifier holds, held. */
    private static List<String> unquantified(Proposition stated) {
        List<String> out = new ArrayList<>();
        switch (stated) {
            case Proposition.All all -> all.parts().forEach(part -> out.addAll(unquantified(part)));
            case Proposition.Any any -> any.parts().forEach(part -> out.addAll(unquantified(part)));
            case Proposition.Some _ -> { }
            default -> out.add(stated instanceof Proposition.Compared compared && !compared.holds()
                    ? compared.denied().key() : stated.key());
        }
        return out;
    }
}
