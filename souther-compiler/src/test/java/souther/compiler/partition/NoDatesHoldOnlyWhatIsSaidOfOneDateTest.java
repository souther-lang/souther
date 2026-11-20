package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A way says no dates hold what it states of a set of places only where the statements are of one
 * date each: the thirtieth of February of a date outside every container is no date, and of a
 * date inside one each statement may be of another element.
 */
class NoDatesHoldOnlyWhatIsSaidOfOneDateTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());

    private static NumericTerm part(String operation, TermPath at) {
        NumericTerm made = NumericTerm.TakenOf.asItStands(
                ValueName.Stdlib.operation("Date", operation), at, Type.Prim.DATE,
                ScopedDeclarations.wrapsOf(SYMBOLS), SYMBOLS);
        assertNotNull(made, operation);
        return made;
    }

    private static UndividedByARelation.OnAWay is(NumericTerm term, long value, TermPath at) {
        return new UndividedByARelation.OnAWay(Set.of(at), false, new TakenConstraint.Affine(
                new LinearForm<>(ExactRatio.of(-value), Map.of(term, ExactRatio.ONE)), Rel.EQ),
                null);
    }

    private static boolean noDatesHoldTheThirtiethOfFebruaryAt(TermPath at) {
        return DatesHeldApartAlongAWay.of(
                List.of(is(part("month", at), 2, at), is(part("day", at), 30, at)), List.of(),
                List.of(), _ -> DateTranslation.none()).someSetNoDatesHold();
    }

    @Test
    void theThirtiethOfFebruaryOfADateIsHeldByNone() {
        assertTrue(noDatesHoldTheThirtiethOfFebruaryAt(TermPath.of("d")));
    }

    @Test
    void theMonthAndTheDayOfADateInAContainerAreNotSaidOfOneDate() {
        assertFalse(noDatesHoldTheThirtiethOfFebruaryAt(TermPath.of("ds").element()));
    }
}
