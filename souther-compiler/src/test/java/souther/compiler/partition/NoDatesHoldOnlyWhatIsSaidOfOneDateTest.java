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

    /** {@code month} and {@code day} of the date at {@code at}. */
    private static List<UndividedByARelation.OnAWay> theDay(long month, long day, TermPath at) {
        return List.of(is(part("month", at), month, at), is(part("day", at), day, at));
    }

    private static boolean someSetNoDatesHold(List<List<UndividedByARelation.OnAWay>> sets) {
        return DatesHeldApartAlongAWay.of(sets.stream().flatMap(List::stream).toList(),
                List.of(), List.of(), _ -> DateTranslation.none()).someSetNoDatesHold();
    }

    /**
     * A way stating one date some dates hold, the thirtieth of February of a date in a container,
     * which the calendar is not asked of, and of a date outside every container, which no date
     * is: no dates hold a set of it, whichever comes first; without the last, none is said,
     * though the calendar shows no dates for the second.
     */
    @Test
    void aSetNoDatesHoldIsSaidBesideSetsHeldAndSetsNotShown() {
        List<UndividedByARelation.OnAWay> held = theDay(2, 29, TermPath.of("d"));
        List<UndividedByARelation.OnAWay> notShown = theDay(2, 30, TermPath.of("ds").element());
        List<UndividedByARelation.OnAWay> none = theDay(2, 30, TermPath.of("f"));

        assertTrue(someSetNoDatesHold(List.of(held, notShown, none)));
        assertTrue(someSetNoDatesHold(List.of(none, held, notShown)));
        assertFalse(someSetNoDatesHold(List.of(held, notShown)));
    }
}
