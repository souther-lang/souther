package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether two numbers are apart is asked of every place each is read off, and not of the place a
 * report files it under.
 *
 * <p>How many times a value occurs in a run is filed under the run and read off the run and the
 * value, so it moves with a number read off the value alone. A remainder of a form that has the
 * value, and that count beside it, is a remainder beside a number it is not apart from.
 */
class ANumberReadOffSeveralPlacesIsNotApartFromWhatSharesOneOfThemTest {

    private static final TermPath RUN = TermPath.of("xs").element().element();

    private static final TermPath KEY = TermPath.of("k");

    private static final TermPath OTHER = TermPath.of("o");

    private static final NumericTerm THE_KEY = new NumericTerm.ValueOf(KEY);

    private static final NumericTerm THE_OTHER = new NumericTerm.ValueOf(OTHER);

    /** How many times {@code key} occurs in the run. */
    private static NumericTerm occurrencesOf(TermPath key) {
        return NumericTerm.OccurrencesOfAKey.of(new RunSource.FlattenedOccurrences(RUN), key);
    }

    @Test
    void aCountIsNotApartFromTheValueItCounts() {
        assertTrue(occurrencesOf(KEY).sharesAPlaceWith(THE_KEY));
        assertTrue(THE_KEY.sharesAPlaceWith(occurrencesOf(KEY)));
        assertFalse(occurrencesOf(KEY).sharesAPlaceWith(THE_OTHER));
    }

    /** The count and the value it counts are filed under places that do not overlap, which is why
     *  the place a report files a number under cannot tell. */
    @Test
    void theyAreFiledUnderPlacesThatDoNotOverlap() {
        TermPath filedUnder = occurrencesOf(KEY).subjectPath();
        assertFalse(filedUnder.isAtOrUnder(KEY) || KEY.isAtOrUnder(filedUnder));
    }

    /** {@code Int.floorMod(k, 11) - beside}, the remainder first as a relation faces. */
    private static Relation.Affine remainderOfTheKeyBeside(NumericTerm beside) {
        Quantity.RemainderOfADividend remainder = new Quantity.RemainderOfADividend(
                ValueName.Stdlib.operation("Int", "floorMod"),
                new LinearForm<>(ExactRatio.ZERO, Map.of(THE_KEY, ExactRatio.ONE)),
                BigInteger.valueOf(11));
        Map<Quantity, ExactRatio> both = new LinkedHashMap<>();
        both.put(remainder, ExactRatio.ONE);
        both.put(new DecisionAtom.OfTheInput(beside), ExactRatio.ONE.negated());
        return new Relation.Affine(new LinearForm<>(ExactRatio.ZERO, both), Rel.EQ);
    }

    @Test
    void aRemainderIsNotReadBesideANumberItSharesAPlaceWith() {
        assertNull(AStatementAtARow.remainderOfADividendIn(
                remainderOfTheKeyBeside(occurrencesOf(KEY))));
        assertNotNull(AStatementAtARow.remainderOfADividendIn(
                remainderOfTheKeyBeside(occurrencesOf(OTHER))));
        assertNotNull(AStatementAtARow.remainderOfADividendIn(
                remainderOfTheKeyBeside(THE_OTHER)));
    }

    @Test
    void aSearchOfTheTwoIsNotMadeOfNumbersThatShareAPlace() {
        assertThrows(IllegalArgumentException.class, () -> searchOf(occurrencesOf(KEY)));
        assertInstanceOf(Standing.OfARemainderAndAForm.class, searchOf(occurrencesOf(OTHER)));
    }

    private static Standing searchOf(NumericTerm beside) {
        return new Standing.OfARemainderAndAForm(
                new LinearForm<>(ExactRatio.ZERO, Map.of(THE_KEY, ExactRatio.ONE)),
                Map.of(THE_KEY, Carrier.WHOLE), BigInteger.valueOf(11),
                Standing.OfARemainderAndAForm.every(BigInteger.valueOf(11)),
                new LinearForm<>(ExactRatio.ZERO, Map.of(beside, ExactRatio.ONE)),
                Map.of(beside, Carrier.WHOLE), LevelSpace.steppingBy(ExactRatio.ONE),
                new Criterion.AtTheLevel(Level.OfTheQuantity.of(0)));
    }

    /** What is read off more than one place leaves nothing shown of the places a relation leaves
     *  undivided, since the sides name only the place each is filed under. */
    @Test
    void nothingIsShownUndividedOfANumberReadOffSeveralPlaces() {
        UndividedByARelation beside = UndividedByARelation.ofARemainderOfAForm(
                new LinearForm<>(ExactRatio.ZERO, Map.of(THE_KEY, ExactRatio.ONE)),
                BigInteger.ZERO, BigInteger.valueOf(11),
                new LinearForm<>(ExactRatio.ZERO, Map.of(occurrencesOf(KEY), ExactRatio.ONE)),
                ExactRatio.ZERO, Rel.EQ);
        assertSame(UndividedByARelation.SHOWING_NOTHING, beside);

        UndividedByARelation apart = UndividedByARelation.ofARemainderOfAForm(
                new LinearForm<>(ExactRatio.ZERO, Map.of(THE_KEY, ExactRatio.ONE)),
                BigInteger.ZERO, BigInteger.valueOf(11),
                new LinearForm<>(ExactRatio.ZERO, Map.of(THE_OTHER, ExactRatio.ONE)),
                ExactRatio.ZERO, Rel.EQ);
        assertNotSame(UndividedByARelation.SHOWING_NOTHING, apart);
        assertEquals(2, apart.sides().size());
    }
}
