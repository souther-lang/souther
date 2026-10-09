package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A relation of numbers read to the end is taken into what a path knows, or meets an edge of what
 * a path can keep it in — and never comes out as a statement left unread.
 *
 * <p>Two numbers of the statement may be one fact on a path, and then their weights add. Where the
 * sum has no exact representation, the statement is no less read: what stops is the number a path
 * would keep the fact in, which is an edge of what a path knows and is said as one.
 */
class AStatementReadToTheEndIsHeldOrMeetsWhatAPathCanKeepTest {

    private static final Term.Interner NAMES = new Term.Interner();

    private static final FactSubject X = FactSubject.of(NAMES.written("x"));

    private static final Quantity ONE_SPELLING =
            new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("x")));

    private static final Quantity ANOTHER_SPELLING =
            new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("y")));

    /** A tenth to the power of a scale near the end of the range, which added to one is no number
     *  the exact arithmetic holds. */
    private static final ExactRatio FINE = ExactRatio.of(new BigDecimal(BigInteger.ONE, 1 << 30));

    @Test
    void twoNumbersOfOneFactAddTheirWeights() {
        MeaningAssumptions.FormAt.Named named = assertInstanceOf(
                MeaningAssumptions.FormAt.Named.class,
                MeaningAssumptions.formOver(form(ExactRatio.ONE, ExactRatio.of(2)),
                        each -> new MeaningAssumptions.AtomAt.Named(X)));
        assertEquals(Map.of(X, ExactRatio.of(3)), named.form().coefs());
    }

    @Test
    void weightsAddingToANumberNotHeldMeetAnEdgeAndAreNotUnread() {
        MeaningAssumptions.FormAt.Unnamed unnamed = assertInstanceOf(
                MeaningAssumptions.FormAt.Unnamed.class,
                MeaningAssumptions.formOver(form(ExactRatio.ONE, FINE),
                        each -> new MeaningAssumptions.AtomAt.Named(X)));
        assertEquals(Set.of(WhyNotTaken.DomainLimit.A_NUMBER_THE_PATH_CANNOT_HOLD),
                unnamed.edges());
    }

    @Test
    void everyEdgeTheNumbersMeetIsSaidOnce() {
        MeaningAssumptions.FormAt.Unnamed unnamed = assertInstanceOf(
                MeaningAssumptions.FormAt.Unnamed.class,
                MeaningAssumptions.formOver(form(ExactRatio.ONE, ExactRatio.of(2)),
                        each -> new MeaningAssumptions.AtomAt.AtTheEdge(
                                each.equals(ONE_SPELLING)
                                        ? WhyNotTaken.DomainLimit.A_PLACE_THE_PATH_DOES_NOT_READ
                                        : WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_COUNT_OF_ELEMENTS)));
        assertEquals(Set.of(WhyNotTaken.DomainLimit.A_PLACE_THE_PATH_DOES_NOT_READ,
                WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_COUNT_OF_ELEMENTS), unnamed.edges());
    }

    private static LinearForm<Quantity> form(ExactRatio one, ExactRatio another) {
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(ONE_SPELLING, one);
        coefs.put(ANOTHER_SPELLING, another);
        return new LinearForm<>(ExactRatio.ZERO, coefs);
    }
}
